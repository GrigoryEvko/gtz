import Gtz.Wave.KFourDualSaturation

/-!
# Saturating the five prior K4 path duals

`KFourDualSaturation` handles the seven paths added by the row atlas.  The
earlier minor atlas contains five more paths: the band tree `{1,3,4}` and four
pendants.  Each admits the same alternating-sign saturation.  This module
checks all five pullbacks against the chart reading law, converts a full dual
witness at a weak path into a nonzero tight direction, and joins the result to
the seven-path ledger.

The four K4 vertex stars are deliberately absent: their three fundamental
triangles cannot be saturated by one sign choice.  After this module, that
sign-frustrated four-tree family is the only tree type without an exact
Z-to-gap pullback.
-/

namespace Gtz

open Matrix Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-! ## The band path `{1,3,4}` -/

noncomputable def kFourBand134ZMatrix (point : DirectionChartPoint 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  zThreeMatrix
    (directionChartExactFloor point 1 - (point.mass 2 + point.mass 5))
    (-(point.mass 2 + point.mass 5)) (-(point.mass 2))
    (directionChartExactFloor point 3 - (point.mass 0 + point.mass 2 + point.mass 5))
    (-(point.mass 0 + point.mass 2))
    (directionChartExactFloor point 4 - (point.mass 0 + point.mass 2))

def kFourBand134Probe (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-y 1, y 2, -(y 0 + y 1)]

theorem dotProduct_kFourBand134Gap_probe_eq_zMatrix
    (point : DirectionChartPoint 6) (y : Fin 3 → ℝ) :
    kFourBand134Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({1, 3, 4} : Finset (Fin 6)) *ᵥ kFourBand134Probe y)
      = y ⬝ᵥ (kFourBand134ZMatrix point *ᵥ y) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  simp [kFourBand134Probe, kFourBand134ZMatrix, zThreeMatrix,
    kFourDirection, directionChartExactFloor, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Fin.sum_univ_six]
  field_simp [ne_of_gt (point.weight_pos 1), ne_of_gt (point.weight_pos 3),
    ne_of_gt (point.weight_pos 4)]
  ring

theorem kFourBand134Probe_ne_zero_of_ne_zero {y : Fin 3 → ℝ} (hy : y ≠ 0) :
    kFourBand134Probe y ≠ 0 := by
  intro hzero
  apply hy
  have hzero0 := congrFun hzero 0
  have hzero1 := congrFun hzero 1
  have hzero2 := congrFun hzero 2
  simp [kFourBand134Probe] at hzero0 hzero1 hzero2
  funext index
  fin_cases index <;> simp <;> linarith

theorem kFourBand134DualTightData_of_blind_of_weak
    (point : DirectionChartPoint 6) (hblind : ¬ KFourUnsignedBandTreeCellFires point)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      ({1, 3, 4} : Finset (Fin 6))).PosSemidef) :
    KFourPathDualTightData point ({1, 3, 4} : Finset (Fin 6))
      (kFourBand134ZMatrix point) kFourBand134Probe := by
  simpa only [KFourPathDualTightData, kFourBand134ZMatrix] using
    exists_nonnegative_tightDirection_of_zThreeDualWitness_of_gap_pullback
      (kFourBand134DualWitness_of_not_fires point hblind) hweak kFourBand134Probe
      kFourBand134Probe_ne_zero_of_ne_zero
      (dotProduct_kFourBand134Gap_probe_eq_zMatrix point)

/-! ## The pendant path `{0,2,3}` -/

noncomputable def kFourPendant023ZMatrix (point : DirectionChartPoint 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  zThreeMatrix
    (directionChartExactFloor point 0 - (point.mass 1 + point.mass 4 + point.mass 5))
    (-(point.mass 1 + point.mass 5)) (-(point.mass 4 + point.mass 5))
    (directionChartExactFloor point 2 - (point.mass 1 + point.mass 5))
    (-(point.mass 5))
    (directionChartExactFloor point 3 - (point.mass 4 + point.mass 5))

def kFourPendant023Probe (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-y 2, -(y 0 + y 2), -(y 0 + y 1 + y 2)]

theorem dotProduct_kFourPendant023Gap_probe_eq_zMatrix
    (point : DirectionChartPoint 6) (y : Fin 3 → ℝ) :
    kFourPendant023Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({0, 2, 3} : Finset (Fin 6)) *ᵥ kFourPendant023Probe y)
      = y ⬝ᵥ (kFourPendant023ZMatrix point *ᵥ y) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  simp [kFourPendant023Probe, kFourPendant023ZMatrix, zThreeMatrix,
    kFourDirection, directionChartExactFloor, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Fin.sum_univ_six]
  field_simp [ne_of_gt (point.weight_pos 0), ne_of_gt (point.weight_pos 2),
    ne_of_gt (point.weight_pos 3)]
  ring

theorem kFourPendant023Probe_ne_zero_of_ne_zero {y : Fin 3 → ℝ} (hy : y ≠ 0) :
    kFourPendant023Probe y ≠ 0 := by
  intro hzero
  apply hy
  have hzero0 := congrFun hzero 0
  have hzero1 := congrFun hzero 1
  have hzero2 := congrFun hzero 2
  simp [kFourPendant023Probe] at hzero0 hzero1 hzero2
  funext index
  fin_cases index <;> simp <;> linarith

theorem kFourPendant023DualTightData_of_blind_of_weak
    (point : DirectionChartPoint 6) (hblind : ¬ KFourPendantCell023Fires point)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      ({0, 2, 3} : Finset (Fin 6))).PosSemidef) :
    KFourPathDualTightData point ({0, 2, 3} : Finset (Fin 6))
      (kFourPendant023ZMatrix point) kFourPendant023Probe := by
  simpa only [KFourPathDualTightData, kFourPendant023ZMatrix] using
    exists_nonnegative_tightDirection_of_zThreeDualWitness_of_gap_pullback
      (kFourPendant023DualWitness_of_not_fires point hblind) hweak kFourPendant023Probe
      kFourPendant023Probe_ne_zero_of_ne_zero
      (dotProduct_kFourPendant023Gap_probe_eq_zMatrix point)

/-! ## The pendant path `{1,2,3}` -/

noncomputable def kFourPendant123ZMatrix (point : DirectionChartPoint 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  zThreeMatrix
    (directionChartExactFloor point 1 - (point.mass 0 + point.mass 4 + point.mass 5))
    (-(point.mass 0 + point.mass 4)) (-(point.mass 4 + point.mass 5))
    (directionChartExactFloor point 2 - (point.mass 0 + point.mass 4))
    (-(point.mass 4))
    (directionChartExactFloor point 3 - (point.mass 4 + point.mass 5))

def kFourPendant123Probe (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-y 2, -(y 0 + y 1 + y 2), -(y 0 + y 2)]

theorem dotProduct_kFourPendant123Gap_probe_eq_zMatrix
    (point : DirectionChartPoint 6) (y : Fin 3 → ℝ) :
    kFourPendant123Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({1, 2, 3} : Finset (Fin 6)) *ᵥ kFourPendant123Probe y)
      = y ⬝ᵥ (kFourPendant123ZMatrix point *ᵥ y) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  simp [kFourPendant123Probe, kFourPendant123ZMatrix, zThreeMatrix,
    kFourDirection, directionChartExactFloor, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Fin.sum_univ_six]
  field_simp [ne_of_gt (point.weight_pos 1), ne_of_gt (point.weight_pos 2),
    ne_of_gt (point.weight_pos 3)]
  ring

theorem kFourPendant123Probe_ne_zero_of_ne_zero {y : Fin 3 → ℝ} (hy : y ≠ 0) :
    kFourPendant123Probe y ≠ 0 := by
  intro hzero
  apply hy
  have hzero0 := congrFun hzero 0
  have hzero1 := congrFun hzero 1
  have hzero2 := congrFun hzero 2
  simp [kFourPendant123Probe] at hzero0 hzero1 hzero2
  funext index
  fin_cases index <;> simp <;> linarith

theorem kFourPendant123DualTightData_of_blind_of_weak
    (point : DirectionChartPoint 6) (hblind : ¬ KFourPendantCell123Fires point)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      ({1, 2, 3} : Finset (Fin 6))).PosSemidef) :
    KFourPathDualTightData point ({1, 2, 3} : Finset (Fin 6))
      (kFourPendant123ZMatrix point) kFourPendant123Probe := by
  simpa only [KFourPathDualTightData, kFourPendant123ZMatrix] using
    exists_nonnegative_tightDirection_of_zThreeDualWitness_of_gap_pullback
      (kFourPendant123DualWitness_of_not_fires point hblind) hweak kFourPendant123Probe
      kFourPendant123Probe_ne_zero_of_ne_zero
      (dotProduct_kFourPendant123Gap_probe_eq_zMatrix point)

/-! ## The pendant path `{2,3,4}` -/

noncomputable def kFourPendant234ZMatrix (point : DirectionChartPoint 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  zThreeMatrix
    (directionChartExactFloor point 2 - (point.mass 1 + point.mass 5))
    (-(point.mass 1)) (-(point.mass 1 + point.mass 5))
    (directionChartExactFloor point 3 - (point.mass 0 + point.mass 1))
    (-(point.mass 0 + point.mass 1))
    (directionChartExactFloor point 4 - (point.mass 0 + point.mass 1 + point.mass 5))

def kFourPendant234Probe (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![y 1, -y 2, -(y 0 + y 2)]

theorem dotProduct_kFourPendant234Gap_probe_eq_zMatrix
    (point : DirectionChartPoint 6) (y : Fin 3 → ℝ) :
    kFourPendant234Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({2, 3, 4} : Finset (Fin 6)) *ᵥ kFourPendant234Probe y)
      = y ⬝ᵥ (kFourPendant234ZMatrix point *ᵥ y) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  simp [kFourPendant234Probe, kFourPendant234ZMatrix, zThreeMatrix,
    kFourDirection, directionChartExactFloor, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Fin.sum_univ_six]
  field_simp [ne_of_gt (point.weight_pos 2), ne_of_gt (point.weight_pos 3),
    ne_of_gt (point.weight_pos 4)]
  ring

theorem kFourPendant234Probe_ne_zero_of_ne_zero {y : Fin 3 → ℝ} (hy : y ≠ 0) :
    kFourPendant234Probe y ≠ 0 := by
  intro hzero
  apply hy
  have hzero0 := congrFun hzero 0
  have hzero1 := congrFun hzero 1
  have hzero2 := congrFun hzero 2
  simp [kFourPendant234Probe] at hzero0 hzero1 hzero2
  funext index
  fin_cases index <;> simp <;> linarith

theorem kFourPendant234DualTightData_of_blind_of_weak
    (point : DirectionChartPoint 6) (hblind : ¬ KFourPendantCell234Fires point)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      ({2, 3, 4} : Finset (Fin 6))).PosSemidef) :
    KFourPathDualTightData point ({2, 3, 4} : Finset (Fin 6))
      (kFourPendant234ZMatrix point) kFourPendant234Probe := by
  simpa only [KFourPathDualTightData, kFourPendant234ZMatrix] using
    exists_nonnegative_tightDirection_of_zThreeDualWitness_of_gap_pullback
      (kFourPendant234DualWitness_of_not_fires point hblind) hweak kFourPendant234Probe
      kFourPendant234Probe_ne_zero_of_ne_zero
      (dotProduct_kFourPendant234Gap_probe_eq_zMatrix point)

/-! ## The pendant path `{2,3,5}` -/

noncomputable def kFourPendant235ZMatrix (point : DirectionChartPoint 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  zThreeMatrix
    (directionChartExactFloor point 2 - (point.mass 0 + point.mass 4))
    (-(point.mass 0)) (-(point.mass 0 + point.mass 4))
    (directionChartExactFloor point 3 - (point.mass 0 + point.mass 1))
    (-(point.mass 0 + point.mass 1))
    (directionChartExactFloor point 5 - (point.mass 0 + point.mass 1 + point.mass 4))

def kFourPendant235Probe (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![y 1, -(y 0 + y 2), -y 2]

theorem dotProduct_kFourPendant235Gap_probe_eq_zMatrix
    (point : DirectionChartPoint 6) (y : Fin 3 → ℝ) :
    kFourPendant235Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({2, 3, 5} : Finset (Fin 6)) *ᵥ kFourPendant235Probe y)
      = y ⬝ᵥ (kFourPendant235ZMatrix point *ᵥ y) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  simp [kFourPendant235Probe, kFourPendant235ZMatrix, zThreeMatrix,
    kFourDirection, directionChartExactFloor, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Fin.sum_univ_six]
  field_simp [ne_of_gt (point.weight_pos 2), ne_of_gt (point.weight_pos 3),
    ne_of_gt (point.weight_pos 5)]
  ring

theorem kFourPendant235Probe_ne_zero_of_ne_zero {y : Fin 3 → ℝ} (hy : y ≠ 0) :
    kFourPendant235Probe y ≠ 0 := by
  intro hzero
  apply hy
  have hzero0 := congrFun hzero 0
  have hzero1 := congrFun hzero 1
  have hzero2 := congrFun hzero 2
  simp [kFourPendant235Probe] at hzero0 hzero1 hzero2
  funext index
  fin_cases index <;> simp <;> linarith

theorem kFourPendant235DualTightData_of_blind_of_weak
    (point : DirectionChartPoint 6) (hblind : ¬ KFourPendantCell235Fires point)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      ({2, 3, 5} : Finset (Fin 6))).PosSemidef) :
    KFourPathDualTightData point ({2, 3, 5} : Finset (Fin 6))
      (kFourPendant235ZMatrix point) kFourPendant235Probe := by
  simpa only [KFourPathDualTightData, kFourPendant235ZMatrix] using
    exists_nonnegative_tightDirection_of_zThreeDualWitness_of_gap_pullback
      (kFourPendant235DualWitness_of_not_fires point hblind) hweak kFourPendant235Probe
      kFourPendant235Probe_ne_zero_of_ne_zero
      (dotProduct_kFourPendant235Gap_probe_eq_zMatrix point)

/-! ## The twelve-path ledger -/

/-- Conditional tight-data producers for the five paths in the prior minor
atlas. -/
def KFourPriorPathDualSaturationLedger (point : DirectionChartPoint 6) : Prop :=
  ((directionChartGap kFourDirection point.mass point.weight
      ({1, 3, 4} : Finset (Fin 6))).PosSemidef →
    KFourPathDualTightData point ({1, 3, 4} : Finset (Fin 6))
      (kFourBand134ZMatrix point) kFourBand134Probe) ∧
  ((directionChartGap kFourDirection point.mass point.weight
      ({0, 2, 3} : Finset (Fin 6))).PosSemidef →
    KFourPathDualTightData point ({0, 2, 3} : Finset (Fin 6))
      (kFourPendant023ZMatrix point) kFourPendant023Probe) ∧
  ((directionChartGap kFourDirection point.mass point.weight
      ({1, 2, 3} : Finset (Fin 6))).PosSemidef →
    KFourPathDualTightData point ({1, 2, 3} : Finset (Fin 6))
      (kFourPendant123ZMatrix point) kFourPendant123Probe) ∧
  ((directionChartGap kFourDirection point.mass point.weight
      ({2, 3, 4} : Finset (Fin 6))).PosSemidef →
    KFourPathDualTightData point ({2, 3, 4} : Finset (Fin 6))
      (kFourPendant234ZMatrix point) kFourPendant234Probe) ∧
  ((directionChartGap kFourDirection point.mass point.weight
      ({2, 3, 5} : Finset (Fin 6))).PosSemidef →
    KFourPathDualTightData point ({2, 3, 5} : Finset (Fin 6))
      (kFourPendant235ZMatrix point) kFourPendant235Probe)

theorem kFourPriorPathDualSaturationLedger_of_allTreeBlind
    (point : DirectionChartPoint 6)
    (hblind : ¬ KFourAllTreeMinorAtlasCellFires point) :
    KFourPriorPathDualSaturationLedger point := by
  have hfull : ¬ KFourFullMinorAtlasCellFires point :=
    fun h => hblind (Or.inl h)
  have hband : ¬ KFourUnsignedBandTreeCellFires point :=
    fun h => hfull (Or.inl (Or.inl (Or.inr h)))
  have h023 : ¬ KFourPendantCell023Fires point :=
    fun h => hfull (Or.inr (Or.inl h))
  have h123 : ¬ KFourPendantCell123Fires point :=
    fun h => hfull (Or.inr (Or.inr (Or.inl h)))
  have h234 : ¬ KFourPendantCell234Fires point :=
    fun h => hfull (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have h235 : ¬ KFourPendantCell235Fires point :=
    fun h => hfull (Or.inr (Or.inr (Or.inr (Or.inr h))))
  exact ⟨kFourBand134DualTightData_of_blind_of_weak point hband,
    kFourPendant023DualTightData_of_blind_of_weak point h023,
    kFourPendant123DualTightData_of_blind_of_weak point h123,
    kFourPendant234DualTightData_of_blind_of_weak point h234,
    kFourPendant235DualTightData_of_blind_of_weak point h235⟩

/-- The exact kernel-coupling ledger for all twelve K4 path trees. -/
def KFourAllPathDualSaturationLedger (point : DirectionChartPoint 6) : Prop :=
  KFourPriorPathDualSaturationLedger point ∧
    KFourMissingPathDualSaturationLedger point

theorem kFourAllPathDualSaturationLedger_of_allTreeBlind
    (point : DirectionChartPoint 6)
    (hblind : ¬ KFourAllTreeMinorAtlasCellFires point) :
    KFourAllPathDualSaturationLedger point :=
  ⟨kFourPriorPathDualSaturationLedger_of_allTreeBlind point hblind,
    kFourMissingPathDualSaturationLedger_of_allTreeBlind point hblind⟩

/-! ## Spend all twelve path saturations in A3 -/

/-- The exact A3 residual retaining full obstruction data for all sixteen
trees and exact dual-to-kernel couplings for all twelve paths. -/
noncomputable def KFourKnifeBandRefinedAllPathSaturatedWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    KFourAllPathDualSaturationLedger point →
    (∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef) →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

theorem allPathSaturatedKFourKnifeBandRefined_of_missingPathSaturated
    (hmissing : KFourKnifeBandRefinedMissingPathSaturatedWeakToStrict) :
    KFourKnifeBandRefinedAllPathSaturatedWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hledger hallPaths hweak
  exact hmissing point hnotLayerA hnotExchange hnotAtlas hledger hallPaths.2 hweak

theorem missingPathSaturatedKFourKnifeBandRefined_of_allPathSaturated
    (hallPaths : KFourKnifeBandRefinedAllPathSaturatedWeakToStrict) :
    KFourKnifeBandRefinedMissingPathSaturatedWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hledger hmissing hweak
  exact hallPaths point hnotLayerA hnotExchange hnotAtlas hledger
    ⟨kFourPriorPathDualSaturationLedger_of_allTreeBlind point hnotAtlas, hmissing⟩ hweak

theorem kFourKnifeBandRefinedAllPathSaturated_iff_missingPathSaturated :
    KFourKnifeBandRefinedAllPathSaturatedWeakToStrict ↔
      KFourKnifeBandRefinedMissingPathSaturatedWeakToStrict :=
  ⟨missingPathSaturatedKFourKnifeBandRefined_of_allPathSaturated,
    allPathSaturatedKFourKnifeBandRefined_of_missingPathSaturated⟩

theorem kFourKnifeBandRefinedAllPathSaturated_iff :
    KFourKnifeBandRefinedAllPathSaturatedWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedAllPathSaturated_iff_missingPathSaturated.trans
    kFourKnifeBandRefinedMissingPathSaturated_iff

theorem kFourFamilySelection_iff_allPathSaturated :
    KFourFamilySelection ↔ KFourKnifeBandRefinedAllPathSaturatedWeakToStrict :=
  kFourFamilySelection_iff_missingPathSaturated.trans
    kFourKnifeBandRefinedAllPathSaturated_iff_missingPathSaturated.symm

end Gtz

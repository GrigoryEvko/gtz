import Gtz.Wave.KFourStarExchangeTreeWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# One-slot exchanges cannot close the K4 corank-two star wall

The amplified star package produces two genuine spanning trees with positive
quadratic reading on one kernel probe.  At the corank-two wall this is only a
stratifier.  The original tree gap kills a plane.  Inside that plane there is
always a nonzero vector orthogonal to the incoming chart direction; on this
vector a one-slot exchange reads as the negative outgoing boost square.
Consequently neither amplified repair can be positive definite.

This module makes that obstruction explicit and carries it into the exact A3
residual.  It rules out the tempting but invalid inference from one positive
probe reading to strict domination.
-/

namespace Gtz

open Matrix

/-! ## A kernel-plane vector orthogonal to any incoming direction -/

/-- Two independent kernel vectors contain a nonzero linear combination
orthogonal to any prescribed direction. -/
theorem exists_nonzero_kernel_orthogonal_of_kFourTreeGapCorankTwo
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (hcorank : KFourTreeGapCorankTwoData point tree)
    (incoming : Fin 3 → ℝ) :
    ∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧
      directionChartGap kFourDirection point.mass point.weight tree *ᵥ probe = 0 ∧
      incoming ⬝ᵥ probe = 0 := by
  obtain ⟨tight, second, pointer, htightNe, hpointerOut, htightKer,
    hpointerReads, hsecondNe, hsecondKer, hpointerOrth, hnotCollinear⟩ := hcorank
  by_cases htightOrth : incoming ⬝ᵥ tight = 0
  · exact ⟨tight, htightNe, htightKer, htightOrth⟩
  · let probe := (incoming ⬝ᵥ second) • tight - (incoming ⬝ᵥ tight) • second
    have hprobeOrth : incoming ⬝ᵥ probe = 0 := by
      simp only [probe, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      ring
    have hprobeKer : directionChartGap kFourDirection point.mass point.weight tree
        *ᵥ probe = 0 := by
      simpa only [probe, sub_eq_add_neg, neg_smul] using
        mulVec_combination_eq_zero htightKer hsecondKer
          (incoming ⬝ᵥ second) (-(incoming ⬝ᵥ tight))
    have hprobeNe : probe ≠ 0 := by
      intro hprobeZero
      apply hnotCollinear
      refine ⟨(incoming ⬝ᵥ second) / (incoming ⬝ᵥ tight), ?_⟩
      funext index
      have hindex := congrFun hprobeZero index
      simp only [probe, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hindex
      change (incoming ⬝ᵥ second) * tight index
        - (incoming ⬝ᵥ tight) * second index = 0 at hindex
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div]
      exact (eq_div_iff htightOrth).2 (by
        simpa only [mul_comm] using (sub_eq_zero.mp hindex).symm)
    exact ⟨probe, hprobeNe, hprobeKer, hprobeOrth⟩

/-! ## The universal one-slot refusal -/

/-- Every one-slot exchange of a K4 tree whose gap has two independent kernel
directions fails to be positive definite.  No positivity or sign hypothesis on
the exchanged reading is needed. -/
theorem not_posDef_exchange_of_kFourTreeGapCorankTwo
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (hcorank : KFourTreeGapCorankTwoData point tree)
    {outLabel incLabel : Fin 6} (hout : outLabel ∈ tree)
    (hinc : incLabel ∉ tree) :
    ¬ (directionChartGap kFourDirection point.mass point.weight
      (insert incLabel (tree.erase outLabel))).PosDef := by
  obtain ⟨probe, hprobeNe, hprobeKer, hprobeOrth⟩ :=
    exists_nonzero_kernel_orthogonal_of_kFourTreeGapCorankTwo point hcorank
      (kFourDirection incLabel)
  intro hposDef
  have hpositive : 0 < probe ⬝ᵥ
      (directionChartGap kFourDirection point.mass point.weight
        (insert incLabel (tree.erase outLabel)) *ᵥ probe) := by
    have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobeNe
    rwa [star_trivial] at h
  rw [dotProduct_exchangeGap_at_kernel kFourDirection point.mass point.weight
      hout hinc hprobeKer,
    hprobeOrth, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_sub]
    at hpositive
  have hquot : 0 ≤ point.mass outLabel / point.weight outLabel :=
    (div_pos (point.mass_pos outLabel) (point.weight_pos outLabel)).le
  nlinarith [mul_nonneg hquot (sq_nonneg (kFourDirection outLabel ⬝ᵥ probe))]

/-! ## Spend the refusal on both amplified spanning trees -/

/-- The spanning-exchange package together with the fact that neither repair
is a strict dominator. -/
def KFourTreeAmplifiedRefusedExchangeData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : Prop :=
  ∃ x : Fin 3 → ℝ, x ≠ 0 ∧
    directionChartGap kFourDirection point.mass point.weight tree *ᵥ x = 0 ∧
    ∃ ampLabel outOne outTwo : Fin 6,
      ampLabel ∉ tree ∧ outOne ∈ tree ∧ outTwo ∈ tree ∧ outOne ≠ outTwo ∧
      insert ampLabel (tree.erase outOne) ∈ kFourSpanningTreeList ∧
      insert ampLabel (tree.erase outTwo) ∈ kFourSpanningTreeList ∧
      ¬ (directionChartGap kFourDirection point.mass point.weight
          (insert ampLabel (tree.erase outOne))).PosDef ∧
      ¬ (directionChartGap kFourDirection point.mass point.weight
          (insert ampLabel (tree.erase outTwo))).PosDef ∧
      (kFourDirection outOne ⬝ᵥ x) ^ 2
        < (kFourDirection ampLabel ⬝ᵥ x) ^ 2 ∧
      (kFourDirection outTwo ⬝ᵥ x) ^ 2
        < (kFourDirection ampLabel ⬝ᵥ x) ^ 2 ∧
      x ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight
          (insert ampLabel (tree.erase outOne)) *ᵥ x)
        = point.mass ampLabel / point.weight ampLabel
            * (kFourDirection ampLabel ⬝ᵥ x) ^ 2
          - point.mass outOne / point.weight outOne
            * (kFourDirection outOne ⬝ᵥ x) ^ 2 ∧
      x ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight
          (insert ampLabel (tree.erase outTwo)) *ᵥ x)
        = point.mass ampLabel / point.weight ampLabel
            * (kFourDirection ampLabel ⬝ᵥ x) ^ 2
          - point.mass outTwo / point.weight outTwo
            * (kFourDirection outTwo ⬝ᵥ x) ^ 2 ∧
      (0 < x ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight
          (insert ampLabel (tree.erase outOne)) *ᵥ x) ∨
        0 < x ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight
          (insert ampLabel (tree.erase outTwo)) *ᵥ x) ∨
        (point.mass ampLabel / point.weight ampLabel
            < point.mass outOne / point.weight outOne ∧
          point.mass ampLabel / point.weight ampLabel
            < point.mass outTwo / point.weight outTwo))

theorem kFourTreeAmplifiedRefusedExchangeData_of_spanning
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (hcorank : KFourTreeGapCorankTwoData point tree)
    (hdata : KFourTreeAmplifiedSpanningExchangeData point tree) :
    KFourTreeAmplifiedRefusedExchangeData point tree := by
  obtain ⟨x, hxne, hker, ampLabel, outOne, outTwo, hampOut, houtOne, houtTwo,
    houtNe, htreeOne, htreeTwo, hsquareOne, hsquareTwo, hreadOne, hreadTwo,
    hsplit⟩ := hdata
  exact ⟨x, hxne, hker, ampLabel, outOne, outTwo, hampOut, houtOne, houtTwo,
    houtNe, htreeOne, htreeTwo,
    not_posDef_exchange_of_kFourTreeGapCorankTwo point hcorank houtOne hampOut,
    not_posDef_exchange_of_kFourTreeGapCorankTwo point hcorank houtTwo hampOut,
    hsquareOne, hsquareTwo, hreadOne, hreadTwo, hsplit⟩

theorem kFourTreeAmplifiedSpanningExchangeData_of_refused
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (hdata : KFourTreeAmplifiedRefusedExchangeData point tree) :
    KFourTreeAmplifiedSpanningExchangeData point tree := by
  obtain ⟨x, hxne, hker, ampLabel, outOne, outTwo, hampOut, houtOne, houtTwo,
    houtNe, htreeOne, htreeTwo, _, _, hsquareOne, hsquareTwo, hreadOne, hreadTwo,
    hsplit⟩ := hdata
  exact ⟨x, hxne, hker, ampLabel, outOne, outTwo, hampOut, houtOne, houtTwo,
    houtNe, htreeOne, htreeTwo, hsquareOne, hsquareTwo, hreadOne, hreadTwo, hsplit⟩

/-! ## The exact refused-exchange wall and registry joint -/

def KFourTreeStarRefusedExchangeWallData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : Prop :=
  KFourTreeStarCorankWallData point tree ∧
  KFourTreeAmplifiedRefusedExchangeData point tree

def KFourWeakTreeStarRefusedExchangeWallResidual
    (point : DirectionChartPoint 6) : Prop :=
  ∃ tree ∈ kFourSpanningTreeList,
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef ∧
    KFourTreeWindowData point tree ∧
    (KFourTreeWindowAllPivotWallData point tree ∨
      KFourTreeStarRefusedExchangeWallData point tree)

theorem kFourWeakTreeStarRefusedExchangeWallResidual_of_spanningExchangeResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeStarSpanningExchangeWallResidual point) :
    KFourWeakTreeStarRefusedExchangeWallResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | hstar⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl hpivot⟩
  · exact ⟨tree, htree, hgap, hwindow, Or.inr ⟨hstar.1,
      kFourTreeAmplifiedRefusedExchangeData_of_spanning point hstar.1.2.1
        hstar.2⟩⟩

theorem kFourWeakTreeStarSpanningExchangeWallResidual_of_refusedExchangeResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeStarRefusedExchangeWallResidual point) :
    KFourWeakTreeStarSpanningExchangeWallResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | hstar⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl hpivot⟩
  · exact ⟨tree, htree, hgap, hwindow, Or.inr ⟨hstar.1,
      kFourTreeAmplifiedSpanningExchangeData_of_refused point hstar.2⟩⟩

theorem kFourWeakTreeStarRefusedExchangeWallResidual_iff_spanningExchangeResidual
    (point : DirectionChartPoint 6) :
    KFourWeakTreeStarRefusedExchangeWallResidual point ↔
      KFourWeakTreeStarSpanningExchangeWallResidual point :=
  ⟨kFourWeakTreeStarSpanningExchangeWallResidual_of_refusedExchangeResidual point,
    kFourWeakTreeStarRefusedExchangeWallResidual_of_spanningExchangeResidual point⟩

/-- **THE REFUSED-EXCHANGE A3 JOINT.**  Positive reading on an amplified repair
is retained, but both one-slot repairs are now explicitly known not to be the
strict tree required by the conclusion. -/
noncomputable def KFourKnifeBandRefinedTreeStarRefusedExchangeWallWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    KFourWeakTreeStarRefusedExchangeWallResidual point →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

theorem kFourKnifeBandRefinedTreeStarRefusedExchangeWall_iff_spanningExchange :
    KFourKnifeBandRefinedTreeStarRefusedExchangeWallWeakToStrict ↔
      KFourKnifeBandRefinedTreeStarSpanningExchangeWallWeakToStrict := by
  constructor
  · intro hrefused point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hrefused point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeStarRefusedExchangeWallResidual_of_spanningExchangeResidual
        point hwitness)
  · intro hspan point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hspan point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeStarSpanningExchangeWallResidual_of_refusedExchangeResidual
        point hwitness)

theorem kFourKnifeBandRefinedTreeStarRefusedExchangeWall_iff :
    KFourKnifeBandRefinedTreeStarRefusedExchangeWallWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedTreeStarRefusedExchangeWall_iff_spanningExchange.trans
    kFourKnifeBandRefinedTreeStarSpanningExchangeWall_iff

theorem kFourFamilySelection_iff_treeStarRefusedExchangeWall :
    KFourFamilySelection ↔
      KFourKnifeBandRefinedTreeStarRefusedExchangeWallWeakToStrict :=
  kFourFamilySelection_iff_treeStarSpanningExchangeWall.trans
    kFourKnifeBandRefinedTreeStarRefusedExchangeWall_iff_spanningExchange.symm

end Gtz

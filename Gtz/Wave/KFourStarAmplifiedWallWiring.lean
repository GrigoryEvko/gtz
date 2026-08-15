import Gtz.Wave.KFourStarWallWiring
import Gtz.Design.StarAmplifiedExchange

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# Spend the amplified exchange on the final K4 star wall

The registered K4 residual already restricts its singular branch to the four
vertex stars and exposes a rank-one gap with two transverse repair pointers.
`StarAmplifiedExchange` supplies a second, complementary piece of structure:
on every weak-not-strict star there is a kernel probe, one opposite-triangle
label, and two distinct outgoing star labels whose squared readings are both
strictly amplified.

This module wires that producer into the residual.  Besides retaining the two
exact exchange identities, it isolates the scalar obstruction left by the
conditional exchange theorem.  Either one of the two exchanged sets reads
strictly positively on the probe, or the incoming boost quotient is strictly
smaller than both outgoing quotients.  The latter is the only branch on which
the amplified exchange itself is silent.

The enriched residual is proved pointwise equivalent to the preceding star
wall, so the registry gains usable data without acquiring a new assumption.
-/

namespace Gtz

open Matrix

/-! ## A common amplified-triangle interface for all four stars -/

/-- The common conclusion of the four landed star-amplification theorems. -/
def KFourTreeAmplifiedTriangleData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : Prop :=
  ∃ x : Fin 3 → ℝ, x ≠ 0 ∧
    directionChartGap kFourDirection point.mass point.weight tree *ᵥ x = 0 ∧
    ∃ ampLabel outOne outTwo : Fin 6,
      ampLabel ∉ tree ∧ outOne ∈ tree ∧ outTwo ∈ tree ∧ outOne ≠ outTwo ∧
      (kFourDirection outOne ⬝ᵥ x) ^ 2
        < (kFourDirection ampLabel ⬝ᵥ x) ^ 2 ∧
      (kFourDirection outTwo ⬝ᵥ x) ^ 2
        < (kFourDirection ampLabel ⬝ᵥ x) ^ 2

/-- Dispatch the four individual amplified-triangle theorems through the
finite star classifier. -/
theorem kFourTreeAmplifiedTriangleData_of_star
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (hstar : tree ∈ kFourStarList)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hnot : ¬ (directionChartGap kFourDirection point.mass point.weight
      tree).PosDef) :
    KFourTreeAmplifiedTriangleData point tree := by
  simp only [kFourStarList, List.mem_cons, List.not_mem_nil, or_false] at hstar
  rcases hstar with rfl | rfl | rfl | rfl
  · simpa [KFourTreeAmplifiedTriangleData] using
      kFourStarA_exists_amplified_triangle point hpsd hnot
  · simpa [KFourTreeAmplifiedTriangleData] using
      kFourStarB_exists_amplified_triangle point hpsd hnot
  · simpa [KFourTreeAmplifiedTriangleData] using
      kFourStarC_exists_amplified_triangle point hpsd hnot
  · simpa [KFourTreeAmplifiedTriangleData] using
      kFourStarGauge_exists_amplified_triangle point hpsd hnot

/-! ## Exact exchange readings and the quotient wall -/

/-- The amplified data after evaluating both exchanges.  The last disjunction
is exhaustive: one exchange reads positively on the kernel probe, or the
incoming quotient is strictly below both outgoing quotients. -/
def KFourTreeAmplifiedExchangeData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : Prop :=
  ∃ x : Fin 3 → ℝ, x ≠ 0 ∧
    directionChartGap kFourDirection point.mass point.weight tree *ᵥ x = 0 ∧
    ∃ ampLabel outOne outTwo : Fin 6,
      ampLabel ∉ tree ∧ outOne ∈ tree ∧ outTwo ∈ tree ∧ outOne ≠ outTwo ∧
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

/-- Evaluate both exchanges and split the two quotient comparisons. -/
theorem kFourTreeAmplifiedExchangeData_of_triangle
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (htriangle : KFourTreeAmplifiedTriangleData point tree) :
    KFourTreeAmplifiedExchangeData point tree := by
  obtain ⟨x, hxne, hker, ampLabel, outOne, outTwo, hampOut, houtOne,
    houtTwo, houtNe, hampOne, hampTwo⟩ := htriangle
  have hreadOne := dotProduct_exchangeGap_at_kernel
    kFourDirection point.mass point.weight houtOne hampOut hker
  have hreadTwo := dotProduct_exchangeGap_at_kernel
    kFourDirection point.mass point.weight houtTwo hampOut hker
  refine ⟨x, hxne, hker, ampLabel, outOne, outTwo, hampOut, houtOne,
    houtTwo, houtNe, hampOne, hampTwo, hreadOne, hreadTwo, ?_⟩
  by_cases hquotOne : point.mass outOne / point.weight outOne
      ≤ point.mass ampLabel / point.weight ampLabel
  · exact Or.inl (exchangeGap_pos_at_kernel_of_le
      kFourDirection point.mass point.weight houtOne hampOut
      (point.mass_pos outOne) (point.weight_pos outOne) hker hampOne hquotOne)
  · have hreverseOne : point.mass ampLabel / point.weight ampLabel
        < point.mass outOne / point.weight outOne := lt_of_not_ge hquotOne
    by_cases hquotTwo : point.mass outTwo / point.weight outTwo
        ≤ point.mass ampLabel / point.weight ampLabel
    · exact Or.inr (Or.inl (exchangeGap_pos_at_kernel_of_le
        kFourDirection point.mass point.weight houtTwo hampOut
        (point.mass_pos outTwo) (point.weight_pos outTwo) hker hampTwo hquotTwo))
    · exact Or.inr (Or.inr ⟨hreverseOne, lt_of_not_ge hquotTwo⟩)

/-- Every weak-not-strict vertex star carries the evaluated exchange package. -/
theorem kFourTreeAmplifiedExchangeData_of_star
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (hstar : tree ∈ kFourStarList)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hnot : ¬ (directionChartGap kFourDirection point.mass point.weight
      tree).PosDef) :
    KFourTreeAmplifiedExchangeData point tree :=
  kFourTreeAmplifiedExchangeData_of_triangle point
    (kFourTreeAmplifiedTriangleData_of_star point hstar hpsd hnot)

/-! ## The exact amplified star wall -/

/-- The final singular wall with the rank-one/two-pointer data and the
amplified exchange evaluated on the same weak star. -/
def KFourTreeStarAmplifiedWallData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : Prop :=
  KFourTreeStarCorankWallData point tree ∧
  KFourTreeAmplifiedExchangeData point tree

/-- Spend the amplified-exchange producer on the existing star wall. -/
theorem kFourTreeStarAmplifiedWallData_of_starWall
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hwindow : KFourTreeWindowData point tree)
    (hstar : KFourTreeStarCorankWallData point tree) :
    KFourTreeStarAmplifiedWallData point tree :=
  ⟨hstar, kFourTreeAmplifiedExchangeData_of_star point hstar.1 hgap
    (not_posDef_of_kFourTreeWindowData point hwindow)⟩

/-- The K4 residual after the amplified exchange has fired on the singular
star branch. -/
def KFourWeakTreeStarAmplifiedWallResidual
    (point : DirectionChartPoint 6) : Prop :=
  ∃ tree ∈ kFourSpanningTreeList,
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef ∧
    KFourTreeWindowData point tree ∧
    (KFourTreeWindowAllPivotWallData point tree ∨
      KFourTreeStarAmplifiedWallData point tree)

theorem kFourWeakTreeStarAmplifiedWallResidual_of_starWallResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeStarWallResidual point) :
    KFourWeakTreeStarAmplifiedWallResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | hstar⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl hpivot⟩
  · exact ⟨tree, htree, hgap, hwindow, Or.inr
      (kFourTreeStarAmplifiedWallData_of_starWall point hgap hwindow hstar)⟩

theorem kFourWeakTreeStarWallResidual_of_amplifiedWallResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeStarAmplifiedWallResidual point) :
    KFourWeakTreeStarWallResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | hstar⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl hpivot⟩
  · exact ⟨tree, htree, hgap, hwindow, Or.inr hstar.1⟩

theorem kFourWeakTreeStarAmplifiedWallResidual_iff_starWallResidual
    (point : DirectionChartPoint 6) :
    KFourWeakTreeStarAmplifiedWallResidual point ↔
      KFourWeakTreeStarWallResidual point :=
  ⟨kFourWeakTreeStarWallResidual_of_amplifiedWallResidual point,
    kFourWeakTreeStarAmplifiedWallResidual_of_starWallResidual point⟩

/-! ## Registry joints -/

/-- **THE AMPLIFIED A3 JOINT.**  The singular wall now includes both exact
exchange readings and the exhaustive positive-exchange/ratio-wall split. -/
noncomputable def KFourKnifeBandRefinedTreeStarAmplifiedWallWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    KFourWeakTreeStarAmplifiedWallResidual point →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

theorem kFourKnifeBandRefinedTreeStarAmplifiedWall_iff_starWall :
    KFourKnifeBandRefinedTreeStarAmplifiedWallWeakToStrict ↔
      KFourKnifeBandRefinedTreeStarWallWeakToStrict := by
  constructor
  · intro hamp point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hamp point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeStarAmplifiedWallResidual_of_starWallResidual point hwitness)
  · intro hwall point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hwall point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeStarWallResidual_of_amplifiedWallResidual point hwitness)

theorem kFourKnifeBandRefinedTreeStarAmplifiedWall_iff :
    KFourKnifeBandRefinedTreeStarAmplifiedWallWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedTreeStarAmplifiedWall_iff_starWall.trans
    kFourKnifeBandRefinedTreeStarWall_iff

theorem kFourFamilySelection_iff_treeStarAmplifiedWall :
    KFourFamilySelection ↔
      KFourKnifeBandRefinedTreeStarAmplifiedWallWeakToStrict :=
  kFourFamilySelection_iff_treeStarWall.trans
    kFourKnifeBandRefinedTreeStarAmplifiedWall_iff_starWall.symm

end Gtz

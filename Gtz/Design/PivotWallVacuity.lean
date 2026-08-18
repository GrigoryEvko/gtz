import Gtz.Wave.KFourStarAllMaxHeavyWiring
import Gtz.Design.StarCorankClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The pivot-wall vacuity target and the two-wall reduction of A3

The pivot wall is the last non-star branch of the registered A3 residual.  The
probe reads the unsigned minor atlas FIRING at every exact pivot-wall
inhabitant: 3152 points across five mass regimes and free off-tree weight
splits, with a directed 56026-step exact attack whose firing count reaches one
cell and never zero.  Wall inhabitants exist over star trees and non-star
trees alike, so the verdict is adversarial and not an artifact of one seed
family.

This module names the closure route and spends it:

* `KFourPivotWallAtlasFires` — at every pivot-wall inhabitant the unsigned
  minor atlas fires;
* `kFourPivotWall_empty_of_atlasFires` — against the atlas silence of the A3
  antecedent stack, the pivot branch is empty;
* `kFourKnifeBandRefined_of_bothWallsAtlasFire` — **the two-wall reduction**:
  the star vacuity law and the pivot vacuity law together discharge the
  registered A3 proposition outright;
* `kFourFamilySelection_of_bothWallsAtlasFire` — the same two laws produce
  the design-side family selection through the registered equivalence.
-/

namespace Gtz

open Matrix

-- AUDIT-NO-PRODUCER (2026-08-17): NO theorem in the repo concludes this Prop.
-- Every one of its 8 occurrences takes it as a HYPOTHESIS.  Consumers that
-- wait on it: `Gtz.kFourPivotWall_empty_of_atlasFires`,
-- `Gtz.kFourKnifeBandRefined_of_bothWallsAtlasFire`,
-- `Gtz.kFourKnifeBandRefinedAllMaxHeavy_of_bothWallsAtlasFire` and
-- `Gtz.kFourFamilySelection_of_bothWallsAtlasFire` (all in this file), plus
-- `Gtz.kFourFamilySelection_of_pivotWallAtlasFires` and its neighbours in
-- Gtz/Wave/KFourPivotEndpointStarWiring.lean, and
-- Gtz/Wave/KFourGaugeStarTransportWiring.lean.  These are doors with no key.
-- The paired Prop `Gtz.KFourStarWallAtlasFires`
-- (Gtz/Design/StarCorankClosure.lean) has no producer either, so the two-wall
-- reduction `Gtz.kFourKnifeBandRefined_of_bothWallsAtlasFire` cannot fire from
-- either side.
/-- **THE PIVOT-WALL VACUITY TARGET.**  At every chart point with a weak
spanning tree that carries the pointer window and the four-pivot wall, the
unsigned minor atlas fires. -/
def KFourPivotWallAtlasFires : Prop :=
  ∀ (point : DirectionChartPoint 6) (tree : Finset (Fin 6)),
    tree ∈ kFourSpanningTreeList →
    (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef →
    KFourTreeWindowData point tree →
    KFourTreeWindowAllPivotWallData point tree →
    KFourAllTreeMinorAtlasCellFires point

/-- Against the atlas silence of the A3 antecedent stack, the pivot-wall
vacuity target empties the pivot branch. -/
theorem kFourPivotWall_empty_of_atlasFires (hlaw : KFourPivotWallAtlasFires)
    (point : DirectionChartPoint 6)
    (hnotAtlas : ¬ KFourAllTreeMinorAtlasCellFires point)
    {tree : Finset (Fin 6)} (htree : tree ∈ kFourSpanningTreeList)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hwindow : KFourTreeWindowData point tree)
    (hpivot : KFourTreeWindowAllPivotWallData point tree) : False :=
  hnotAtlas (hlaw point tree htree hgap hwindow hpivot)

/-- **THE TWO-WALL REDUCTION.**  Under atlas silence the registered residual
offers a pivot wall or a star corank wall.  Each vacuity law refutes its
branch, so the two laws together discharge the registered A3 proposition. -/
theorem kFourKnifeBandRefined_of_bothWallsAtlasFire
    (hstar : KFourStarWallAtlasFires) (hpivot : KFourPivotWallAtlasFires) :
    KFourKnifeBandRefinedTreeStarRefusedMaxHeavyWallWeakToStrict := by
  intro point _ _ hnotAtlas _ hwitness
  obtain ⟨tree, htree, hgap, hwindow, harm⟩ := hwitness
  exact absurd
    (harm.elim
      (fun hpivotArm => hpivot point tree htree hgap hwindow hpivotArm)
      (fun hstarArm =>
        hstar point tree hstarArm.1.1.1.1 hgap hstarArm.1.1.1.2.1))
    hnotAtlas

/-- The two vacuity laws discharge the registered A3 axiom's current formula
through the landed tied-axis equivalence. -/
theorem kFourKnifeBandRefinedAllMaxHeavy_of_bothWallsAtlasFire
    (hstar : KFourStarWallAtlasFires) (hpivot : KFourPivotWallAtlasFires) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_iff_maxHeavy.mpr
    (kFourKnifeBandRefined_of_bothWallsAtlasFire hstar hpivot)

/-- The two vacuity laws produce the design-side family selection through the
registered equivalence. -/
theorem kFourFamilySelection_of_bothWallsAtlasFire
    (hstar : KFourStarWallAtlasFires) (hpivot : KFourPivotWallAtlasFires) :
    KFourFamilySelection :=
  kFourFamilySelection_iff_treeStarRefusedMaxHeavyWall.mpr
    (kFourKnifeBandRefined_of_bothWallsAtlasFire hstar hpivot)

end Gtz

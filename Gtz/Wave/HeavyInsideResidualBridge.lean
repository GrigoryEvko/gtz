import Gtz.Wave.CappedSharpFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The heavy-inside residual reduces to one conjunctive emptiness

The residual Prop `Gtz.OneAxisZeroHeavyInsideResidual` carries the three
outside floors among its hypotheses, and on the heavy-inside cell those
floors already force the excluded-pair excess nonnegative
(`Gtz.corner_oneAxisZero_heavyInside_floors_force_excess`).  So a certificate
may ASSUME `S ≥ 0` without proving it, and the whole residual reduces to the
emptiness of ONE conjunctive system
(`Gtz.oneAxisZeroHeavyInsideResidual_of_geometry`):

  `{ cell H,  S ≥ 0,  r_{d} ≥ 1 for every outside `d` }  =  ∅` .

No tie hypothesis, no disjunction, no selector.  The `min` of the measured
formulation is existential and must NOT be split into one statement per
outside atom: at every stored survivor the three readings straddle one, so
the per-atom statement is false while the conjunction is empty.

The odds, downdate and mixed clauses of the Prop are not needed by the
bridge: they are consequences of the floors on this cell, so the reduction
discards them and leaves the smallest system a certificate must refute.
-/

namespace Gtz

open Matrix Finset

/-- **THE RESIDUAL BRIDGE.**  To discharge the heavy-inside residual it is
enough to refute the conjunctive geometry: the cell, the excluded-pair excess
nonnegative, and the three outside floors.  The excess hypothesis is free —
the floors force it — so a certificate may consume it. -/
theorem oneAxisZeroHeavyInsideResidual_of_geometry
    (hgeom : ∀ (D : WeightedDesign 6 3) (x y z : Fin 6), x ≠ y → x ≠ z → y ≠ z →
      ∀ lam : ℝ, 0 < lam → ∀ u : Fin 3 → ℝ, u ⬝ᵥ u = 1 →
      subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u →
      D.atom x ⬝ᵥ u = 0 → D.atom z ⬝ᵥ u ≠ 0 →
      ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef →
      0 ≤ D.weight x
            * (D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom x) - 1)
          + D.weight z
            * (D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom z) - 1) →
      (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        1 ≤ D.atom d ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
          - 1)⁻¹ *ᵥ D.atom d)) →
      False) :
    OneAxisZeroHeavyInsideResidual := by
  intro D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz hnotz hfloors
    _hodds _hdown _hmixed
  exact hgeom D x y z hxy hxz hyz lam hlam u hunit hgap hax haz hnotz
    (corner_oneAxisZero_heavyInside_floors_force_excess D hxy hxz hyz hlam
      hunit hgap hax haz hnotz hfloors)
    hfloors

end Gtz

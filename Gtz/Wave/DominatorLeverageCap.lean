/-
# The leverage cap of a weak dominator at a tie

Two landed laws meet on the same triple and pin it from both sides.

* From BELOW, `Gtz.dominator_bracket_floor_sharp`: a weak dominator carries
  squared bracket at least its total leverage minus two, so its BRACKET MASS
  obeys `m_C ≥ t_xt_yt_z·(ℓ_x + ℓ_y + ℓ_z − 2)`.
* From ABOVE, `Gtz.isTie_bracket_tax`: at a tie the same mass is at most one
  of the triple's own member weights.

Together (`Gtz.isTie_dominator_leverage_cap`):

  `t_xt_yt_z·(ℓ_x + ℓ_y + ℓ_z − 2) ≤ t_member`   for some member,

so at a tie **a weak dominator cannot carry large total leverage unless its
weights are very unequal**: dividing by the weight product
(`Gtz.isTie_dominator_leverage_total_cap`),

  `ℓ_x + ℓ_y + ℓ_z ≤ 2 + t_max / (t_xt_yt_z)` .

Both sides are multiplicative — a product of the three weights against a
single weight — which is the shape the aggregation doctrine asks for.  The
statement is tie-necessary, consumes the dominator, and is field-blind: the
realness of this lane stays at `Gtz.pair_mass_nonneg` and
`Gtz.bracket_threeCycle_nonneg`.

The trace floor `ℓ_x + ℓ_y + ℓ_z ≥ 3` (`Gtz.dominator_trace_floor`) makes the
left side at least the weight product, so the cap never degenerates into a
triviality: it always says something about `t_max` against `t_xt_yt_z`.
-/
import Gtz.Wave.DominatorWedgeFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

/-! ## 1. The mass floor of a dominator -/

/-- **THE BRACKET MASS OF A WEAK DOMINATOR IS AT LEAST ITS WEIGHTED LEVERAGE
DEFICIT.**  The sharpened bracket floor, multiplied by the weight product. -/
theorem dominator_bracketMass_floor (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6))) :
    D.weight x * (D.weight y * (D.weight z
        * (leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z) - 2)))
      ≤ D.weight x * (D.weight y * (D.weight z * atomBracket D x y z ^ 2)) := by
  have hfloor := dominator_bracket_floor_sharp D hxy hxz hyz hdominates
  have hx := (D.weight_pos x).le
  have hy := (D.weight_pos y).le
  have hz := (D.weight_pos z).le
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfloor hz) hy) hx

/-! ## 2. The cap -/

/-- **THE LEVERAGE CAP OF A WEAK DOMINATOR AT A TIE.**  At a tie, a weakly
dominating triple obeys

  `t_xt_yt_z·(ℓ_x + ℓ_y + ℓ_z − 2) ≤ t_member`

for one of its own members: the mass floor from the sharpened bracket, the
mass cap from the contraction tax, and the two meet on the same number. -/
theorem isTie_dominator_leverage_cap (D : WeightedDesign 6 3) (htie : IsTie D)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6))) :
    ∃ member ∈ ({x, y, z} : Finset (Fin 6)),
      D.weight x * (D.weight y * (D.weight z
          * (leverageOf (D.atom x) + leverageOf (D.atom y)
            + leverageOf (D.atom z) - 2)))
        ≤ D.weight member := by
  obtain ⟨member, hmem, hle⟩ := isTie_bracket_tax D htie hxy hxz hyz
  exact ⟨member, hmem, le_trans
    (dominator_bracketMass_floor D hxy hxz hyz hdominates) hle⟩

/-- **THE TOTAL LEVERAGE IS CAPPED BY THE WEIGHT SPREAD.**  Dividing the cap
by the positive weight product: at a tie a weak dominator's total leverage
never exceeds two plus one member weight over the product of all three.  A
dominator with large leverage must therefore have very unequal weights. -/
theorem isTie_dominator_leverage_total_cap (D : WeightedDesign 6 3) (htie : IsTie D)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6))) :
    ∃ member ∈ ({x, y, z} : Finset (Fin 6)),
      leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z)
        ≤ 2 + D.weight member
          / (D.weight x * (D.weight y * D.weight z)) := by
  obtain ⟨member, hmem, hle⟩ :=
    isTie_dominator_leverage_cap D htie hxy hxz hyz hdominates
  refine ⟨member, hmem, ?_⟩
  have hprod : 0 < D.weight x * (D.weight y * D.weight z) :=
    mul_pos (D.weight_pos x) (mul_pos (D.weight_pos y) (D.weight_pos z))
  rw [← sub_le_iff_le_add', le_div_iff₀ hprod]
  nlinarith [hle]

/-- **THE CAP IS NEVER VACUOUS.**  The trace floor makes the leverage deficit
at least one, so the cap always compares the weight product to a member
weight: at a tie every weak dominator satisfies
`t_xt_yt_z ≤ t_member` for one of its members. -/
theorem isTie_dominator_weightProduct_le (D : WeightedDesign 6 3) (htie : IsTie D)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6))) :
    ∃ member ∈ ({x, y, z} : Finset (Fin 6)),
      D.weight x * (D.weight y * D.weight z) ≤ D.weight member := by
  obtain ⟨member, hmem, hle⟩ :=
    isTie_dominator_leverage_cap D htie hxy hxz hyz hdominates
  refine ⟨member, hmem, le_trans ?_ hle⟩
  have htrace := dominator_trace_floor D hxy hxz hyz hdominates
  have hx := (D.weight_pos x).le
  have hy := (D.weight_pos y).le
  have hz := (D.weight_pos z).le
  have hone : (1 : ℝ) ≤ leverageOf (D.atom x) + leverageOf (D.atom y)
      + leverageOf (D.atom z) - 2 := by linarith
  nlinarith [hone, mul_nonneg hx (mul_nonneg hy hz)]

end Gtz

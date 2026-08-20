import Gtz.Wave.LedgerSharpSFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The floors force the excluded excess, with no tie

On the heavy-inside cell the three outside floors alone force the
excluded-pair excess nonnegative.  No tie hypothesis is needed anywhere: the
coweight ledger is an identity, the self-read of the surviving inside atom is
tie-free on the cell, and the coweights of a design of six atoms are
positive.

This removes one clause from every downstream argument.  The residual Prop
carries `S ≥ 0` implicitly through its floors, so a certificate that refutes
the floors may be stated as PURE GEOMETRY on the cell — no tie, no
disjunction:

  `cell H ∧ (the three outside floors)  ⟹  S ≥ 0` .

Composed with the transported pair system
(`Gtz.corner_oneAxisZero_heavyInside_isTie_iff_transportedPairs`) and the
`z`-pair collapse (`Gtz.corner_anchor_zPair_iff_floor`), the heavy-inside tie
is exactly the three floors, so any geometric statement contradicting them on
`{cell H, S ≥ 0}` discharges the residual.
-/

namespace Gtz

open Matrix Finset

/-- **THE FLOORS FORCE THE EXCESS.**  On the heavy-inside cell the three
outside floors alone give `S ≥ 0` — tie-free.  The ledger identity splits `S`
into coweighted member excesses, the self-read makes the inside excess
nonnegative on the cell, and every coweight of a six-atom design is
positive. -/
theorem corner_oneAxisZero_heavyInside_floors_force_excess (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hfloors : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      1 ≤ D.atom d ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
        - 1)⁻¹ *ᵥ D.atom d)) :
    0 ≤ D.weight x
          * (D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom x) - 1)
        + D.weight z
          * (D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z) - 1) := by
  classical
  have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  have hident := corner_oneAxisZero_heavyInside_ledger_identity D hxy hxz hyz hAy
  have hm : 2 ≤ (6 : ℕ) := by norm_num
  -- the inside excess is nonnegative on the cell, with no tie
  have hself := corner_oneAxisZero_heavyInside_selfRead_ge_one D hxy hxz hyz
    hlam hunit hgap hax haz hnotz
  have hcoy : (0 : ℝ) ≤ 1 - D.weight y := by linarith [weight_lt_one D hm y]
  have hinside : (0 : ℝ) ≤ (1 - D.weight y)
      * (D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
          - 1)⁻¹ *ᵥ D.atom y) - 1) :=
    mul_nonneg hcoy (by linarith)
  -- the outside excesses are nonnegative by the floors
  have houts : (0 : ℝ)
      ≤ ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          (1 - D.weight d)
            * (D.atom d ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom d) - 1) := by
    refine Finset.sum_nonneg fun d hd => ?_
    exact mul_nonneg (by linarith [weight_lt_one D hm d]) (by linarith [hfloors d hd])
  linarith [hident, hinside, houts]

end Gtz

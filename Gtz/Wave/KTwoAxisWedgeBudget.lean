/-
# The axis wedge budget, and why the erased scale is the hinge's own currency

The two-zero chart carries an "erased scale" `P`, and the `(5,3)` bridge
identified it as the squared plane part of an outside atom.  This module says
what that is invariantly, and the answer puts the chart directly into the
hinge's currency:

  **`P = crossNormSq g_x g_d`** — the erased scale IS the WEDGE of the outside
  atom with the axis atom (`Gtz.axisWedge_eq_leverage_sub_pairing_sq`).

Two consequences follow, and both hold at EVERY size, so both are available at
`(6,3)` where the stratum is still open.

## 1. The vanishing branch is the hinge's conclusion

A wedge vanishes exactly at a parallel pair.  So the chart's hypothesis `0 < P`
is precisely primitivity at the pair `(x,d)`, and the branch it excludes does
not have to be refuted at all — it HANDS OVER a parallel pair
(`Gtz.hasParallelPair_of_axisWedge_eq_zero`).  In the two-zero analysis at
`(6,3)`, an outside atom with vanishing plane part is a hinge WITNESS, not a
case.

## 2. The budget

Parseval read at a unit atom gives `Σ_c t_c⟨g_c,g_x⟩² = 1`, and the trace gives
`Σ_c t_c ℓ_c = 3`.  Subtracting:

  **`Σ_c t_c · crossNormSq g_x g_c = 2`**   (`Gtz.axisWedge_budget`)

at every design carrying a unit atom.  Every summand is a squared area, so the
budget is a distribution of total mass two over the atoms — and the axis's own
term is zero, so the OTHER atoms carry all of it.  A unit atom therefore cannot
be parallel to every other atom: some atom carries a strictly positive share
(`Gtz.exists_axisWedge_pos`).

Written in the two-zero configuration, where the two plane partners read the
axis at zero and so contribute their full leverages, the budget becomes a law on
the erased scales alone,

  `Σ_{d ∉ C} t_d·P_d = 2 − t_y·ℓ_y − t_z·ℓ_z`   (`Gtz.axisWedge_outside_budget`),

which is size-free and is the `(6,3)` replacement for the `(5,3)` collinearity
count.

## 3. The cross law, homogeneous

`Gtz.k2Plane_cross_law` was stated with `c + d = 1`, the normalisation the
`(5,3)` plane happens to satisfy because ONE erased direction absorbs everything.
At `(6,3)` the outside plane moment has rank two and the second plane reading
returns `1 − ν₂` instead of `1`.  The law does not need the normalisation
(`Gtz.k2Plane_cross_law_homog`):

  **`a·c = b·d  ⟹  (a+b)(ty·c + tz·d) = (c+d)(ty·b + tz·a)`** ,

homogeneous in `(c,d)`.  This is what carries the plane machinery of the `(5,3)`
bridge to `(6,3)` with the two erased masses left free.
-/
import Gtz.Wave.KTwoBridgePlaneReadings
import Gtz.Design.SphereExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The erased scale is the axis wedge -/

/-- **THE AXIS WEDGE IS THE SQUARED PLANE PART.**  Against a unit atom the wedge
of any atom is its leverage less the square of its axis reading — exactly the
chart's erased scale. -/
theorem axisWedge_eq_leverage_sub_pairing_sq (D : WeightedDesign m 3) {x : Fin m}
    (hunit : leverageOf (D.atom x) = 1) (d : Fin m) :
    crossNormSq (D.atom x) (D.atom d)
      = leverageOf (D.atom d) - atomPairing D d x ^ 2 := by
  rw [crossNormSq_eq_leverage_mul_sub_sq, hunit, one_mul, atomPairing,
    dotProduct_comm]

/-- **A VANISHING AXIS WEDGE IS A PARALLEL PAIR.**  The branch the chart excludes
by `0 < P` does not need refuting: it hands over the hinge's conclusion. -/
theorem hasParallelPair_of_axisWedge_eq_zero (D : WeightedDesign m 3)
    {x d : Fin m} (hne : x ≠ d)
    (hzero : crossNormSq (D.atom x) (D.atom d) = 0) :
    HasParallelPair D := by
  refine hasParallelPair_of_crossProduct_atom_eq_zero D hne ?_
  by_contra hne0
  have hlt := (crossProduct_ne_zero_iff_sq_lt_mul (D.atom x) (D.atom d)).mp hne0
  have hw : crossNormSq (D.atom x) (D.atom d)
      = leverageOf (D.atom x) * leverageOf (D.atom d)
        - (D.atom x ⬝ᵥ D.atom d) ^ 2 :=
    crossNormSq_eq_leverage_mul_sub_sq _ _
  rw [hzero] at hw
  rw [dotProduct_self_eq_leverage, dotProduct_self_eq_leverage] at hlt
  linarith [hw, hlt]

/-! ## 2. The budget -/

/-- **THE AXIS WEDGE BUDGET.**  At every design carrying a unit atom, the
weighted wedges of that atom against the whole design total exactly two.  The
trace of Parseval less its reading at the axis. -/
theorem axisWedge_budget (D : WeightedDesign m 3) {x : Fin m}
    (hunit : leverageOf (D.atom x) = 1) :
    ∑ c, D.weight c * crossNormSq (D.atom x) (D.atom c) = 2 := by
  have hlev : ∑ c, D.weight c * leverageOf (D.atom c) = 3 := sum_weighted_leverage D
  have hax : ∑ c, D.weight c * atomPairing D c x ^ 2 = 1 :=
    k2Axis_reading_total D hunit
  have hsplit : ∑ c, D.weight c * crossNormSq (D.atom x) (D.atom c)
      = (∑ c, D.weight c * leverageOf (D.atom c))
        - ∑ c, D.weight c * atomPairing D c x ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [axisWedge_eq_leverage_sub_pairing_sq D hunit c]; ring
  rw [hsplit, hlev, hax]; norm_num

/-- Each summand of the budget is a squared area, so none is negative. -/
theorem axisWedge_term_nonneg (D : WeightedDesign m 3) (x c : Fin m) :
    0 ≤ D.weight c * crossNormSq (D.atom x) (D.atom c) := by
  refine mul_nonneg (D.weight_pos c).le ?_
  rw [crossNormSq]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- **A UNIT ATOM IS NOT PARALLEL TO EVERYTHING.**  The budget is two and every
term is nonnegative, so some atom carries a positive share. -/
theorem exists_axisWedge_pos (D : WeightedDesign m 3) {x : Fin m}
    (hunit : leverageOf (D.atom x) = 1) :
    ∃ c, 0 < crossNormSq (D.atom x) (D.atom c) := by
  by_contra hcon
  push_neg at hcon
  have hle : ∑ c, D.weight c * crossNormSq (D.atom x) (D.atom c) ≤ 0 := by
    refine Finset.sum_nonpos fun c _ => ?_
    exact mul_nonpos_of_nonneg_of_nonpos (D.weight_pos c).le (hcon c)
  rw [axisWedge_budget D hunit] at hle
  norm_num at hle

/-! ## 3. The budget in the two-zero configuration -/

/-- **THE OUTSIDE ERASED SCALES TOTAL THE BUDGET LESS THE PLANE LEVERAGES.**  In
a two-zero configuration the two plane partners read the axis at zero, so their
wedges are their full leverages and the budget becomes a law on the erased
scales of the outside atoms alone.  Size-free, so it is the `(6,3)` replacement
for the `(5,3)` collinearity count. -/
theorem axisWedge_outside_budget (D : WeightedDesign 5 3)
    (hunit : leverageOf (D.atom 0) = 1)
    (hy : atomPairing D 0 1 = 0) (hz : atomPairing D 0 2 = 0) :
    D.weight 3 * crossNormSq (D.atom 0) (D.atom 3)
        + D.weight 4 * crossNormSq (D.atom 0) (D.atom 4)
      = 2 - D.weight 1 * leverageOf (D.atom 1)
          - D.weight 2 * leverageOf (D.atom 2) := by
  have hb := axisWedge_budget D hunit
  rw [Fin.sum_univ_five] at hb
  have e0 : crossNormSq (D.atom 0) (D.atom 0) = 0 := by
    rw [axisWedge_eq_leverage_sub_pairing_sq D hunit 0, atomPairing, hunit]
    rw [dotProduct_self_eq_leverage, hunit]; ring
  have e1 : crossNormSq (D.atom 0) (D.atom 1) = leverageOf (D.atom 1) := by
    rw [axisWedge_eq_leverage_sub_pairing_sq D hunit 1, atomPairing,
      dotProduct_comm, ← atomPairing, hy]; ring
  have e2 : crossNormSq (D.atom 0) (D.atom 2) = leverageOf (D.atom 2) := by
    rw [axisWedge_eq_leverage_sub_pairing_sq D hunit 2, atomPairing,
      dotProduct_comm, ← atomPairing, hz]; ring
  rw [e0, e1, e2] at hb
  linarith [hb]

/-! ## 4. The cross law without the normalisation -/

/-- **THE CROSS LAW IS HOMOGENEOUS.**  The `(5,3)` plane satisfies `c + d = 1`
because one erased direction absorbs everything; at `(6,3)` the outside plane
moment has rank two and the second plane reading returns less than one.  The law
never needed the normalisation. -/
theorem k2Plane_cross_law_homog (a b c d ty tz : ℝ) (hac : a*c = b*d) :
    (a + b)*(ty*c + tz*d) = (c + d)*(ty*b + tz*a) := by
  linear_combination (ty - tz)*hac

end Gtz

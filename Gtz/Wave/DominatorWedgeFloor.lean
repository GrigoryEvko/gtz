/-
# The wedge floor of a weak dominator, and the misalignment it forces

The bracket floor of a weak dominator (`Gtz.dominator_bracket_floor`) says a
dominating triple carries squared bracket at least one.  Cauchy–Schwarz at the
cross product turns that floor into a floor on the INSIDE WEDGES, which is the
direction the rigidity fight needs: the hinge wants a wedge driven to zero, and
a dominator forbids it on its own three pairs, quantitatively.

* `Gtz.dominator_inside_wedge_floor` — at a weak dominator,
  `w_{xy}·ℓ_z ≥ 1` for each of the three inside pairs;
* `Gtz.dominator_inside_wedge_ge_weight` — hence `w_{xy} ≥ t_z`, because the
  projection diagonal `t_zℓ_z` never exceeds one;
* `Gtz.dominator_inside_pair_mass_floor` — in the pair-mass currency of
  `Gtz.PairBracketMass`, `t_xt_y·w_{xy} ≥ t_xt_yt_z`: the dominator's own
  share of the bracket budget, localized to one pair;
* `Gtz.dominator_no_inside_parallel` — no inside pair of a weak dominator is
  parallel, with the margin `t_z` rather than merely a rank count.

Then the aggregation.  The corank-one endgame prices each inside pair from
ABOVE by the misalignment of two null lines,
`w_{pq}·β_q² ≤ ℓ_p·R²·(1 − ⟨w,w'⟩²)`.  Against the wedge floor this becomes a
bound on the null readings alone, and the readings of a dominator are a UNIT
vector, so summing the three instances cannot be satisfied by a small
misalignment: `Gtz.misalignment_floor_of_pairBounds` returns

  `1 ≤ R²·(1 − ⟨w,w'⟩²)·(ℓ_xℓ_y + ℓ_xℓ_z + ℓ_yℓ_z)` ,

an INTRINSIC lower bound on the misalignment of the two null lines in terms of
the second elementary symmetric function of the inside leverages.  The
aggregation is per-pair throughout, and the only field-sensitive ingredient is
the nonnegativity of a wedge — `Gtz.pair_mass_nonneg`, the named realness
carrier of this lane.
-/
import Gtz.Wave.PairMassRowLaw
import Gtz.Wave.KOneBracketLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

/-! ## 1. The wedge floor -/

/-- The squared bracket never exceeds the wedge of a pair times the leverage
of the third slot — Cauchy–Schwarz at the cross product. -/
theorem tripleBracket_sq_le_wedge_mul_leverage (u v w : Fin 3 → ℝ) :
    tripleBracket u v w ^ 2
      ≤ (leverageOf u * leverageOf v - (u ⬝ᵥ v) ^ 2) * leverageOf w := by
  have hcross : crossProduct u v ⬝ᵥ crossProduct u v
      = leverageOf u * leverageOf v - (u ⬝ᵥ v) ^ 2 := by
    rw [cross_dot_cross, ← leverageOf_eq_dotProduct, ← leverageOf_eq_dotProduct,
      dotProduct_comm v u]
    ring
  have hcs := dotProduct_sq_le_mul (crossProduct u v) w
  rw [hcross, ← leverageOf_eq_dotProduct] at hcs
  rw [tripleBracket_eq_cross_dot]
  exact hcs

/-- **THE WEDGE FLOOR OF A WEAK DOMINATOR.**  Each inside pair of a weakly
dominating triple has wedge at least the reciprocal of the third leverage:

  `w_{xy}·ℓ_z ≥ 1` .

The bracket floor says the dominator's squared bracket is at least one, and
Cauchy–Schwarz caps that bracket by the wedge times the leverage. -/
theorem dominator_inside_wedge_floor (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6))) :
    1 ≤ (leverageOf (D.atom x) * leverageOf (D.atom y)
      - atomPairing D x y ^ 2) * leverageOf (D.atom z) := by
  have hfloor := dominator_bracket_floor D hxy hxz hyz hdominates
  have hcs := tripleBracket_sq_le_wedge_mul_leverage (D.atom x) (D.atom y) (D.atom z)
  rw [← atomBracket, ← atomPairing] at hcs
  linarith [hfloor, hcs]

/-- **THE WEDGE FLOOR IN WEIGHTS.**  Each inside pair of a weak dominator has
wedge at least the third member's weight: the projection diagonal `t_zℓ_z`
never exceeds one, so `1/ℓ_z ≥ t_z`. -/
theorem dominator_inside_wedge_ge_weight (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6))) :
    D.weight z ≤ leverageOf (D.atom x) * leverageOf (D.atom y)
      - atomPairing D x y ^ 2 := by
  have hfloor := dominator_inside_wedge_floor D hxy hxz hyz hdominates
  have hdiag := parseval_weight_leverage_le_one D z
  rw [← leverageOf_eq_dotProduct] at hdiag
  have hlevpos : 0 < leverageOf (D.atom z) := by
    by_contra hcon
    push Not at hcon
    have hlevnn : 0 ≤ leverageOf (D.atom z) := by
      rw [leverageOf]; positivity
    have hzero : leverageOf (D.atom z) = 0 := le_antisymm hcon hlevnn
    rw [hzero, mul_zero] at hfloor
    linarith
  -- the wedge is nonnegative, so the floor divides
  have hwnn : 0 ≤ leverageOf (D.atom x) * leverageOf (D.atom y)
      - atomPairing D x y ^ 2 := by
    have hcross : crossProduct (D.atom x) (D.atom y)
        ⬝ᵥ crossProduct (D.atom x) (D.atom y)
        = leverageOf (D.atom x) * leverageOf (D.atom y)
          - atomPairing D x y ^ 2 := by
      rw [cross_dot_cross, ← leverageOf_eq_dotProduct, ← leverageOf_eq_dotProduct,
        atomPairing, dotProduct_comm (D.atom y) (D.atom x)]
      ring
    rw [← hcross]
    exact dotProduct_self_nonneg _
  nlinarith [hfloor, hdiag, hlevpos, hwnn, (D.weight_pos z).le]

/-- **THE PAIR-MASS FLOOR OF A DOMINATOR.**  In the currency of the pair
bracket mass, an inside pair of a weak dominator carries at least the product
of all three member weights — the dominator's own localized share of the
design's unit bracket budget. -/
theorem dominator_inside_pair_mass_floor (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6))) :
    D.weight x * (D.weight y * D.weight z)
      ≤ D.weight x * (D.weight y
        * (leverageOf (D.atom x) * leverageOf (D.atom y)
          - atomPairing D x y ^ 2)) := by
  have hw := dominator_inside_wedge_ge_weight D hxy hxz hyz hdominates
  have hx := (D.weight_pos x).le
  have hy := (D.weight_pos y).le
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hy) hx

/-- **NO INSIDE PAIR OF A DOMINATOR IS PARALLEL**, with the margin `t_z`.  A
parallel pair has vanishing wedge, and the wedge floor forbids it. -/
theorem dominator_no_inside_parallel (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    (ratio : ℝ) : D.atom y ≠ ratio • D.atom x := by
  intro hpar
  have hw := dominator_inside_wedge_ge_weight D hxy hxz hyz hdominates
  have hzero : leverageOf (D.atom x) * leverageOf (D.atom y)
      - atomPairing D x y ^ 2 = 0 := by
    rw [leverageOf_eq_dotProduct, leverageOf_eq_dotProduct, atomPairing, hpar]
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  rw [hzero] at hw
  exact absurd hw (not_le.mpr (D.weight_pos z))

/-! ## 2. The misalignment floor -/

/-- **THE MISALIGNMENT FLOOR.**  Suppose each inside pair of a weak dominator
is priced from above by the misalignment of two null lines,

  `w_{pq}·β_q² ≤ ℓ_p·radius`   (`radius = R²·(1 − ⟨w,w'⟩²)`),

and the null readings of the dominator form a unit vector, `Σβ² = 1`.  Then

  `1 ≤ radius·(ℓ_xℓ_y + ℓ_xℓ_z + ℓ_yℓ_z)` .

The wedge floor converts each per-pair bound into a bound on a single squared
reading, and the readings cannot all be small because they total one.  So the
two null lines are misaligned by an INTRINSIC amount, set by the second
elementary symmetric function of the inside leverages.  Per-pair throughout;
the only field-sensitive ingredient is the nonnegativity of a wedge. -/
theorem misalignment_floor_of_pairBounds (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    {bx by' bz radius : ℝ}
    (hunit : bx ^ 2 + by' ^ 2 + bz ^ 2 = 1)
    (hboundX : (leverageOf (D.atom x) * leverageOf (D.atom y)
        - atomPairing D x y ^ 2) * bx ^ 2 ≤ leverageOf (D.atom y) * radius)
    (hboundY : (leverageOf (D.atom y) * leverageOf (D.atom z)
        - atomPairing D y z ^ 2) * by' ^ 2 ≤ leverageOf (D.atom z) * radius)
    (hboundZ : (leverageOf (D.atom x) * leverageOf (D.atom z)
        - atomPairing D x z ^ 2) * bz ^ 2 ≤ leverageOf (D.atom x) * radius) :
    1 ≤ radius * (leverageOf (D.atom x) * leverageOf (D.atom y)
      + leverageOf (D.atom x) * leverageOf (D.atom z)
      + leverageOf (D.atom y) * leverageOf (D.atom z)) := by
  -- the three wedge floors, one per inside pair, each against the third leverage
  have hfZ : 1 ≤ (leverageOf (D.atom x) * leverageOf (D.atom y)
      - atomPairing D x y ^ 2) * leverageOf (D.atom z) :=
    dominator_inside_wedge_floor D hxy hxz hyz hdominates
  have hfX : 1 ≤ (leverageOf (D.atom y) * leverageOf (D.atom z)
      - atomPairing D y z ^ 2) * leverageOf (D.atom x) := by
    have hperm : Dominates D ({y, z, x} : Finset (Fin 6)) := by
      have hset : ({y, z, x} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) := by
        ext w; simp [or_comm, or_assoc, or_left_comm]
      rw [hset]; exact hdominates
    exact dominator_inside_wedge_floor D hyz (Ne.symm hxy) (Ne.symm hxz) hperm
  have hfY : 1 ≤ (leverageOf (D.atom x) * leverageOf (D.atom z)
      - atomPairing D x z ^ 2) * leverageOf (D.atom y) := by
    have hperm : Dominates D ({x, z, y} : Finset (Fin 6)) := by
      have hset : ({x, z, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) := by
        ext w; simp [or_comm, or_assoc, or_left_comm]
      rw [hset]; exact hdominates
    exact dominator_inside_wedge_floor D hxz hxy (Ne.symm hyz) hperm
  have hsqX : 0 ≤ bx ^ 2 := sq_nonneg bx
  have hsqY : 0 ≤ by' ^ 2 := sq_nonneg by'
  have hsqZ : 0 ≤ bz ^ 2 := sq_nonneg bz
  have hlx : 0 ≤ leverageOf (D.atom x) := by rw [leverageOf]; positivity
  have hly : 0 ≤ leverageOf (D.atom y) := by rw [leverageOf]; positivity
  have hlz : 0 ≤ leverageOf (D.atom z) := by rw [leverageOf]; positivity
  -- each squared reading is capped by the radius times the OTHER two leverages
  have hcapX : bx ^ 2 ≤ leverageOf (D.atom y) * leverageOf (D.atom z) * radius := by
    nlinarith [mul_le_mul_of_nonneg_left hboundX hlz,
      mul_le_mul_of_nonneg_left hfZ hsqX]
  have hcapY : by' ^ 2 ≤ leverageOf (D.atom z) * leverageOf (D.atom x) * radius := by
    nlinarith [mul_le_mul_of_nonneg_left hboundY hlx,
      mul_le_mul_of_nonneg_left hfX hsqY]
  have hcapZ : bz ^ 2 ≤ leverageOf (D.atom x) * leverageOf (D.atom y) * radius := by
    nlinarith [mul_le_mul_of_nonneg_left hboundZ hly,
      mul_le_mul_of_nonneg_left hfY hsqZ]
  nlinarith [hunit, hcapX, hcapY, hcapZ]

end Gtz

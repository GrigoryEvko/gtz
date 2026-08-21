/-
# The leverage-excess law of the two-zero stratum

In the two-zero stratum the reading vector of a weak dominator has two zeros,
so one inside atom IS the unit null vector and the other two are orthogonal to
it.  That collapses the dominator's Gram to a block form and its bracket to a
single wedge:

  `[xyz]² = ℓ_yℓ_z − ⟨g_y,g_z⟩² = w_{yz}`   (`Gtz.axisTriple_bracket_sq`)

— the squared bracket of the triple IS the wedge of the pair that avoids the
axis.  Feeding that into the SHARPENED bracket floor
(`Gtz.dominator_bracket_floor_sharp`, which keeps the trace term the plain
floor discards) gives the stratum's own inequality:

  **`⟨g_y,g_z⟩² ≤ (ℓ_y − 1)·(ℓ_z − 1)`**   (`Gtz.axisTriple_pairing_sq_le`)

The two non-axis atoms may pair only as far as their LEVERAGE EXCESSES allow.
Both excesses are nonnegative by the landed leverage ladder, so the bound is
never vacuous, and it degenerates exactly when one of them reaches the floor
`ℓ = 1` — which is where the atom would itself become the axis.

Two consequences.  `Gtz.axisTriple_orthogonal_of_leverage_one`: if either
non-axis atom sits at leverage one, the two are ORTHOGONAL — no freedom at
all.  `Gtz.axisTriple_leverage_gt_one_of_pairing`: conversely, a nonzero
pairing forces BOTH leverages strictly above one, quantitatively.

The whole derivation is field-blind and consumes only the sharpened floor and
the orthogonality of the axis; the realness of this lane stays at
`Gtz.pair_mass_nonneg` and `Gtz.bracket_threeCycle_nonneg`.
-/
import Gtz.Wave.DominatorLeverageCap
import Gtz.Wave.CorankOneGramMirror

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

/-! ## 1. The bracket collapses to a wedge -/

/-- **THE AXIS TRIPLE'S BRACKET IS THE OPPOSITE WEDGE.**  When one atom of a
triple has unit leverage and is orthogonal to the other two, the squared
bracket is exactly the wedge of the remaining pair. -/
theorem axisTriple_bracket_sq (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hunit : leverageOf (D.atom x) = 1)
    (hxy : atomPairing D x y = 0) (hxz : atomPairing D x z = 0) :
    atomBracket D x y z ^ 2
      = leverageOf (D.atom y) * leverageOf (D.atom z) - atomPairing D y z ^ 2 := by
  rw [atomBracket, tripleBracket_sq_gram]
  rw [atomPairing] at hxy hxz
  have hzx : D.atom z ⬝ᵥ D.atom x = 0 := by
    rw [dotProduct_comm]; exact hxz
  rw [atomPairing, hunit, hxy, hzx]
  ring

/-! ## 2. The leverage-excess bound -/

/-- **THE LEVERAGE-EXCESS LAW OF THE TWO-ZERO STRATUM.**  At a weak dominator
whose axis atom has unit leverage and is orthogonal to its two partners, the
partners pair only as far as their leverage excesses permit:

  `⟨g_y,g_z⟩² ≤ (ℓ_y − 1)·(ℓ_z − 1)` .

The sharpened bracket floor, read through the collapse of the bracket to the
opposite wedge. -/
theorem axisTriple_pairing_sq_le (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    (hunit : leverageOf (D.atom x) = 1)
    (hpxy : atomPairing D x y = 0) (hpxz : atomPairing D x z = 0) :
    atomPairing D y z ^ 2
      ≤ (leverageOf (D.atom y) - 1) * (leverageOf (D.atom z) - 1) := by
  have hfloor := dominator_bracket_floor_sharp D hxy hxz hyz hdominates
  rw [axisTriple_bracket_sq D hunit hpxy hpxz, hunit] at hfloor
  nlinarith [hfloor]

/-- **A PARTNER AT THE LEVERAGE FLOOR FORCES ORTHOGONALITY.**  If either
non-axis atom sits at leverage one, the excess vanishes and the two partners
are orthogonal — the bound leaves them no freedom. -/
theorem axisTriple_orthogonal_of_leverage_one (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    (hunit : leverageOf (D.atom x) = 1)
    (hpxy : atomPairing D x y = 0) (hpxz : atomPairing D x z = 0)
    (hy : leverageOf (D.atom y) = 1) :
    atomPairing D y z = 0 := by
  have hbound := axisTriple_pairing_sq_le D hxy hxz hyz hdominates hunit hpxy hpxz
  rw [hy] at hbound
  have hsq : atomPairing D y z ^ 2 ≤ 0 := by
    have : (1 : ℝ) - 1 = 0 := by ring
    rw [this, zero_mul] at hbound
    exact hbound
  have := sq_nonneg (atomPairing D y z)
  have hzero : atomPairing D y z ^ 2 = 0 := le_antisymm hsq this
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero

/-- **A NONZERO PAIRING FORCES BOTH EXCESSES POSITIVE.**  Contrapositive of
the bound: partners that pair at all must both sit strictly above the leverage
floor, by at least the pairing squared over the other excess. -/
theorem axisTriple_leverage_gt_one_of_pairing (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    (hunit : leverageOf (D.atom x) = 1)
    (hpxy : atomPairing D x y = 0) (hpxz : atomPairing D x z = 0)
    (hpair : atomPairing D y z ≠ 0) :
    1 < leverageOf (D.atom y) ∧ 1 < leverageOf (D.atom z) := by
  have hbound := axisTriple_pairing_sq_le D hxy hxz hyz hdominates hunit hpxy hpxz
  have hpos : 0 < atomPairing D y z ^ 2 := by positivity
  -- the landed leverage ladder floors both partners at one
  have hly : 1 ≤ leverageOf (D.atom y) := by
    have hperm : Dominates D ({y, x, z} : Finset (Fin 6)) := by
      have hset : ({y, x, z} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) := by
        ext w; simp [or_comm, or_assoc, or_left_comm]
      rw [hset]; exact hdominates
    exact one_le_leverage_of_mem_dominating_triple D (Ne.symm hxy) hyz hxz hperm
  have hlz : 1 ≤ leverageOf (D.atom z) := by
    have hperm : Dominates D ({z, x, y} : Finset (Fin 6)) := by
      have hset : ({z, x, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) := by
        ext w; simp [or_comm, or_assoc, or_left_comm]
      rw [hset]; exact hdominates
    exact one_le_leverage_of_mem_dominating_triple D (Ne.symm hxz) (Ne.symm hyz) hxy hperm
  constructor
  · by_contra hcon
    push Not at hcon
    have : leverageOf (D.atom y) = 1 := le_antisymm hcon hly
    rw [this] at hbound
    nlinarith [hbound, hpos]
  · by_contra hcon
    push Not at hcon
    have : leverageOf (D.atom z) = 1 := le_antisymm hcon hlz
    rw [this] at hbound
    nlinarith [hbound, hpos]

end Gtz

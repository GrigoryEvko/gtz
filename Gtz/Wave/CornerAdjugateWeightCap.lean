/-
# The corner's pair areas, and the weight cap they carry

`Gtz.design_adjugate_probe_law` reads Parseval at the adjugate probe of a
triple.  At a corank-two corner the landed rank-one Gram
(`Gtz.insideGram_of_rankOneGap`) collapses every cross-product pairing of the
inside triple into leverage data, and the probe law becomes a cap on the inside
WEIGHTS.  Nothing here needs a vanishing axis reading, so every statement holds
on the whole corner stratum — the two `Z1` cells and BOTH horns alike.

## The pair area of an inside pair

`Gtz.corner_inside_pairArea_eq`: the squared area of two inside atoms is

  `w_ef = l_e + l_f - 1` ,

and by the landed trace identity that is `2 + lam - l_g` for the third inside
atom `g`.  The corner's three pair areas are therefore an affine image of its
three leverages, with no pairing left over.

## The weight cap

Feeding this into the diagonal instance of the probe law
(`Gtz.design_pairArea_ge_weight_mul_bracket_sq`, whose bracket square is the
landed `1 + lam`) gives, at EVERY inside atom of EVERY corner,

  **`l_g + (1 + lam) * t_g  <=  2 + lam`**    (`Gtz.corner_leverage_weight_cap`).

The landed `Gtz.parseval_weight_leverage_le_one` reads `t*l <= 1`, hence
`l <= 1/t`, which is vacuous as the weight goes to zero.  The cap above stays
finite there: no inside atom of a corner can carry leverage past `2 + lam`, and
each unit of weight it carries costs it `1 + lam` of leverage.

## The off-diagonal cap

The full two-variable instance keeps the cross term.  The corner collapses the
mixed cross-product pairing to a single pairing
(`Gtz.corner_crossPair_collapse`), and the discriminant of the resulting form is

  **`(2 + lam - l_y - (1+lam)*t_y) * (2 + lam - l_z - (1+lam)*t_z) >= (g_y.g_z)^2`**

(`Gtz.corner_offDiagonal_weight_cap`).  Both factors are exactly the slacks of
the diagonal cap, so the corner pays for its inside pairing out of the two
weight caps at once.
-/
import Gtz.Wave.CornerGramWeightLaw
import Gtz.Wave.CorankTwoNonplanarSystem

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The pair area of two inside atoms -/

/-- **THE INSIDE PAIR AREA.**  The squared area of two inside atoms of a corner
is their leverage total less one.  The rank-one Gram cancels the pairing
square against the leverage product exactly. -/
theorem corner_inside_pairArea_eq (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {e f : Fin m} (he : e ∈ C) (hf : f ∈ C) (hef : e ≠ f) :
    bracketNormal (D.atom e) (D.atom f) ⬝ᵥ bracketNormal (D.atom e) (D.atom f)
      = D.atom e ⬝ᵥ D.atom e + D.atom f ⬝ᵥ D.atom f - 1 := by
  -- the landed vanishing pair minor turns the area into a leverage total
  have hminor := corner_pairMinor_eq_zero D C hcard hlam hunit hgap he hf hef
  rw [pairMinor, heavyExcess, heavyExcess, atomPairing, leverageOf_eq_dotProduct,
    leverageOf_eq_dotProduct] at hminor
  rw [bracketNormal_dotProduct_bracketNormal,
    dotProduct_comm (D.atom f) (D.atom e)]
  linear_combination hminor

/-- **THE PAIR AREA IN THE THIRD LEVERAGE.**  With the landed trace identity the
inside pair area is `2 + lam` less the leverage of the atom left out. -/
theorem corner_inside_pairArea_eq_third (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u) :
    bracketNormal (D.atom y) (D.atom z) ⬝ᵥ bracketNormal (D.atom y) (D.atom z)
      = 2 + lam - D.atom x ⬝ᵥ D.atom x := by
  have harea := corner_inside_pairArea_eq D _ (card_triple_eq hxy hxz hyz) hlam hunit hgap
    (by simp : y ∈ ({x, y, z} : Finset (Fin m)))
    (by simp : z ∈ ({x, y, z} : Finset (Fin m))) hyz
  have htr := corner_trace_identity D hxy hxz hyz hunit hgap
  rw [harea]; linarith [htr]

/-! ## 2. The diagonal weight cap -/

/-- **THE CORNER LEVERAGE-WEIGHT CAP.**  At every inside atom of every corner
the leverage and the weight trade off at the exact rate `1 + lam`:

  `l_x + (1 + lam) * t_x <= 2 + lam` .

No axis reading is assumed to vanish, so this holds on the whole corner
stratum.  Unlike the landed `t*l <= 1`, it does not degenerate as the weight
goes to zero. -/
theorem corner_leverage_weight_cap (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u) :
    D.atom x ⬝ᵥ D.atom x + (1 + lam) * D.weight x ≤ 2 + lam := by
  have hfloor := design_pairArea_ge_weight_mul_bracket_sq D hxy hxz hyz
  have hbr := corner_atomBracket_sq D hxy hxz hyz hlam hunit hgap
  have harea := corner_inside_pairArea_eq_third D hxy hxz hyz hlam hunit hgap
  rw [hbr] at hfloor
  rw [harea] at hfloor
  linarith [hfloor]

/-! ## 3. The mixed cross-product pairing -/

/-- **THE MIXED CROSS PAIRING COLLAPSES.**  At a corner the Binet-Cauchy value
of two cross products sharing one inside atom is minus the pairing of the two
atoms they do not share.  The rank-one Gram makes the two terms cancel down to
a single pairing. -/
theorem corner_crossPair_collapse (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (D.atom z ⬝ᵥ D.atom x) * (D.atom x ⬝ᵥ D.atom y)
        - (D.atom z ⬝ᵥ D.atom y) * (D.atom x ⬝ᵥ D.atom x)
      = -(D.atom y ⬝ᵥ D.atom z) := by
  have hzx := insideGram_offDiag_of_rankOneGap D C hcard hlam hunit hgap hz hx
    (Ne.symm hxz)
  have hxy' := insideGram_offDiag_of_rankOneGap D C hcard hlam hunit hgap hx hy hxy
  have hyz' := insideGram_offDiag_of_rankOneGap D C hcard hlam hunit hgap hy hz hyz
  have hzy : D.atom z ⬝ᵥ D.atom y = D.atom y ⬝ᵥ D.atom z := dotProduct_comm _ _
  have hlx := insideGram_self_of_rankOneGap D C hcard hlam hunit hgap hx
  have hpos : (0 : ℝ) < 1 + lam := by linarith
  have hne : ((1 + lam) ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (ne_of_gt hpos)
  have hkey : ((1 + lam) ^ 2 : ℝ)
        * ((D.atom z ⬝ᵥ D.atom x) * (D.atom x ⬝ᵥ D.atom y)
          - (D.atom y ⬝ᵥ D.atom z) * (D.atom x ⬝ᵥ D.atom x))
      = ((1 + lam) ^ 2 : ℝ) * (-(D.atom y ⬝ᵥ D.atom z)) := by
    linear_combination (1 + lam) * (D.atom x ⬝ᵥ D.atom y) * hzx
      + lam * ((D.atom z ⬝ᵥ u) * (D.atom x ⬝ᵥ u)) * hxy'
      - (1 + lam) * ((D.atom x ⬝ᵥ D.atom x) - 1) * hyz'
      - lam * ((D.atom y ⬝ᵥ u) * (D.atom z ⬝ᵥ u)) * hlx
  rw [hzy]
  exact mul_left_cancel₀ hne hkey

/-! ## 4. The off-diagonal weight cap -/

/-- **THE OFF-DIAGONAL CORNER CAP.**  The two diagonal slacks of the corner
weight cap multiply to at least the squared pairing of the two atoms they
belong to.  The corner pays for its inside pairing out of both weight caps at
once, and the two caps can never both be tight unless that pairing vanishes. -/
theorem corner_offDiagonal_weight_cap (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u) :
    (D.atom y ⬝ᵥ D.atom z) ^ 2
      ≤ (2 + lam - D.atom y ⬝ᵥ D.atom y - (1 + lam) * D.weight y)
        * (2 + lam - D.atom z ⬝ᵥ D.atom z - (1 + lam) * D.weight z) := by
  have hcard := card_triple_eq hxy hxz hyz
  have hxmem : x ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hymem : y ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hzmem : z ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hbr := corner_atomBracket_sq D hxy hxz hyz hlam hunit hgap
  -- the two diagonal cross squares, in the third leverage
  have hareaZX : bracketNormal (D.atom z) (D.atom x) ⬝ᵥ bracketNormal (D.atom z) (D.atom x)
      = 2 + lam - D.atom y ⬝ᵥ D.atom y := by
    have h := corner_inside_pairArea_eq D _ hcard hlam hunit hgap hzmem hxmem (Ne.symm hxz)
    have htr := corner_trace_identity D hxy hxz hyz hunit hgap
    rw [h]; linarith [htr]
  have hareaXY : bracketNormal (D.atom x) (D.atom y) ⬝ᵥ bracketNormal (D.atom x) (D.atom y)
      = 2 + lam - D.atom z ⬝ᵥ D.atom z := by
    have h := corner_inside_pairArea_eq D _ hcard hlam hunit hgap hxmem hymem hxy
    have htr := corner_trace_identity D hxy hxz hyz hunit hgap
    rw [h]; linarith [htr]
  have hcross := corner_crossPair_collapse D _ hcard hlam hunit hgap hxmem hymem hzmem
    hxy hxz hyz
  -- the quadratic form, from the adjugate probe law at `w0 = 0`
  have hQ : ∀ w1 w2 : ℝ,
      0 ≤ (2 + lam - D.atom y ⬝ᵥ D.atom y - (1 + lam) * D.weight y) * w1 ^ 2
        - 2 * (D.atom y ⬝ᵥ D.atom z) * w1 * w2
        + (2 + lam - D.atom z ⬝ᵥ D.atom z - (1 + lam) * D.weight z) * w2 ^ 2 := by
    intro w1 w2
    have h := design_adjugate_probe_law D hxy hxz hyz 0 w1 w2
    rw [hbr] at h
    have hsq : adjugateProbe (D.atom x) (D.atom y) (D.atom z) 0 w1 w2
          ⬝ᵥ adjugateProbe (D.atom x) (D.atom y) (D.atom z) 0 w1 w2
        = w1 ^ 2 * (bracketNormal (D.atom z) (D.atom x)
              ⬝ᵥ bracketNormal (D.atom z) (D.atom x))
          + 2 * w1 * w2 * (bracketNormal (D.atom z) (D.atom x)
              ⬝ᵥ bracketNormal (D.atom x) (D.atom y))
          + w2 ^ 2 * (bracketNormal (D.atom x) (D.atom y)
              ⬝ᵥ bracketNormal (D.atom x) (D.atom y)) := by
      simp only [adjugateProbe, dotProduct, Fin.sum_univ_three]
      ring
    rw [hsq, hareaZX, hareaXY, bracketNormal_dotProduct_bracketNormal, hcross] at h
    nlinarith [h]
  have hdisc := discriminant_nonneg_of_binaryForm_nonneg hQ
  linarith [hdisc]

/-! ## 5. The simplex form -/

/-- **THE CORNER SIMPLEX LAW.**  The landed vanishing pair minor turns the
squared pairing on the left of the off-diagonal cap into the product of the two
leverage excesses.  That product cancels, and one factor of the corner scale
divides out, leaving a law that is LINEAR in the two excesses:

  **`e_y*(1 - t_z) + e_z*(1 - t_y)  <=  (1 + lam)*(1 - t_y)*(1 - t_z)`** ,

with `e = l - 1` the leverage excess.  Reading it against the two positive
slacks puts the corner on a simplex: each excess, measured against its own
weight complement at the corner scale, uses up a share of one budget, and the
two shares together never exceed the whole.

This holds at every pair of inside atoms of every corner.  On the `Z1` cell,
where the third excess vanishes and the other two total `lam`, it is exactly
`Gtz.corner_oneAxisZero_weight_law`. -/
theorem corner_excess_simplex (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u) :
    (D.atom y ⬝ᵥ D.atom y - 1) * (1 - D.weight z)
        + (D.atom z ⬝ᵥ D.atom z - 1) * (1 - D.weight y)
      ≤ (1 + lam) * ((1 - D.weight y) * (1 - D.weight z)) := by
  have hoff := corner_offDiagonal_weight_cap D hxy hxz hyz hlam hunit hgap
  have hminor := corner_pairMinor_eq_zero D _ (card_triple_eq hxy hxz hyz) hlam hunit hgap
    (by simp : y ∈ ({x, y, z} : Finset (Fin m)))
    (by simp : z ∈ ({x, y, z} : Finset (Fin m))) hyz
  rw [pairMinor, heavyExcess, heavyExcess, atomPairing, leverageOf_eq_dotProduct,
    leverageOf_eq_dotProduct] at hminor
  have hpos : (0 : ℝ) < 1 + lam := by linarith
  -- the squared pairing cancels and one corner scale divides out
  have hscaled : (1 + lam) * ((D.atom y ⬝ᵥ D.atom y - 1) * (1 - D.weight z)
        + (D.atom z ⬝ᵥ D.atom z - 1) * (1 - D.weight y))
      ≤ (1 + lam) * ((1 + lam) * ((1 - D.weight y) * (1 - D.weight z))) := by
    nlinarith [hoff, hminor]
  exact le_of_mul_le_mul_left hscaled hpos

end Gtz

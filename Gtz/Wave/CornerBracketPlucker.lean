import Gtz.Wave.CornerParityLedger
import Gtz.Quantitative.PlueckerRealness
import Gtz.Quantitative.SixThreeCruxSigns
import Gtz.Reduction.PolarGapDeterminant
import Gtz.Wave.CornerRefusalCensus

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The corner bracket, and the Grassmann-Pluecker bridge to the informative
refusals

`Gtz.corner_fourSet_parity_forced` shows that the parity bit of a triple carries
nothing new at a corank-two corner: the rank-one gap already forces it on the
dominator and on all nine two-inside triples.  The campaign owns a SECOND realness
carrier, and this module shows that the second one is LIVE where the first one is
spent.

## The dominator bracket is the gap scale

The three inside pair minors vanish (`Gtz.corner_inside_pairMinor_eq_zero`), the
three inside excesses sum to the gap scale (`Gtz.corner_heavyExcess_sum`), and the
excess determinant of the dominator vanishes because a rank-one form in three
dimensions is singular.  Read those three facts in
`Gtz.atomBracket_sq_eq_discriminantTie_add` and the dominator bracket collapses to
one number:

  `atomBracket x y z ² = 1 + lam`   (`Gtz.corner_atomBracket_sq`).

## The bridge

Five atoms of rank three obey the three-term relation of Grassmann and Pluecker
(`Gtz.threeTermAtomBracketRelation`).  Take the three inside atoms and two outside
ones, with an inside atom as the base:

  `[x y z]·[x p q] = [x y p]·[x z q] − [x y q]·[x z p]` .

The left factor is the dominator bracket, so squaring gives

  `(1 + lam)·[x p q]² = ([x y p][x z q] − [x y q][x z p])²`
  (`Gtz.corner_bracket_bridge`).

The left side reads `[x p q]`, a triple with ONE inside atom and two outside ones
— one of the ten informative refusals of `Gtz.isTie_iff_corner_refusals`.  The
right side reads only two-inside brackets, and every one of those the corner
already pins.  So the bridge computes an informative bracket from corner data,
exactly.

## Where the realness sits

Over the complex numbers the same three-term relation holds for the complex
brackets, but domination reads the SQUARED MODULUS `|[abc]|²` and not `[abc]²`.
The right side becomes `|A|² + |B|² − 2·Re(A·conj B)`, and the real part is only
bounded by the modulus.  The bridge degrades to the two triangle bounds, and the
exact value is lost.  In the squared-bracket form the loss is the Heron identity
of `Gtz.squaredBracketProducts_heronDegenerate`, which this module instantiates at
the corner (`Gtz.corner_heron`): over the reals the three complementary products
have a DEGENERATE Heron determinant, and over the complex numbers only a
nonnegative one.

The complex corner-tie witness on record measures the split.  Its parity pattern
obeys the two-graph axiom on all fifteen four-sets, so the first carrier is blind
to it.  Its Heron determinant on the five-sets that carry the whole dominator is
nonzero, up to 29 percent of the leading term.  The second carrier sees it.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The mass of the gap axis and the excess total -/

/-- **The dominator resolves its own axis with mass `1 + lam`.**  The squared axis
readings of the inside atoms total `1 + lam`. -/
theorem corner_axis_mass (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ∑ e ∈ C, (D.atom e ⬝ᵥ u) ^ 2 = 1 + lam := by
  have hres := resolve_of_rankOneGap D C hunit hgap
  have hread : (∑ c ∈ C, (D.atom c ⬝ᵥ u) • D.atom c) ⬝ᵥ u = 1 + lam := by
    rw [hres, smul_dotProduct, hunit, smul_eq_mul, mul_one]
  rw [← hread, sum_dotProduct]
  exact Finset.sum_congr rfl fun e _ => by rw [smul_dotProduct, smul_eq_mul, sq]

/-- **The inside excesses total the gap scale.** -/
theorem corner_heavyExcess_sum (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ∑ e ∈ C, heavyExcess D e = lam := by
  have hpos : (0 : ℝ) < 1 + lam := by linarith
  have hscaled : ∑ e ∈ C, (1 + lam) * heavyExcess D e
      = ∑ e ∈ C, lam * (D.atom e ⬝ᵥ u) ^ 2 :=
    Finset.sum_congr rfl fun e he => corner_heavyExcess_axis D C hcard hlam hunit hgap he
  rw [← Finset.mul_sum, ← Finset.mul_sum, corner_axis_mass D C hunit hgap] at hscaled
  have := mul_left_cancel₀ (ne_of_gt hpos) (hscaled.trans (by ring))
  exact this

/-- The pair minor of two distinct inside atoms is zero. -/
theorem corner_pairMinor_eq_zero (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {e f : Fin m} (he : e ∈ C) (hf : f ∈ C) (hef : e ≠ f) :
    pairMinor D e f = 0 := by
  rw [pairMinor, corner_inside_pairMinor_eq_zero D C hcard hlam hunit hgap he hf hef]
  ring

/-! ## 2. The dominator bracket -/

/-- **THE DOMINATOR BRACKET IS THE GAP SCALE.**  At a corank-two corner the
squared bracket of the three inside atoms is `1 + lam`, with no other data. -/
theorem corner_atomBracket_sq (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u) :
    atomBracket D x y z ^ 2 = 1 + lam := by
  have hcard := card_triple_eq hxy hxz hyz
  have hx : x ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hy : y ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hz : z ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hdet : discriminantTie D x y z = 0 := by
    rw [← det_subsetSum_sub_one_eq_discriminantTie D hxy hxz hyz, hgap,
      det_atomSingle_eq_zero]
  have hmXY := corner_pairMinor_eq_zero D _ hcard hlam hunit hgap hx hy hxy
  have hmXZ := corner_pairMinor_eq_zero D _ hcard hlam hunit hgap hx hz hxz
  have hmYZ := corner_pairMinor_eq_zero D _ hcard hlam hunit hgap hy hz hyz
  have hsum := corner_heavyExcess_sum D _ hcard hlam hunit hgap
  rw [sum_triple_eq hxy hxz hyz fun c => heavyExcess D c] at hsum
  rw [atomBracket_sq_eq_discriminantTie_add, hdet, hmXY, hmXZ, hmYZ]
  linarith

/-! ## 3. The bridge to an informative bracket -/

/-- **THE BRACKET BRIDGE.**  The squared bracket of a triple with ONE inside atom
and two outside atoms is computed exactly from the two-inside brackets, scaled by
the gap.  This is the first law that reads an informative refusal of a corank-two
corner off the corner data alone.

Over the complex numbers the three-term relation still holds for the complex
brackets, but domination reads squared MODULI.  The right side becomes a modulus
of a difference and the exact value is replaced by the two triangle bounds. -/
theorem corner_bracket_bridge (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (outFirst outSecond : Fin m) :
    (1 + lam) * atomBracket D x outFirst outSecond ^ 2
      = (atomBracket D x y outFirst * atomBracket D x z outSecond
          - atomBracket D x y outSecond * atomBracket D x z outFirst) ^ 2 := by
  have hrel := threeTermAtomBracketRelation D x y z outFirst outSecond
  have hbase := corner_atomBracket_sq D hxy hxz hyz hlam hunit hgap
  have hsplit : atomBracket D x y z * atomBracket D x outFirst outSecond
      = atomBracket D x y outFirst * atomBracket D x z outSecond
        - atomBracket D x y outSecond * atomBracket D x z outFirst := by
    linarith [hrel]
  have hsq := congrArg (fun t : ℝ => t ^ 2) hsplit
  simp only [mul_pow] at hsq
  rw [hbase] at hsq
  exact hsq

/-- **THE HERON INSTANCE AT A CORNER.**  The Heron degeneracy of
`Gtz.squaredBracketProducts_heronDegenerate`, read at the three inside atoms and
two outside atoms, with the dominator bracket replaced by the gap scale.  The
first product carries the informative bracket, the other two carry only
two-inside brackets.  Over the complex numbers the same three products have a
strictly positive Heron determinant off the real locus. -/
theorem corner_heron (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (outFirst outSecond : Fin m) :
    ((1 + lam) * atomBracket D x outFirst outSecond ^ 2
        + atomBracket D x y outFirst ^ 2 * atomBracket D x z outSecond ^ 2
        + atomBracket D x y outSecond ^ 2 * atomBracket D x z outFirst ^ 2) ^ 2
      = 4 * (((1 + lam) * atomBracket D x outFirst outSecond ^ 2)
            * (atomBracket D x y outFirst ^ 2 * atomBracket D x z outSecond ^ 2)
          + (atomBracket D x y outFirst ^ 2 * atomBracket D x z outSecond ^ 2)
            * (atomBracket D x y outSecond ^ 2 * atomBracket D x z outFirst ^ 2)
          + (atomBracket D x y outSecond ^ 2 * atomBracket D x z outFirst ^ 2)
            * ((1 + lam) * atomBracket D x outFirst outSecond ^ 2)) := by
  have hheron := squaredBracketProducts_heronDegenerate D x y z outFirst outSecond
  have hbase := corner_atomBracket_sq D hxy hxz hyz hlam hunit hgap
  rw [hbase] at hheron
  exact hheron

/-- **THE EXTREMAL FORM.**  The deviation of the scaled informative bracket from
the sum of the two two-inside products is EXTREMAL: its square is four times their
product.  This is the polynomial statement a corner certificate can consume, and
it is the exact place the ground field acts.  Over the complex numbers the same
three quantities give only `≤`, because the cross term is a real part and not a
modulus.  The complex corner-tie witness on record sits strictly inside the
interval the two real branches bound, at every one of the nine instances. -/
theorem corner_bracket_extremal (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (outFirst outSecond : Fin m) :
    ((1 + lam) * atomBracket D x outFirst outSecond ^ 2
        - atomBracket D x y outFirst ^ 2 * atomBracket D x z outSecond ^ 2
        - atomBracket D x y outSecond ^ 2 * atomBracket D x z outFirst ^ 2) ^ 2
      = 4 * (atomBracket D x y outFirst ^ 2 * atomBracket D x z outSecond ^ 2
          * (atomBracket D x y outSecond ^ 2 * atomBracket D x z outFirst ^ 2)) := by
  have hbridge := corner_bracket_bridge D hxy hxz hyz hlam hunit hgap outFirst outSecond
  rw [hbridge]
  ring

/-! ## 4. The two-sided form the corner can consume -/

/-- The informative bracket is capped by the two-inside brackets. -/
theorem corner_bracket_le (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (outFirst outSecond : Fin m) :
    (1 + lam) * atomBracket D x outFirst outSecond ^ 2
      ≤ 2 * (atomBracket D x y outFirst ^ 2 * atomBracket D x z outSecond ^ 2
          + atomBracket D x y outSecond ^ 2 * atomBracket D x z outFirst ^ 2) := by
  have hbridge := corner_bracket_bridge D hxy hxz hyz hlam hunit hgap outFirst outSecond
  rw [hbridge]
  nlinarith [sq_nonneg (atomBracket D x y outFirst * atomBracket D x z outSecond
      + atomBracket D x y outSecond * atomBracket D x z outFirst)]

end Gtz

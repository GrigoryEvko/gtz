/-
# The strong graph of a `(6,3)` design, and the elliptope reading of the trichotomy

`Gtz/Wave/BranchBStrongPair.lean` proves that a refused triple of heavy atoms
carries a STRONG pair — one whose squared pairing clears a quarter of the product
of the two leverage excesses — and its header then claims, in prose:

  "The pairs that are NOT strong span a triangle-free graph, so by Mantel at most
   nine of the fifteen pairs of a `(6,3)` design can be weak: a branch-B tie
   carries at least six strong pairs."

**That count was never a theorem.**  This module proves it, and proves it without
the branch-B hypothesis the prose assumed.

## 1. Strongness needs no admissibility

`Gtz.exists_strongPair_of_isTie_of_allHeavy` asks for one ADMISSIBLE pair inside
the triple, and `Gtz.branchB_exists_strongPair` discharges that by assuming every
pair of the design is admissible.  Neither hypothesis is needed, because an
INADMISSIBLE pair is strong outright:

  `q_ab <= 0`  says  `x_a x_b <= p_ab ^ 2`,  and  `p_ab ^ 2 <= 4 p_ab ^ 2` .

That is `Gtz.strongPair_of_pairGapMinor_nonpos`, two lines.  Splitting on the
admissibility of ONE pair therefore closes both branches, and gives

  **`Gtz.exists_strongPair_of_allHeavy_of_not_posDef`** — at an ALL-HEAVY design,
  EVERY triple that fails to dominate strictly carries a strong pair.

No tie, no branch, no admissibility.  This is the hypothesis a `Gtz.GtzWeighted`
counterexample supplies for free, so the whole count below runs on the main
statement and not only on the hinge.

## 2. The Mantel count

Strongness is symmetric, so the WEAK pairs span a graph.  Part 1 says no triple is
entirely weak, which is exactly `Gtz.CliqueFree 3`, and Mathlib's Turan bound at
`r = 2` caps a triangle-free graph on six vertices at `36 * 1 / 4 = 9` edges.  The
complement then carries at least `15 - 9 = 6`:

  **`Gtz.six_le_card_strongPairs_of_allHeavy`** — at least SIX of the fifteen pairs
  of an all-heavy `(6,3)` design with no strictly dominating triple are strong.

The same triangle-freeness feeds `R(3,3) = 6` rather than Mantel and returns a
STRONG TRIANGLE (`Gtz.exists_strong_triangle_of_allHeavy_of_no_posDef`), which is
`Gtz.branchB_exists_strong_triangle` with the branch hypothesis removed.

## 3. The elliptope dictionary

Every scalar in the trichotomy is a statement about `Gtz.normalizedPairing`
`rho_cd = p_cd / sqrt(x_c x_d)`, the coordinate in which `Gtz.RhoNormalForm`
already places domination:

| pair condition | `rho` reading |
| --- | --- |
| `pairGapMinor = 0` (an elliptope EDGE) | `rho ^ 2 = 1` |
| `AdmissiblePair` (the elliptope INTERIOR of that edge) | `rho ^ 2 < 1` |
| `StrongPair` | `1 <= 4 rho ^ 2` |

`Gtz.sq_normalizedPairing_eq` is the bridge, and the three readings are
`Gtz.pairGapMinor_eq_zero_iff_sq_normalizedPairing_eq_one`,
`Gtz.admissiblePair_iff_sq_normalizedPairing_lt_one` and
`Gtz.strongPair_iff_one_le_four_mul_sq_normalizedPairing`.

**The `K1` edge equation IS the landed `K1` minor ratio.**  On the elliptope, a
unit correlation on one edge makes the other two correlations equal in modulus.
Cleared of every square root that reads

  `x_a * q_bc - x_b * q_ac  =  x_b * p_ac ^ 2 - x_a * p_bc ^ 2`

(`Gtz.excess_mul_pairGapMinor_sub`, a `ring` identity with no hypothesis), whose
vanishing is exactly `Gtz.pairGapMinor_ratio_of_pivotRow`, and whose `rho` form is
`Gtz.excess_mul_pairGapMinor_sub_eq_sq_normalizedPairing_sub`.  So the two
vocabularies agree on the nose.

**The corner sign is `+1`, not `-1`.**  A corner has all three pair minors zero,
so all three `|rho| = 1` and the product of the three is `+-1`.  Domination forces
the elliptope bracket up, and the bracket at a `+-1` triple is `2 (prod - 1)`.  So

  **`Gtz.pairing_product_eq_excess_product_of_three_pairGapMinor_eq_zero`:**
  at a DOMINATING triple with three vanishing pair minors,
  `p_ab * p_ac * p_bc = x_a * x_b * x_c` — strictly positive — and the triple
  determinant vanishes.

In `rho` coordinates that is `rho_ab * rho_ac * rho_bc = +1`.  A reader who
negates the correlations to put the gap in standard correlation form picks up
`(-1) ^ 3` and sees `-1`; the tree's `Gtz.normalizedPairing` does not negate, and
in it the corner product is `+1`.

## 4. The trichotomy needs three excesses, not `AllHeavy`

`Gtz.tripleStratum_trichotomy` asks `Gtz.AllHeavy`, a hypothesis on all six atoms,
but its proof reads only the three excesses of the triple, and only through the
sign of the triple determinant.  `Gtz.tripleStratum_trichotomy_of_excess_pos` is
the raw-vector form: three positive excesses and `0 <= tripleGapDet` give `0`, `1`
or `3` vanishing pair minors, never `2`.  No design, no weights, no domination.

## Scope

`Gtz.GtzWeighted 6 3` is NOT proved here.  What is proved is that a counterexample
carries six strong pairs and a strong triangle, so `Gtz.gtzWeighted_sixThree_of_strongGraph`
reduces the main statement to refuting that configuration.

Every statement is FIELD-BLIND: the strong-pair engine is a determinant sign and
three squares, all of which transport to `ℂ` with the squared modulus.  By
`Gtz/Complex/ComplexTransportLedger.lean` no field-blind instrument can prove the
HINGE, so these are stratum tools.  They are NOT blocked against `Gtz.GtzWeighted 6 3`
itself, which `Gtz.complexHingeSixDesign` does not refute.

[MEASURED before proving, double precision, `scratchpad/elliptope`.  The
equivalence `StrongPair <-> |rho| >= 1/2` was checked at every admissible pair of
3000 random `(6,3)` designs with ZERO mismatches.  "Inadmissible implies strong"
was checked at 9538 inadmissible pairs with ZERO violations.  The `K1` edge
identity held to relative `1.2e-13` over 4000 designs and all ordered triples.
The corner product was `+1.000000000` at four exact rank-one Gram gaps with
`max |q| = 3.6e-15`.  The headline of part 1 — every non-strict triple of an
all-heavy design carries a strong pair — was checked at 159181 non-strict triples
with ZERO violations.]
-/
import Gtz.Wave.StrongTriangleRamsey
import Gtz.Wave.CorankStratumCollapse
import Gtz.Design.RhoNormalForm
import Gtz.Design.SignSelectedAggregate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## Part 1 — the elliptope dictionary

Three pair conditions, one coordinate.  Everything in this part is the statement
that `Gtz.normalizedPairing` squares to the pairing over the excess product. -/

/-- **THE SQUARED CORRELATION.**  With both excesses positive the normalized
pairing squares to the ratio of the squared pairing to the excess product.  This
is the only place a square root is opened, and every reading below spends it. -/
theorem sq_normalizedPairing_eq (D : WeightedDesign m 3) {first second : Fin m}
    (hfirst : 0 < heavyExcess D first) (hsecond : 0 < heavyExcess D second) :
    normalizedPairing D first second ^ 2
      = atomPairing D first second ^ 2 / (heavyExcess D first * heavyExcess D second) := by
  have hprod : (0 : ℝ) < heavyExcess D first * heavyExcess D second := mul_pos hfirst hsecond
  rw [normalizedPairing, div_pow, Real.sq_sqrt hprod.le]

/-- The pair minor in the excess vocabulary the correlation speaks. -/
theorem pairGapMinor_eq_excess_mul_sub (D : WeightedDesign m 3) (first second : Fin m) :
    pairGapMinor (D.atom first) (D.atom second)
      = heavyExcess D first * heavyExcess D second - atomPairing D first second ^ 2 := by
  rw [pairGapMinor, heavyExcess, heavyExcess, atomPairing]

/-- **A VANISHING PAIR MINOR IS A UNIT CORRELATION.**  The elliptope EDGE, in the
campaign's own vocabulary. -/
theorem pairGapMinor_eq_zero_iff_sq_normalizedPairing_eq_one (D : WeightedDesign m 3)
    {first second : Fin m} (hfirst : 0 < heavyExcess D first)
    (hsecond : 0 < heavyExcess D second) :
    pairGapMinor (D.atom first) (D.atom second) = 0
      ↔ normalizedPairing D first second ^ 2 = 1 := by
  have hprod : (0 : ℝ) < heavyExcess D first * heavyExcess D second := mul_pos hfirst hsecond
  rw [sq_normalizedPairing_eq D hfirst hsecond, div_eq_one_iff_eq (ne_of_gt hprod),
    pairGapMinor_eq_excess_mul_sub]
  constructor
  · intro hzero; linarith
  · intro heq; linarith

/-- **ADMISSIBILITY IS THE OPEN EDGE CONDITION.**  A pair is admissible exactly
when its correlation is a genuine cosine. -/
theorem admissiblePair_iff_sq_normalizedPairing_lt_one (D : WeightedDesign m 3)
    {first second : Fin m} (hfirst : 0 < heavyExcess D first)
    (hsecond : 0 < heavyExcess D second) :
    AdmissiblePair (D.atom first) (D.atom second)
      ↔ normalizedPairing D first second ^ 2 < 1 := by
  have hprod : (0 : ℝ) < heavyExcess D first * heavyExcess D second := mul_pos hfirst hsecond
  rw [AdmissiblePair, sq_normalizedPairing_eq D hfirst hsecond, div_lt_one hprod,
    pairGapMinor_eq_excess_mul_sub]
  constructor
  · intro hpos; linarith
  · intro hlt; linarith

/-- **STRONGNESS IS A HALF ON THE CORRELATION.**  `Gtz.StrongPair` says exactly
that the correlation has modulus at least one half, which is the constant the
regular tetrahedron attains. -/
theorem strongPair_iff_one_le_four_mul_sq_normalizedPairing (D : WeightedDesign m 3)
    {first second : Fin m} (hfirst : 0 < heavyExcess D first)
    (hsecond : 0 < heavyExcess D second) :
    StrongPair (D.atom first) (D.atom second)
      ↔ 1 ≤ 4 * normalizedPairing D first second ^ 2 := by
  have hprod : (0 : ℝ) < heavyExcess D first * heavyExcess D second := mul_pos hfirst hsecond
  rw [StrongPair, sq_normalizedPairing_eq D hfirst hsecond]
  rw [show (4 : ℝ) * (atomPairing D first second ^ 2
      / (heavyExcess D first * heavyExcess D second))
      = (4 * atomPairing D first second ^ 2)
        / (heavyExcess D first * heavyExcess D second) by ring,
    le_div_iff₀ hprod, one_mul]
  simp only [heavyExcess, atomPairing]

/-! ## Part 2 — the `K1` edge identity

On the elliptope a unit correlation on one edge equalizes the moduli of the other
two.  Cleared of square roots that is a `ring` identity in the six scalars, and
its vanishing is the landed `K1` minor ratio. -/

/-- **THE EDGE IDENTITY.**  Hypothesis-free, no design: the difference of the two
excess-weighted pair minors through a common atom is the difference of the two
excess-weighted squared pairings, with the slots exchanged. -/
theorem excess_mul_pairGapMinor_sub (a b c : Fin 3 → ℝ) :
    (leverageOf a - 1) * pairGapMinor b c - (leverageOf b - 1) * pairGapMinor a c
      = (leverageOf b - 1) * (a ⬝ᵥ c) ^ 2 - (leverageOf a - 1) * (b ⬝ᵥ c) ^ 2 := by
  simp only [pairGapMinor]
  ring

/-- **THE EDGE IDENTITY IN CORRELATION COORDINATES.**  The same difference is the
gap between the two squared correlations through the shared atom, scaled by the
product of the three excesses.  So the landed `K1` ratio
`Gtz.pairGapMinor_ratio_of_pivotRow` and the elliptope edge condition
`rho_ac ^ 2 = rho_bc ^ 2` are ONE equation. -/
theorem excess_mul_pairGapMinor_sub_eq_sq_normalizedPairing_sub (D : WeightedDesign m 3)
    {first second third : Fin m} (hfirst : 0 < heavyExcess D first)
    (hsecond : 0 < heavyExcess D second) (hthird : 0 < heavyExcess D third) :
    heavyExcess D first * pairGapMinor (D.atom second) (D.atom third)
        - heavyExcess D second * pairGapMinor (D.atom first) (D.atom third)
      = (normalizedPairing D first third ^ 2 - normalizedPairing D second third ^ 2)
        * (heavyExcess D first * heavyExcess D second * heavyExcess D third) := by
  rw [sq_normalizedPairing_eq D hfirst hthird, sq_normalizedPairing_eq D hsecond hthird]
  have hfirstNe : heavyExcess D first ≠ 0 := ne_of_gt hfirst
  have hsecondNe : heavyExcess D second ≠ 0 := ne_of_gt hsecond
  have hthirdNe : heavyExcess D third ≠ 0 := ne_of_gt hthird
  rw [pairGapMinor_eq_excess_mul_sub, pairGapMinor_eq_excess_mul_sub]
  field_simp
  ring

/-- **THE `K1` EDGE, AS AN EQUIVALENCE.**  The two surviving pair minors of a
triple stand in the landed ratio exactly when the two correlations through the
shared atom have equal modulus. -/
theorem pairGapMinor_ratio_iff_sq_normalizedPairing_eq (D : WeightedDesign m 3)
    {first second third : Fin m} (hfirst : 0 < heavyExcess D first)
    (hsecond : 0 < heavyExcess D second) (hthird : 0 < heavyExcess D third) :
    heavyExcess D first * pairGapMinor (D.atom second) (D.atom third)
        = heavyExcess D second * pairGapMinor (D.atom first) (D.atom third)
      ↔ normalizedPairing D first third ^ 2 = normalizedPairing D second third ^ 2 := by
  have hprod : (0 : ℝ) < heavyExcess D first * heavyExcess D second * heavyExcess D third := by
    positivity
  have hkey := excess_mul_pairGapMinor_sub_eq_sq_normalizedPairing_sub D hfirst hsecond hthird
  constructor
  · intro heq
    rw [heq, sub_self] at hkey
    have := (mul_eq_zero.mp hkey.symm).resolve_right (ne_of_gt hprod)
    linarith
  · intro heq
    rw [heq, sub_self, zero_mul] at hkey
    linarith

/-! ## Part 3 — the corner vertex, with its sign

All three pair minors vanish at a corank-two corner.  Each correlation is then
`+-1`, and DOMINATION picks the sign of the product. -/

/-- **THE CORNER PRODUCT.**  At a triple with three vanishing pair minors and a
nonnegative triple determinant the product of the three pairings equals the
product of the three excesses — in particular it is STRICTLY POSITIVE when the
excesses are — and the determinant vanishes.

In correlation coordinates this reads `rho_ab * rho_ac * rho_bc = +1`.  The sign is
`+1` in `Gtz.normalizedPairing`, which does not negate the off-diagonal; a reader
who negates to reach the standard correlation form picks up `(-1) ^ 3`. -/
private theorem cornerProduct_aux {xa xb xc u v w : ℝ}
    (hxa : 0 < xa) (hxb : 0 < xb) (hxc : 0 < xc)
    (hab : xa * xb = u ^ 2) (hac : xa * xc = v ^ 2) (hbc : xb * xc = w ^ 2)
    (hdet : 0 ≤ xa * xb * xc - xa * w ^ 2 - xb * v ^ 2 - xc * u ^ 2 + 2 * u * v * w) :
    u * v * w = xa * xb * xc := by
  have hcollapse : xa * xb * xc - xa * w ^ 2 - xb * v ^ 2 - xc * u ^ 2 + 2 * u * v * w
      = 2 * (u * v * w) - 2 * (xa * xb * xc) := by
    linear_combination xc * hab + xb * hac + xa * hbc
  have hge : xa * xb * xc ≤ u * v * w := by rw [hcollapse] at hdet; linarith
  have hsq : (u * v * w) ^ 2 = (xa * xb * xc) ^ 2 := by
    calc (u * v * w) ^ 2 = u ^ 2 * v ^ 2 * w ^ 2 := by ring
      _ = (xa * xb) * (xa * xc) * (xb * xc) := by rw [hab, hac, hbc]
      _ = (xa * xb * xc) ^ 2 := by ring
  have hfactor : (u * v * w - xa * xb * xc) * (u * v * w + xa * xb * xc) = 0 := by
    linear_combination hsq
  have hpos : 0 < xa * xb * xc := by positivity
  rcases mul_eq_zero.mp hfactor with hzero | hzero
  · linarith
  · linarith

theorem pairing_product_eq_excess_product_of_three_pairGapMinor_eq_zero {a b c : Fin 3 → ℝ}
    (hheavyA : 1 < leverageOf a) (hheavyB : 1 < leverageOf b) (hheavyC : 1 < leverageOf c)
    (hab : pairGapMinor a b = 0) (hac : pairGapMinor a c = 0) (hbc : pairGapMinor b c = 0)
    (hdet : 0 ≤ tripleGapDet a b c) :
    (a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c)
        = (leverageOf a - 1) * (leverageOf b - 1) * (leverageOf c - 1)
      ∧ tripleGapDet a b c = 0 := by
  have hprodAB : (leverageOf a - 1) * (leverageOf b - 1) = (a ⬝ᵥ b) ^ 2 := by
    rw [pairGapMinor] at hab; linarith
  have hprodAC : (leverageOf a - 1) * (leverageOf c - 1) = (a ⬝ᵥ c) ^ 2 := by
    rw [pairGapMinor] at hac; linarith
  have hprodBC : (leverageOf b - 1) * (leverageOf c - 1) = (b ⬝ᵥ c) ^ 2 := by
    rw [pairGapMinor] at hbc; linarith
  have hshape : tripleGapDet a b c
      = (leverageOf a - 1) * (leverageOf b - 1) * (leverageOf c - 1)
        - (leverageOf a - 1) * (b ⬝ᵥ c) ^ 2 - (leverageOf b - 1) * (a ⬝ᵥ c) ^ 2
        - (leverageOf c - 1) * (a ⬝ᵥ b) ^ 2
        + 2 * (a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c) := by
    rw [tripleGapDet]
  have heq : (a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c)
      = (leverageOf a - 1) * (leverageOf b - 1) * (leverageOf c - 1) :=
    cornerProduct_aux (by linarith) (by linarith) (by linarith) hprodAB hprodAC hprodBC
      (by rw [hshape] at hdet; linarith)
  refine ⟨heq, ?_⟩
  rw [hshape]
  linear_combination (leverageOf c - 1) * hprodAB + (leverageOf b - 1) * hprodAC
    + (leverageOf a - 1) * hprodBC + 2 * heq

/-! ## Part 4 — the trichotomy from three excesses

`Gtz.tripleStratum_trichotomy` asks `Gtz.AllHeavy`, a hypothesis on the whole
design, and `Gtz.Dominates`, a hypothesis on the whole gap.  Its content needs
neither: three positive excesses and the sign of one determinant suffice, on RAW
vectors. -/

/-- **TWO VANISHING PAIR MINORS FORCE THE THIRD, ON RAW VECTORS.**  The
design-level `Gtz.pairGapMinor_eq_zero_of_two_eq_zero` spends `Gtz.Dominates`
only to sign the determinant.  Here the sign is the hypothesis. -/
theorem pairGapMinor_eq_zero_of_two_eq_zero_raw {a b c : Fin 3 → ℝ}
    (hheavy : 1 < leverageOf a) (hdet : 0 ≤ tripleGapDet a b c)
    (hab : pairGapMinor a b = 0) (hac : pairGapMinor a c = 0) :
    pairGapMinor b c = 0 := by
  have hupper := tripleGapDet_nonpos_of_pairGapMinor_eq_zero c hheavy hab
  have hzero : tripleGapDet a b c = 0 := le_antisymm hupper hdet
  have hkey := leverageSub_mul_tripleGapDet_add_sq a b c
  rw [hab, zero_mul, hzero, mul_zero, zero_add] at hkey
  have hrow : (leverageOf a - 1) * (b ⬝ᵥ c) = (a ⬝ᵥ b) * (a ⬝ᵥ c) := by
    have hsq := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hkey
    linarith
  have hexcess : 0 < leverageOf a - 1 := by linarith
  have hfirst' : (leverageOf a - 1) * (leverageOf b - 1) = (a ⬝ᵥ b) ^ 2 := by
    rw [pairGapMinor] at hab; linarith
  have hsecond' : (leverageOf a - 1) * (leverageOf c - 1) = (a ⬝ᵥ c) ^ 2 := by
    rw [pairGapMinor] at hac; linarith
  have hclear : (leverageOf a - 1) ^ 2 * pairGapMinor b c = 0 := by
    rw [pairGapMinor]
    linear_combination ((leverageOf a - 1) * (leverageOf c - 1)) * hfirst'
      + ((a ⬝ᵥ b) ^ 2) * hsecond'
      - ((leverageOf a - 1) * (b ⬝ᵥ c) + (a ⬝ᵥ b) * (a ⬝ᵥ c)) * hrow
  have hne : (leverageOf a - 1) ^ 2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp hclear).resolve_left hne

/-- **THE TRICHOTOMY, ON RAW VECTORS.**  Three positive excesses and a
nonnegative triple determinant: the number of vanishing pair minors is `0`, `1` or
`3`, never `2`.  No design, no weights, no `Gtz.AllHeavy`, no `Gtz.Dominates`.

This is the elliptope's face structure.  A correlation matrix on the boundary of
the `3 x 3` elliptope has a unit entry only on an EDGE, and a unit entry forces the
other two rows proportional, so a second unit entry drags the third along.  There
is no two-vanishing face. -/
theorem tripleStratum_trichotomy_of_excess_pos {a b c : Fin 3 → ℝ}
    (hheavyA : 1 < leverageOf a) (hheavyB : 1 < leverageOf b) (hheavyC : 1 < leverageOf c)
    (hdet : 0 ≤ tripleGapDet a b c) :
    (pairGapMinor a b = 0 ∧ pairGapMinor a c = 0 ∧ pairGapMinor b c = 0)
      ∨ (pairGapMinor a b ≠ 0 ∧ pairGapMinor a c ≠ 0)
      ∨ (pairGapMinor a b ≠ 0 ∧ pairGapMinor b c ≠ 0)
      ∨ (pairGapMinor a c ≠ 0 ∧ pairGapMinor b c ≠ 0) := by
  by_cases hab : pairGapMinor a b = 0
  · by_cases hac : pairGapMinor a c = 0
    · exact Or.inl ⟨hab, hac, pairGapMinor_eq_zero_of_two_eq_zero_raw hheavyA hdet hab hac⟩
    · by_cases hbc : pairGapMinor b c = 0
      · refine absurd ?_ hac
        have hrot : tripleGapDet b a c = tripleGapDet a b c := by
          simp only [tripleGapDet, dotProduct_comm b a, dotProduct_comm b c, dotProduct_comm a c]
          ring
        have hbaZero : pairGapMinor b a = 0 := by rwa [pairGapMinor_comm]
        exact pairGapMinor_eq_zero_of_two_eq_zero_raw hheavyB (by rw [hrot]; exact hdet)
          hbaZero hbc
      · exact Or.inr (Or.inr (Or.inr ⟨hac, hbc⟩))
  · by_cases hac : pairGapMinor a c = 0
    · by_cases hbc : pairGapMinor b c = 0
      · refine absurd ?_ hab
        have hrot : tripleGapDet c a b = tripleGapDet a b c := tripleGapDet_rotate_left a b c
        have hcaZero : pairGapMinor c a = 0 := by rwa [pairGapMinor_comm]
        have hcbZero : pairGapMinor c b = 0 := by rwa [pairGapMinor_comm]
        exact pairGapMinor_eq_zero_of_two_eq_zero_raw hheavyC (by rw [hrot]; exact hdet)
          hcaZero hcbZero
      · exact Or.inr (Or.inr (Or.inl ⟨hab, hbc⟩))
    · exact Or.inr (Or.inl ⟨hab, hac⟩)

/-! ## Part 5 — strongness needs no admissibility

An inadmissible pair is strong outright, so the admissibility hypothesis of
`Gtz.exists_strongPair_of_isTie_of_allHeavy` and the branch-B hypothesis of
`Gtz.branchB_exists_strongPair` both dissolve. -/

/-- **AN INADMISSIBLE PAIR IS STRONG.**  Its excess product is already below its
squared pairing, let alone four times it.  Two lines, no hypothesis. -/
theorem strongPair_of_pairGapMinor_nonpos {a b : Fin 3 → ℝ}
    (hminor : pairGapMinor a b ≤ 0) : StrongPair a b := by
  rw [StrongPair]
  rw [pairGapMinor] at hminor
  nlinarith [sq_nonneg (a ⬝ᵥ b)]

/-- **EVERY NON-STRICT TRIPLE OF AN ALL-HEAVY DESIGN CARRIES A STRONG PAIR.**
No tie, no branch, no admissibility.

Split on the admissibility of the pair `{x,y}`.  If it fails, that pair is strong
by `Gtz.strongPair_of_pairGapMinor_nonpos`.  If it holds, the pair criterion
`Gtz.subsetSum_posDef_iff_pairVocabulary` has its first two clauses satisfied, so
the failure of strict domination is carried by the third, and
`Gtz.exists_strongPair_of_tripleGapDet_nonpos` reads a strong pair off that sign. -/
theorem exists_strongPair_of_allHeavy_of_not_posDef (D : WeightedDesign m 3)
    (hheavy : AllHeavy D) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hfail : ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    StrongPair (D.atom x) (D.atom y) ∨ StrongPair (D.atom x) (D.atom z)
      ∨ StrongPair (D.atom y) (D.atom z) := by
  by_cases hadm : AdmissiblePair (D.atom x) (D.atom y)
  · refine exists_strongPair_of_tripleGapDet_nonpos
      (by linarith [hheavy x]) (by linarith [hheavy y]) (by linarith [hheavy z]) ?_
    by_contra hpos
    push Not at hpos
    exact hfail ((subsetSum_posDef_iff_pairVocabulary D x y z hxy hxz hyz).mpr
      ⟨by linarith [hheavy x], hadm, hpos⟩)
  · exact Or.inl (strongPair_of_pairGapMinor_nonpos (not_lt.mp hadm))

/-- **THE `Gtz.GtzWeighted` READING.**  A design with NO dominating triple has no
strictly dominating triple either, so every triple carries a strong pair.  This is
the hypothesis a counterexample to the main statement supplies. -/
theorem exists_strongPair_of_allHeavy_of_forall_not_dominates (D : WeightedDesign m 3)
    (hheavy : AllHeavy D)
    (hnone : ∀ triple : Finset (Fin m), triple.card = 3 → ¬ Dominates D triple)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    StrongPair (D.atom x) (D.atom y) ∨ StrongPair (D.atom x) (D.atom z)
      ∨ StrongPair (D.atom y) (D.atom z) := by
  refine exists_strongPair_of_allHeavy_of_not_posDef D hheavy hxy hxz hyz fun hposDef => ?_
  exact hnone _ (card_triple_eq hxy hxz hyz) hposDef.posSemidef

/-- **THE TIE READING.**  At an all-heavy tie every triple carries a strong pair.
This removes the admissibility hypothesis from
`Gtz.exists_strongPair_of_isTie_of_allHeavy` and the branch hypothesis from
`Gtz.branchB_exists_strongPair`. -/
theorem exists_strongPair_of_isTie_of_allHeavy_unconditional (D : WeightedDesign m 3)
    (htie : IsTie D) (hheavy : AllHeavy D) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    StrongPair (D.atom x) (D.atom y) ∨ StrongPair (D.atom x) (D.atom z)
      ∨ StrongPair (D.atom y) (D.atom z) :=
  exists_strongPair_of_allHeavy_of_not_posDef D hheavy hxy hxz hyz
    (htie.2 _ (card_triple_eq hxy hxz hyz))

/-! ## Part 6 — the weak graph, and the Mantel count

Strongness is symmetric, so its negation spans a graph.  Part 5 says that graph is
triangle-free, and Mathlib's Turan bound at `r = 2` is Mantel's theorem. -/

/-- A pair is **weak** when it is not strong. -/
def WeakPair (D : WeightedDesign m 3) (first second : Fin m) : Prop :=
  ¬ StrongPair (D.atom first) (D.atom second)

theorem weakPair_comm (D : WeightedDesign m 3) (first second : Fin m) :
    WeakPair D first second ↔ WeakPair D second first := by
  rw [WeakPair, WeakPair]
  exact not_congr ⟨fun h => strongPair_comm h, fun h => strongPair_comm h⟩

/-- The **weak graph** on the labels of a design. -/
def weakPairGraph (D : WeightedDesign m 3) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel (WeakPair D)

@[simp] theorem weakPairGraph_adj (D : WeightedDesign m 3) (first second : Fin m) :
    (weakPairGraph D).Adj first second ↔ first ≠ second ∧ WeakPair D first second := by
  rw [weakPairGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hweak | hweak⟩
    · exact ⟨hne, hweak⟩
    · exact ⟨hne, (weakPair_comm D second first).mp hweak⟩
  · rintro ⟨hne, hweak⟩
    exact ⟨hne, Or.inl hweak⟩

/-- **THE WEAK GRAPH OF AN ALL-HEAVY DESIGN WITH NO STRICT DOMINATOR IS
TRIANGLE-FREE.**  Three pairwise weak labels would be a triple with no strong
pair, which part 5 forbids. -/
theorem cliqueFree_three_weakPairGraph (D : WeightedDesign m 3) (hheavy : AllHeavy D)
    (hnone : ∀ (x y z : Fin m), x ≠ y → x ≠ z → y ≠ z →
      ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    (weakPairGraph D).CliqueFree 3 := by
  classical
  intro clique hclique
  have hcard : clique.card = 3 := hclique.2
  set pick : Fin 3 → Fin m := fun index => clique.orderEmbOfFin hcard index with hpick
  have hmem : ∀ index : Fin 3, pick index ∈ clique := fun index =>
    clique.orderEmbOfFin_mem hcard index
  have hinjective : Function.Injective pick := (clique.orderEmbOfFin hcard).injective
  have hweak : ∀ left right : Fin 3, left ≠ right → WeakPair D (pick left) (pick right) := by
    intro left right hne
    have hadj : (weakPairGraph D).Adj (pick left) (pick right) :=
      hclique.1 (Finset.mem_coe.mpr (hmem left)) (Finset.mem_coe.mpr (hmem right))
        (fun heq => hne (hinjective heq))
    exact ((weakPairGraph_adj D _ _).mp hadj).2
  have hxy : pick 0 ≠ pick 1 := fun heq => by simpa using hinjective heq
  have hxz : pick 0 ≠ pick 2 := fun heq => by simpa using hinjective heq
  have hyz : pick 1 ≠ pick 2 := fun heq => by simpa using hinjective heq
  rcases exists_strongPair_of_allHeavy_of_not_posDef D hheavy hxy hxz hyz
    (hnone _ _ _ hxy hxz hyz) with hstrong | hstrong | hstrong
  · exact hweak 0 1 (by decide) hstrong
  · exact hweak 0 2 (by decide) hstrong
  · exact hweak 1 2 (by decide) hstrong

/-- **MANTEL'S COUNT ON THE WEAK GRAPH.**  A triangle-free graph on `m` vertices
has at most `(m ^ 2 - (m % 2) ^ 2) / 4` edges.  Mathlib's Turan bound at `r = 2`. -/
theorem card_edgeFinset_weakPairGraph_le (D : WeightedDesign m 3)
    [DecidableRel (weakPairGraph D).Adj] (hheavy : AllHeavy D)
    (hnone : ∀ (x y z : Fin m), x ≠ y → x ≠ z → y ≠ z →
      ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    (weakPairGraph D).edgeFinset.card
      ≤ (m ^ 2 - (m % 2) ^ 2) * 1 / 4 + (m % 2).choose 2 := by
  have hfree : (weakPairGraph D).CliqueFree (2 + 1) :=
    cliqueFree_three_weakPairGraph D hheavy hnone
  have hbound := hfree.card_edgeFinset_le (r := 2)
  simpa only [Fintype.card_fin] using hbound

/-- At `m = 6`: at most NINE of the fifteen pairs are weak. -/
theorem card_edgeFinset_weakPairGraph_le_nine (D : WeightedDesign 6 3)
    [DecidableRel (weakPairGraph D).Adj] (hheavy : AllHeavy D)
    (hnone : ∀ (x y z : Fin 6), x ≠ y → x ≠ z → y ≠ z →
      ¬ (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1).PosDef) :
    (weakPairGraph D).edgeFinset.card ≤ 9 := by
  have hbound := card_edgeFinset_weakPairGraph_le D hheavy hnone
  norm_num at hbound
  exact hbound

/-- **THE STRONG PAIRS ARE THE COMPLEMENTARY EDGES.**  Two distinct labels are
non-adjacent in the weak graph exactly when their pair is strong. -/
theorem compl_weakPairGraph_adj (D : WeightedDesign m 3) (first second : Fin m) :
    (weakPairGraph D)ᶜ.Adj first second
      ↔ first ≠ second ∧ StrongPair (D.atom first) (D.atom second) := by
  rw [SimpleGraph.compl_adj]
  constructor
  · rintro ⟨hne, hnotadj⟩
    refine ⟨hne, ?_⟩
    by_contra hweak
    exact hnotadj ((weakPairGraph_adj D first second).mpr ⟨hne, hweak⟩)
  · rintro ⟨hne, hstrong⟩
    refine ⟨hne, fun hadj => ?_⟩
    exact ((weakPairGraph_adj D first second).mp hadj).2 hstrong

/-- **THE COUNT.**  The two edge sets partition the complete graph, so the strong
pairs are at least `C(m,2)` minus the Mantel bound. -/
theorem card_edgeFinset_compl_weakPairGraph_ge (D : WeightedDesign m 3)
    [DecidableRel (weakPairGraph D).Adj] [DecidableRel (weakPairGraph D)ᶜ.Adj]
    (hheavy : AllHeavy D)
    (hnone : ∀ (x y z : Fin m), x ≠ y → x ≠ z → y ≠ z →
      ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    m.choose 2 - ((m ^ 2 - (m % 2) ^ 2) * 1 / 4 + (m % 2).choose 2)
      ≤ (weakPairGraph D)ᶜ.edgeFinset.card := by
  classical
  have hbound := card_edgeFinset_weakPairGraph_le D hheavy hnone
  have hdisjoint : Disjoint (weakPairGraph D).edgeFinset (weakPairGraph D)ᶜ.edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr disjoint_compl_right
  have hunion : (weakPairGraph D).edgeFinset ∪ (weakPairGraph D)ᶜ.edgeFinset
      = (⊤ : SimpleGraph (Fin m)).edgeFinset := by
    ext edge
    simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset]
    induction edge using Sym2.ind with
    | _ leftVertex rightVertex =>
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj, SimpleGraph.top_adj]
      constructor
      · rintro (hadjacent | ⟨hne, _⟩)
        · exact (weakPairGraph D).ne_of_adj hadjacent
        · exact hne
      · intro hne
        by_cases hadjacent : (weakPairGraph D).Adj leftVertex rightVertex
        · exact Or.inl hadjacent
        · exact Or.inr ⟨hne, hadjacent⟩
  have htotal : (weakPairGraph D).edgeFinset.card + (weakPairGraph D)ᶜ.edgeFinset.card
      = m.choose 2 := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  omega

/-- **AT LEAST SIX OF THE FIFTEEN PAIRS ARE STRONG.**  The count
`Gtz/Wave/BranchBStrongPair.lean` claimed in prose, now a theorem — and without
the branch-B hypothesis that claim carried.

An all-heavy `(6,3)` design with no strictly dominating triple has at most nine
weak pairs by Mantel, hence at least six strong ones. -/
theorem six_le_card_strongPairs_of_allHeavy (D : WeightedDesign 6 3)
    [DecidableRel (weakPairGraph D).Adj] [DecidableRel (weakPairGraph D)ᶜ.Adj]
    (hheavy : AllHeavy D)
    (hnone : ∀ (x y z : Fin 6), x ≠ y → x ≠ z → y ≠ z →
      ¬ (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1).PosDef) :
    6 ≤ (weakPairGraph D)ᶜ.edgeFinset.card := by
  have hbound := card_edgeFinset_compl_weakPairGraph_ge D hheavy hnone
  have hchoose : Nat.choose 6 2 = 15 := by decide
  norm_num [hchoose] at hbound
  omega

/-- **THE COUNT AT A TIE.**  An all-heavy `(6,3)` tie carries at least six strong
pairs. -/
theorem six_le_card_strongPairs_of_isTie (D : WeightedDesign 6 3)
    [DecidableRel (weakPairGraph D).Adj] [DecidableRel (weakPairGraph D)ᶜ.Adj]
    (htie : IsTie D) (hheavy : AllHeavy D) :
    6 ≤ (weakPairGraph D)ᶜ.edgeFinset.card :=
  six_le_card_strongPairs_of_allHeavy D hheavy
    fun _ _ _ hxy hxz hyz => htie.2 _ (card_triple_eq hxy hxz hyz)

/-! ## Part 7 — the strong triangle, unconditionally

The same triangle-freeness fed to `R(3,3) = 6` rather than to Mantel. -/

/-- **A STRONG TRIANGLE, WITH NO BRANCH HYPOTHESIS.**  Three atoms of an all-heavy
`(6,3)` design with no strictly dominating triple are pairwise strong.

`Gtz.branchB_exists_strong_triangle` proves the same conclusion under the branch-B
hypothesis that EVERY pair of the design is admissible.  Part 5 removes it. -/
theorem exists_strong_triangle_of_allHeavy_of_no_posDef (D : WeightedDesign 6 3)
    (hheavy : AllHeavy D)
    (hnone : ∀ (x y z : Fin 6), x ≠ y → x ≠ z → y ≠ z →
      ¬ (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1).PosDef) :
    ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      StrongPair (D.atom a) (D.atom b) ∧ StrongPair (D.atom a) (D.atom c)
        ∧ StrongPair (D.atom b) (D.atom c) := by
  obtain ⟨a, b, c, hab, hac, hbc, hbranch⟩ :=
    exists_monochromaticTriple_of_pairPredicate
      (fun i j : Fin 6 => StrongPair (D.atom i) (D.atom j)) (id : Fin 6 → Fin 6)
  simp only [id_eq] at hbranch
  rcases hbranch with hstrong | ⟨hwa, hwb, hwc⟩
  · exact ⟨a, b, c, hab, hac, hbc, hstrong.1, hstrong.2.1, hstrong.2.2⟩
  · exfalso
    rcases exists_strongPair_of_allHeavy_of_not_posDef D hheavy hab hac hbc
      (hnone _ _ _ hab hac hbc) with h | h | h
    · exact hwa h
    · exact hwb h
    · exact hwc h

/-- **THE STRONG TRIANGLE AT A TIE.** -/
theorem exists_strong_triangle_of_isTie_of_allHeavy (D : WeightedDesign 6 3)
    (htie : IsTie D) (hheavy : AllHeavy D) :
    ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      StrongPair (D.atom a) (D.atom b) ∧ StrongPair (D.atom a) (D.atom c)
        ∧ StrongPair (D.atom b) (D.atom c) :=
  exists_strong_triangle_of_allHeavy_of_no_posDef D hheavy
    fun _ _ _ hxy hxz hyz => htie.2 _ (card_triple_eq hxy hxz hyz)

/-! ## Part 8 — the weight currency of the triangle, and the reduction

`Gtz.strongPair_weight_cap` converts a strong pair into a statement about the
weight budgets `Σ a_c = 2` and `Σ (1 - s_c) = 3`.  Applied to the unconditional
triangle it prices a counterexample to the main statement. -/

/-- **A COUNTEREXAMPLE'S TRIANGLE, IN WEIGHT CURRENCY.**  An all-heavy `(6,3)`
design with no strictly dominating triple carries three labels whose weighted
excesses obey the three caps `a_i a_j ≤ 4 (1 - s_i)(1 - s_j)` at once. -/
theorem exists_strong_triangle_weight_caps_of_allHeavy (D : WeightedDesign 6 3)
    (hheavy : AllHeavy D)
    (hnone : ∀ (x y z : Fin 6), x ≠ y → x ≠ z → y ≠ z →
      ¬ (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1).PosDef) :
    ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (D.weight a * (leverageOf (D.atom a) - 1))
          * (D.weight b * (leverageOf (D.atom b) - 1))
        ≤ 4 * ((1 - D.weight a * leverageOf (D.atom a))
          * (1 - D.weight b * leverageOf (D.atom b))) ∧
      (D.weight a * (leverageOf (D.atom a) - 1))
          * (D.weight c * (leverageOf (D.atom c) - 1))
        ≤ 4 * ((1 - D.weight a * leverageOf (D.atom a))
          * (1 - D.weight c * leverageOf (D.atom c))) ∧
      (D.weight b * (leverageOf (D.atom b) - 1))
          * (D.weight c * (leverageOf (D.atom c) - 1))
        ≤ 4 * ((1 - D.weight b * leverageOf (D.atom b))
          * (1 - D.weight c * leverageOf (D.atom c))) := by
  obtain ⟨a, b, c, hab, hac, hbc, hsab, hsac, hsbc⟩ :=
    exists_strong_triangle_of_allHeavy_of_no_posDef D hheavy hnone
  exact ⟨a, b, c, hab, hac, hbc, strongPair_weight_cap D hab hsab,
    strongPair_weight_cap D hac hsac, strongPair_weight_cap D hbc hsbc⟩

/-- **THE REDUCTION.**  `Gtz.GtzWeighted 6 3` on the all-heavy stratum follows from
refuting the strong-graph configuration: an all-heavy design in which at least six
pairs are strong and some three are pairwise strong.

The hypothesis is stated as a refutation of the TRIANGLE, which is the sharper of
the two consequences.  A successor that instead refutes the COUNT should consume
`Gtz.six_le_card_strongPairs_of_allHeavy`. -/
theorem gtzWeighted_sixThree_of_strongGraph
    (hrefute : ∀ D : WeightedDesign 6 3, AllHeavy D →
      ¬ (∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        StrongPair (D.atom a) (D.atom b) ∧ StrongPair (D.atom a) (D.atom c)
          ∧ StrongPair (D.atom b) (D.atom c)))
    (D : WeightedDesign 6 3) (hheavy : AllHeavy D) :
    ∃ triple : Finset (Fin 6), triple.card = 3 ∧ Dominates D triple := by
  classical
  by_contra hnone
  push Not at hnone
  refine hrefute D hheavy (exists_strong_triangle_of_allHeavy_of_no_posDef D hheavy ?_)
  intro x y z hxy hxz hyz hposDef
  exact hnone _ (card_triple_eq hxy hxz hyz) hposDef.posSemidef

/-! ## Part 9 — triangle-freeness without the graph, and the tetrahedron detector

The graph of part 6 is only a bookkeeping device.  Its content is one three-line
statement about three labels, and that statement detects the regular tetrahedron. -/

/-- **TWO WEAK PAIRS THROUGH A COMMON ATOM FORCE A STRONG PAIR.**  The
triangle-freeness of the weak graph, with no graph API: if a pivot is weak to two
labels, those two labels are strong to each other.

This is the whole combinatorial content of parts 6 and 7, and it is the form a
successor should consume. -/
theorem strongPair_of_weakPair_of_weakPair (D : WeightedDesign m 3) (hheavy : AllHeavy D)
    {pivot first second : Fin m} (hpf : pivot ≠ first) (hps : pivot ≠ second)
    (hfs : first ≠ second)
    (hfail : ¬ (subsetSum D ({pivot, first, second} : Finset (Fin m)) - 1).PosDef)
    (hweakFirst : ¬ StrongPair (D.atom pivot) (D.atom first))
    (hweakSecond : ¬ StrongPair (D.atom pivot) (D.atom second)) :
    StrongPair (D.atom first) (D.atom second) := by
  rcases exists_strongPair_of_allHeavy_of_not_posDef D hheavy hpf hps hfs hfail with
    hstrong | hstrong | hstrong
  · exact absurd hstrong hweakFirst
  · exact absurd hstrong hweakSecond
  · exact hstrong

/-- **THE TETRAHEDRON DETECTOR.**  An atom weak to four others leaves those four
PAIRWISE STRONG — a strong `K_4`, which is exactly the configuration the regular
tetrahedron realises with equality in all six caps.

So the strong graph of a counterexample is either sparse at every vertex, or it
contains the tetrahedral clique.  Each of the six conclusions is one application
of `Gtz.strongPair_of_weakPair_of_weakPair` at the same pivot. -/
theorem strong_fourClique_of_weak_to_four (D : WeightedDesign m 3) (hheavy : AllHeavy D)
    (hnone : ∀ (x y z : Fin m), x ≠ y → x ≠ z → y ≠ z →
      ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef)
    {pivot a b c d : Fin m} (hpa : pivot ≠ a) (hpb : pivot ≠ b) (hpc : pivot ≠ c)
    (hpd : pivot ≠ d) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d)
    (hwa : ¬ StrongPair (D.atom pivot) (D.atom a))
    (hwb : ¬ StrongPair (D.atom pivot) (D.atom b))
    (hwc : ¬ StrongPair (D.atom pivot) (D.atom c))
    (hwd : ¬ StrongPair (D.atom pivot) (D.atom d)) :
    StrongPair (D.atom a) (D.atom b) ∧ StrongPair (D.atom a) (D.atom c)
      ∧ StrongPair (D.atom a) (D.atom d) ∧ StrongPair (D.atom b) (D.atom c)
      ∧ StrongPair (D.atom b) (D.atom d) ∧ StrongPair (D.atom c) (D.atom d) :=
  ⟨strongPair_of_weakPair_of_weakPair D hheavy hpa hpb hab (hnone _ _ _ hpa hpb hab) hwa hwb,
    strongPair_of_weakPair_of_weakPair D hheavy hpa hpc hac (hnone _ _ _ hpa hpc hac) hwa hwc,
    strongPair_of_weakPair_of_weakPair D hheavy hpa hpd had (hnone _ _ _ hpa hpd had) hwa hwd,
    strongPair_of_weakPair_of_weakPair D hheavy hpb hpc hbc (hnone _ _ _ hpb hpc hbc) hwb hwc,
    strongPair_of_weakPair_of_weakPair D hheavy hpb hpd hbd (hnone _ _ _ hpb hpd hbd) hwb hwd,
    strongPair_of_weakPair_of_weakPair D hheavy hpc hpd hcd (hnone _ _ _ hpc hpd hcd) hwc hwd⟩

/-! ## Part 10 — the two graph programmes are nested

`Gtz/Design/SignSelectedAggregate.lean` runs a second graph on the same labels:
`Gtz.IsHalfBoxGoodPair` is `2 p ^ 2 <= x_c x_d`, that is `rho ^ 2 <= 1/2`, and its
graph is `K_5`-FREE with a Turan bound of thirteen at six labels.  The strong graph
of this module is `rho ^ 2 >= 1/4`, so the two are NESTED, and nobody had said so.

The nesting is one line in each direction, and it shows which count is binding:
the half-box bound gives at least two strong pairs at six labels, and
`Gtz.six_le_card_strongPairs_of_allHeavy` gives six. -/

/-- **A WEAK PAIR IS HALF-BOX GOOD.**  `4 p ^ 2 < x_c x_d` implies `2 p ^ 2 <= x_c x_d`
because `2 p ^ 2 <= 4 p ^ 2`.  No hypothesis at all: the weak graph is a SUBGRAPH of
the landed half-box graph. -/
theorem isHalfBoxGoodPair_of_not_strongPair (D : WeightedDesign m 3) {first second : Fin m}
    (hweak : ¬ StrongPair (D.atom first) (D.atom second)) :
    IsHalfBoxGoodPair D first second := by
  rw [StrongPair] at hweak
  push Not at hweak
  rw [IsHalfBoxGoodPair, atomPairing, heavyExcess, heavyExcess]
  nlinarith [sq_nonneg (D.atom first ⬝ᵥ D.atom second)]

/-- **A HALF-BOX BAD PAIR IS STRONG.**  The contrapositive, and the direction that
transfers information: every pair the landed half-box count certifies as bad is a
strong pair of this module. -/
theorem strongPair_of_not_isHalfBoxGoodPair (D : WeightedDesign m 3) {first second : Fin m}
    (hbad : ¬ IsHalfBoxGoodPair D first second) :
    StrongPair (D.atom first) (D.atom second) := by
  by_contra hweak
  exact hbad (isHalfBoxGoodPair_of_not_strongPair D hweak)

/-- **THE STRONG GRAPH CONTAINS THE COMPLEMENT OF THE HALF-BOX GRAPH.**  Stated on
the graphs, so a successor may quote either Turan bound. -/
theorem weakPairGraph_le_halfBoxGoodGraph (D : WeightedDesign m 3) :
    weakPairGraph D ≤ halfBoxGoodGraph D := by
  intro first second hadj
  obtain ⟨hne, hweak⟩ := (weakPairGraph_adj D first second).mp hadj
  exact (halfBoxGoodGraph_adj D first second).mpr
    ⟨hne, isHalfBoxGoodPair_of_not_strongPair D hweak⟩

/-! ## Part 11 — the capstone

`Gtz.gtzWeightedHeavy_six_three_iff_gtzWeighted_six_three` says heaviness is not a
restriction at `(6,3)`, so the all-heavy reduction of part 8 upgrades to the main
statement with no hypothesis left over. -/

/-- **`Gtz.GtzWeighted 6 3` FOLLOWS FROM REFUTING THE STRONG TRIANGLE.**  Every
all-heavy `(6,3)` design carrying three pairwise strong atoms must instead carry a
dominating triple, and heaviness is free at this cell.

This is the whole main statement reduced to one finite geometric configuration:
three atoms of `ℝ^3`, each pair with squared pairing at least a quarter of the
product of its two leverage excesses. -/
theorem gtzWeighted_sixThree_of_no_strong_triangle
    (hrefute : ∀ D : WeightedDesign 6 3, AllHeavy D →
      ¬ (∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        StrongPair (D.atom a) (D.atom b) ∧ StrongPair (D.atom a) (D.atom c)
          ∧ StrongPair (D.atom b) (D.atom c))) :
    GtzWeighted 6 3 :=
  gtzWeightedHeavy_six_three_iff_gtzWeighted_six_three.mp
    fun D hheavy => gtzWeighted_sixThree_of_strongGraph hrefute D hheavy

/-- **THE HINGE READING.**  A `(6,3)` tie whose strong graph carries no triangle
has a parallel pair.  The funnel closure discharges the non-all-heavy case, so the
hypothesis is needed only on the all-heavy stratum. -/
theorem hasParallelPair_of_isTie_sixThree_of_no_strong_triangle (D : WeightedDesign 6 3)
    (htie : IsTie D)
    (hno : ¬ (∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      StrongPair (D.atom a) (D.atom b) ∧ StrongPair (D.atom a) (D.atom c)
        ∧ StrongPair (D.atom b) (D.atom c))) :
    HasParallelPair D := by
  rcases allHeavy_or_exists_leverage_eq_one_of_isTie_sixThree D htie with hall | ⟨label, hlabel⟩
  · exact absurd (exists_strong_triangle_of_isTie_of_allHeavy D htie hall) hno
  · exact hasParallelPair_of_isTie_sixThree_of_unitAtom D htie label hlabel

end Gtz

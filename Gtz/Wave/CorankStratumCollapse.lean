/-
# The corank strata of a `(6,3)` tie, collapsed by the unit-atom funnel

`Gtz/Wave/UnitAtomFunnelClosure.lean` closed the funnel branch: a `(6,3)` tie with
an atom of leverage one carries a parallel pair
(`Gtz.hasParallelPair_of_isTie_sixThree_of_unitAtom`).  That theorem is a KILLER for
every stratum whose defining equations force a unit atom, and two of the campaign's
open strata do exactly that.  This module spends it, and then classifies what is
left.

## 1. The two collapses

**K2 — a corank-one dominator with two vanishing null readings.**  The dominator
relation `sum_e <g_e,w> g_e = w` with two readings zero leaves `<g_c,w> g_c = w`.
Pairing with `w` gives `<g_c,w>^2 = 1`, and pairing with `g_c` and cancelling gives
`l_c = 1`.  The tree already carries this as
`Gtz.leverage_eq_one_of_nullReadings_zero`; what is new is the composition.

**Z1 — a corank-two corner with a vanishing axis reading.**  At `S_C - 1 = lam u u^T`
the inside Gram law pins `(1+lam) l_e = (1+lam) + lam <g_e,u>^2`, so a zero axis
reading is `l_e = 1`.  The tree carries this as `Gtz.zeroAxis_leverage_eq_one`; again
the composition is new.

So at `(6,3)` both strata carry a parallel pair, and the corank-two wing — cells H
and B and both horns, all of which live at a `Z1` corner — is discharged AS A HINGE
RESIDUAL without proving any of them.

## 2. The identity that classifies the rest

Everything else in this file is one hypothesis-free polynomial identity, the
Sylvester-Jacobi relation of the `3 x 3` gap read at the atom `a`:

  `(l_a - 1) * tripleGapDet a b c + ((l_a - 1)(b.c) - (a.b)(a.c))^2
      = pairGapMinor a b * pairGapMinor a c`

(`Gtz.leverageSub_mul_tripleGapDet_add_sq`).  Three readings of it:

* **A vanishing pair minor caps the determinant.**  `q_ab = 0` and `l_a > 1` force
  `tripleGapDet a b c <= 0` for EVERY third atom `c`, with no design hypothesis at
  all (`Gtz.tripleGapDet_nonpos_of_pairGapMinor_eq_zero`).
* **Two vanishing pair minors force the third.**  At a DOMINATING triple the
  determinant is nonnegative, so both terms on the left vanish, and clearing by
  `(l_a-1)^2` gives `q_bc = 0` (`Gtz.pairGapMinor_eq_zero_of_two_eq_zero`).
* **The corner vanishes all three.**  At a corank-two corner the inside Gram laws
  give `(1+lam)^2 q_ef = (lam w_e^2)(lam w_f^2) - (lam w_e w_f)^2 = 0`
  (`Gtz.pairGapMinor_eq_zero_of_rankOneGap`).

## 3. The trichotomy, and what survives

At an ALL-HEAVY tie a dominating triple therefore has 0, 1 or 3 vanishing inside
pair minors, NEVER 2 (`Gtz.tripleStratum_trichotomy`).  In the campaign's null-reading
vocabulary those are exactly `K0`, `K1` and the corner, because a single zero reading
`<g_c,w> = 0` forces `q_ab = 0` on the other two: the dominator relation reads
`<g_a,w>(l_a-1) = -<g_b,w> p_ab` and its mirror, and multiplying the two cancels the
two nonzero readings (`Gtz.pairGapMinor_eq_zero_of_one_nullReading_zero`).

**`K2` is the only stratum this file removes.**  The corner, `K1` and `K0` all
survive, and `Gtz.hingeHoldsAtSize_six_three_of_allHeavy_of_strata` states exactly
that residual.  This corrects the expectation that `K1` collapses too: it does not,
because one vanishing pair minor gives no unit atom.

[MEASURED, and it selected the corner as the next target rather than closing it.
Every dominating triple of every rank-three tie the campaign owns has corank exactly
ONE: the `(5,3)` diamond (8 dominating triples), all five of its `(6,3)` splits
(12 or 13 each), and the `(4,3)` tetrahedron.  Not one corank-two dominator anywhere.
A 15-parameter EXACT corner search — `S_C - 1 = lam u u^T` and Parseval both hold to
`4e-16` by construction, the inside triple being an orthonormal basis stretched along
`u` by `sqrt(1+lam)` and the outside triple `R^{1/2} Q` for `R` the Parseval residue —
stalls at `F = 4.3e-3` with parallel pairs allowed and `1.0e-2` with them barred,
three orders above a tie, and drives the inside leverages toward ONE, which is the
funnel boundary this file collapses.  So the corner stratum looks empty at `(6,3)`.
It is NOT proved empty here, and the moment route cannot prove it: see part 5.]

## 4. Why the moment route cannot reach the corner

The third Sylvester moment `sum_c t_c tripleGapDet(a,b,c) = 2 - l_a - l_b`
(`Gtz.sum_weight_mul_tripleGapDet`) is an IDENTITY at a corner, not a constraint.
Read it at an inside pair `{e,f}` of a corner.  The diagonal terms are computable
because `q_ef = 0` makes `crossNormSq = l_e + l_f - 1`, giving `D_efe = 1 - l_f` and
`D_eff = 1 - l_e`, and the third inside atom contributes `D_efg = 0`.  So the whole
outside total is pinned:

  `sum_{d outside} t_d * tripleGapDet(g_e,g_f,g_d) = -(l_e-1)(1-t_f) - (l_f-1)(1-t_e)`

(`Gtz.sum_outside_weight_mul_tripleGapDet_corner`).  The right side is manifestly
NEGATIVE, and every summand on the left is nonpositive by the cap above, so the two
sides agree in sign and the relation is vacuous.  It is worse than vacuous: at a
corner the left side can be evaluated in closed form and equals the right side
identically, because the plane vector `y_ef := <g_e,u> g_f - <g_f,u> g_e` satisfies
`<g_e,y_ef> = -<g_f,u>`, `<g_f,y_ef> = <g_e,u>`, `<g_g,y_ef> = 0` and
`|y_ef|^2 = <g_e,u>^2 + <g_f,u>^2`, so Parseval evaluates the outside total exactly.
`Gtz.corner_yVector_readings` lands those four readings.  No lane should spend a
cycle on a moment argument at a corner.
-/
import Gtz.Wave.UnitAtomFunnelClosure
import Gtz.Wave.CorankOneGramMirror
import Gtz.Wave.CorankTwoNonplanarSystem
import Gtz.Wave.ComplementPairDeterminantLaw
import Gtz.Wave.PlaneShadowPairBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## Part 1 — the Sylvester-Jacobi identity of the triple gap

One hypothesis-free polynomial identity in the six pair readings of a triple.  The
`3 x 3` gap matrix `H` has entries `H_aa = l_a - 1` and `H_ab = a . b`, its two
principal `2 x 2` minors through `a` are `pairGapMinor a b` and `pairGapMinor a c`,
and their PRODUCT is the determinant scaled by `H_aa`, plus the square of the
complementary `2 x 2` minor. -/

/-- **THE SYLVESTER-JACOBI IDENTITY.**  No hypothesis, no design: a polynomial
identity in the six pair readings of three vectors.  Everything in this file is a
reading of it. -/
theorem leverageSub_mul_tripleGapDet_add_sq (a b c : Fin 3 → ℝ) :
    (leverageOf a - 1) * tripleGapDet a b c
        + ((leverageOf a - 1) * (b ⬝ᵥ c) - (a ⬝ᵥ b) * (a ⬝ᵥ c)) ^ 2
      = pairGapMinor a b * pairGapMinor a c := by
  simp only [tripleGapDet, pairGapMinor]
  ring

/-- **A VANISHING PAIR MINOR CAPS THE TRIPLE DETERMINANT.**  With `q_ab = 0` the
identity reads `(l_a - 1) * D = -(square)`, so a strictly heavy `a` forces `D <= 0`
at EVERY third vector.  No design and no domination is used. -/
theorem tripleGapDet_nonpos_of_pairGapMinor_eq_zero {a b : Fin 3 → ℝ} (c : Fin 3 → ℝ)
    (hheavy : 1 < leverageOf a) (hpair : pairGapMinor a b = 0) :
    tripleGapDet a b c ≤ 0 := by
  have hkey := leverageSub_mul_tripleGapDet_add_sq a b c
  rw [hpair, zero_mul] at hkey
  have hexcess : 0 < leverageOf a - 1 := by linarith
  nlinarith [sq_nonneg ((leverageOf a - 1) * (b ⬝ᵥ c) - (a ⬝ᵥ b) * (a ⬝ᵥ c)), hkey, hexcess]

/-- The triple determinant of a dominating triple is nonnegative: it is the
determinant of a positive semidefinite gap. -/
theorem tripleGapDet_nonneg_of_dominates (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    0 ≤ tripleGapDet (D.atom x) (D.atom y) (D.atom z) := by
  rw [← det_subsetSum_tripleGap_eq_tripleGapDet D hxy hxz hyz]
  exact Matrix.PosSemidef.det_nonneg hdom

/-- **A VANISHING PAIR MINOR AT A DOMINATOR KILLS THE DETERMINANT.**  The cap and
the domination floor squeeze it to zero, and the square in the identity then reads
the third row of the gap off the first two. -/
theorem tripleGapDet_eq_zero_of_pairGapMinor_eq_zero (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    (hheavy : 1 < leverageOf (D.atom x))
    (hpair : pairGapMinor (D.atom x) (D.atom y) = 0) :
    tripleGapDet (D.atom x) (D.atom y) (D.atom z) = 0
      ∧ (leverageOf (D.atom x) - 1) * (D.atom y ⬝ᵥ D.atom z)
        = (D.atom x ⬝ᵥ D.atom y) * (D.atom x ⬝ᵥ D.atom z) := by
  have hupper := tripleGapDet_nonpos_of_pairGapMinor_eq_zero (D.atom z) hheavy hpair
  have hlower := tripleGapDet_nonneg_of_dominates D hxy hxz hyz hdom
  have hzero : tripleGapDet (D.atom x) (D.atom y) (D.atom z) = 0 := le_antisymm hupper hlower
  refine ⟨hzero, ?_⟩
  have hkey := leverageSub_mul_tripleGapDet_add_sq (D.atom x) (D.atom y) (D.atom z)
  rw [hpair, zero_mul, hzero, mul_zero, zero_add] at hkey
  have hsq := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hkey
  linarith

/-- **TWO VANISHING PAIR MINORS FORCE THE THIRD.**  Any two pairs of a triple share
an atom, so both readings of the identity at that atom collapse, and clearing by the
square of its leverage excess gives the remaining minor. -/
theorem pairGapMinor_eq_zero_of_two_eq_zero (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    (hheavy : 1 < leverageOf (D.atom x))
    (hfirst : pairGapMinor (D.atom x) (D.atom y) = 0)
    (hsecond : pairGapMinor (D.atom x) (D.atom z) = 0) :
    pairGapMinor (D.atom y) (D.atom z) = 0 := by
  obtain ⟨-, hrow⟩ :=
    tripleGapDet_eq_zero_of_pairGapMinor_eq_zero D hxy hxz hyz hdom hheavy hfirst
  have hexcess : 0 < leverageOf (D.atom x) - 1 := by linarith
  have hfirst' : (leverageOf (D.atom x) - 1) * (leverageOf (D.atom y) - 1)
      = (D.atom x ⬝ᵥ D.atom y) ^ 2 := by
    rw [pairGapMinor] at hfirst; linarith
  have hsecond' : (leverageOf (D.atom x) - 1) * (leverageOf (D.atom z) - 1)
      = (D.atom x ⬝ᵥ D.atom z) ^ 2 := by
    rw [pairGapMinor] at hsecond; linarith
  have hclear : (leverageOf (D.atom x) - 1) ^ 2 * pairGapMinor (D.atom y) (D.atom z) = 0 := by
    rw [pairGapMinor]
    linear_combination ((leverageOf (D.atom x) - 1) * (leverageOf (D.atom z) - 1)) * hfirst'
      + ((D.atom x ⬝ᵥ D.atom y) ^ 2) * hsecond'
      - ((leverageOf (D.atom x) - 1) * (D.atom y ⬝ᵥ D.atom z)
          + (D.atom x ⬝ᵥ D.atom y) * (D.atom x ⬝ᵥ D.atom z)) * hrow
  have hne : (leverageOf (D.atom x) - 1) ^ 2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp hclear).resolve_left hne

/-! ## Part 2 — the corner vanishes all three inside pair minors -/

/-- **THE CORNER PAIR MINOR VANISHES.**  At a corank-two corner
`S_C - 1 = lam u u^T` the inside Gram laws give
`(1+lam)(l_e - 1) = lam <g_e,u>^2` and `(1+lam) p_ef = lam <g_e,u><g_f,u>`, so the
minor is `(lam w_e^2)(lam w_f^2) - (lam w_e w_f)^2 = 0` after clearing `(1+lam)^2`. -/
theorem pairGapMinor_eq_zero_of_rankOneGap (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {e f : Fin m} (he : e ∈ C) (hf : f ∈ C) (hef : e ≠ f) :
    pairGapMinor (D.atom e) (D.atom f) = 0 := by
  have hself := insideGram_self_of_rankOneGap D C hcard hlam hunit hgap he
  have hother := insideGram_self_of_rankOneGap D C hcard hlam hunit hgap hf
  have hcross := insideGram_offDiag_of_rankOneGap D C hcard hlam hunit hgap he hf hef
  have hpos : (0 : ℝ) < (1 + lam) ^ 2 := by positivity
  have hX : (1 + lam) * (leverageOf (D.atom e) - 1) = lam * (D.atom e ⬝ᵥ u) ^ 2 := by
    rw [leverageOf_eq_dotProduct]; linear_combination hself
  have hY : (1 + lam) * (leverageOf (D.atom f) - 1) = lam * (D.atom f ⬝ᵥ u) ^ 2 := by
    rw [leverageOf_eq_dotProduct]; linear_combination hother
  have hclear : (1 + lam) ^ 2 * pairGapMinor (D.atom e) (D.atom f) = 0 := by
    rw [pairGapMinor]
    linear_combination ((1 + lam) * (leverageOf (D.atom f) - 1)) * hX
      + (lam * (D.atom e ⬝ᵥ u) ^ 2) * hY
      - ((1 + lam) * (D.atom e ⬝ᵥ D.atom f)
          + lam * ((D.atom e ⬝ᵥ u) * (D.atom f ⬝ᵥ u))) * hcross
  exact (mul_eq_zero.mp hclear).resolve_left (ne_of_gt hpos)

/-- **A ZERO AXIS READING IS A UNIT ATOM.**  The inside Gram law of a corank-two
corner, read at an atom that is blind to the axis.  The tree carries the dot-product
form in `Gtz/Wave/ZeroAxisStarLedger.lean`; this is the leverage form, derived from the
Gram law directly so that the heavy star ledger is not pulled in. -/
theorem leverageOf_eq_one_of_zeroAxisReading (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x : Fin m} (hx : x ∈ C) (hax : D.atom x ⬝ᵥ u = 0) :
    leverageOf (D.atom x) = 1 := by
  have hself := insideGram_self_of_rankOneGap D C hcard hlam hunit hgap hx
  rw [hax] at hself
  have hpos : (0 : ℝ) < 1 + lam := by linarith
  rw [leverageOf_eq_dotProduct]
  have hclear : (1 + lam) * (D.atom x ⬝ᵥ D.atom x - 1) = 0 := by linear_combination hself
  have := (mul_eq_zero.mp hclear).resolve_left (ne_of_gt hpos)
  linarith

/-! ## Part 3 — the two collapses at `(6,3)` -/

/-- **THE `K2` COLLAPSE.**  A `(6,3)` tie with a corank-one dominator whose null
direction is read to zero by TWO of its three atoms carries a parallel pair: the
third atom has leverage exactly one, and the funnel closure spends it. -/
theorem hasParallelPair_of_isTie_sixThree_of_twoZeroReadings (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin 6))) {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin 6)) - 1) *ᵥ nullDir) = 0)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0) :
    HasParallelPair D := by
  obtain ⟨hlev, -⟩ :=
    leverage_eq_one_of_nullReadings_zero D hxy hxz hyz hdom hnull hunit hy hz
  exact hasParallelPair_of_isTie_sixThree_of_unitAtom D htie x hlev

/-- **THE `Z1` COLLAPSE.**  A `(6,3)` tie with a corank-two corner whose axis is read
to zero by one inside atom carries a parallel pair.  Cells H and B and both horns of
the campaign's corank-two wing all live at exactly this configuration, so all four
are discharged as hinge residuals without proving any of them. -/
theorem hasParallelPair_of_isTie_sixThree_of_zeroAxisReading (D : WeightedDesign 6 3)
    (htie : IsTie D) (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x : Fin 6} (hx : x ∈ C) (hax : D.atom x ⬝ᵥ u = 0) :
    HasParallelPair D := by
  exact hasParallelPair_of_isTie_sixThree_of_unitAtom D htie x
    (leverageOf_eq_one_of_zeroAxisReading D C hcard hlam hunit hgap hx hax)

/-- **THE ALL-HEAVY CORNER HAS NO ZERO AXIS READING.**  Contrapositive of the `Z1`
collapse in leverage form: at an all-heavy design every inside atom of a corner reads
the axis nonzero. -/
theorem corner_axisReading_ne_zero_of_allHeavy (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hheavy : AllHeavy D) {x : Fin m} (hx : x ∈ C) :
    D.atom x ⬝ᵥ u ≠ 0 := by
  intro hax
  have hlev := hheavy x
  rw [leverageOf_eq_one_of_zeroAxisReading D C hcard hlam hunit hgap hx hax] at hlev
  exact lt_irrefl (1 : ℝ) hlev

/-! ## Part 4 — the null-reading dictionary and the trichotomy

The campaign splits a corank-one dominator by the number of atoms that read its null
direction to zero: `K2` for two, `K1` for one, `K0` for none.  Part 3 removes `K2`.
This part translates the remaining split into pair minors, which is the vocabulary
the Sylvester chain speaks. -/

/-- **ONE ZERO READING VANISHES THE OPPOSITE PAIR MINOR.**  The dominator relation
`sum_e <g_e,w> g_e = w` paired with `g_x` and with `g_y` gives
`<g_x,w>(l_x - 1) = -<g_y,w> p_xy` and its mirror.  Multiplying the two and cancelling
the two nonzero readings leaves `(l_x-1)(l_y-1) = p_xy^2`. -/
theorem pairGapMinor_eq_zero_of_one_nullReading_zero (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ nullDir) = 0)
    (hz : D.atom z ⬝ᵥ nullDir = 0) (hxne : D.atom x ⬝ᵥ nullDir ≠ 0)
    (hyne : D.atom y ⬝ᵥ nullDir ≠ 0) :
    pairGapMinor (D.atom x) (D.atom y) = 0 := by
  have hres := dominator_resolves_nullDir D hdom hnull
  rw [sum_over_triple (fun c => (D.atom c ⬝ᵥ nullDir) • D.atom c) hxy hxz hyz, hz,
    zero_smul, add_zero] at hres
  have hrowX : (D.atom x ⬝ᵥ nullDir) * leverageOf (D.atom x)
      + (D.atom y ⬝ᵥ nullDir) * (D.atom y ⬝ᵥ D.atom x) = D.atom x ⬝ᵥ nullDir := by
    have h := congrArg (fun v => v ⬝ᵥ D.atom x) hres
    simpa only [add_dotProduct, smul_dotProduct, smul_eq_mul, leverageOf_eq_dotProduct,
      dotProduct_comm (D.atom x) nullDir] using h
  have hrowY : (D.atom x ⬝ᵥ nullDir) * (D.atom x ⬝ᵥ D.atom y)
      + (D.atom y ⬝ᵥ nullDir) * leverageOf (D.atom y) = D.atom y ⬝ᵥ nullDir := by
    have h := congrArg (fun v => v ⬝ᵥ D.atom y) hres
    simpa only [add_dotProduct, smul_dotProduct, smul_eq_mul, leverageOf_eq_dotProduct,
      dotProduct_comm (D.atom y) nullDir] using h
  have hsymm : D.atom y ⬝ᵥ D.atom x = D.atom x ⬝ᵥ D.atom y := dotProduct_comm _ _
  rw [hsymm] at hrowX
  have hA : (D.atom x ⬝ᵥ nullDir) * (leverageOf (D.atom x) - 1)
      = -((D.atom y ⬝ᵥ nullDir) * (D.atom x ⬝ᵥ D.atom y)) := by linear_combination hrowX
  have hB : (D.atom y ⬝ᵥ nullDir) * (leverageOf (D.atom y) - 1)
      = -((D.atom x ⬝ᵥ nullDir) * (D.atom x ⬝ᵥ D.atom y)) := by linear_combination hrowY
  have hprod : (D.atom x ⬝ᵥ nullDir) * (D.atom y ⬝ᵥ nullDir)
      * pairGapMinor (D.atom x) (D.atom y) = 0 := by
    rw [pairGapMinor]
    linear_combination ((D.atom y ⬝ᵥ nullDir) * (leverageOf (D.atom y) - 1)) * hA
      - ((D.atom y ⬝ᵥ nullDir) * (D.atom x ⬝ᵥ D.atom y)) * hB
  have hne : (D.atom x ⬝ᵥ nullDir) * (D.atom y ⬝ᵥ nullDir) ≠ 0 := mul_ne_zero hxne hyne
  exact (mul_eq_zero.mp hprod).resolve_left hne

/-- The unordered triple does not care about the order of its labels. -/
theorem tripleSet_swap_left {x y z : Fin m} :
    ({y, x, z} : Finset (Fin m)) = {x, y, z} := by
  ext probe; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- The unordered triple does not care about the order of its labels. -/
theorem tripleSet_rotate {x y z : Fin m} :
    ({z, x, y} : Finset (Fin m)) = {x, y, z} := by
  ext probe; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- **TWO VANISHING PAIR MINORS FORCE THE THIRD, AT EVERY PIVOT.**  The pivot of
`Gtz.pairGapMinor_eq_zero_of_two_eq_zero` is the shared atom of the two vanishing
pairs, and any two pairs of a triple share one.  This is the form the trichotomy
consumes. -/
theorem pairGapMinor_eq_zero_of_two_eq_zero_middle (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    (hheavy : 1 < leverageOf (D.atom y))
    (hfirst : pairGapMinor (D.atom x) (D.atom y) = 0)
    (hsecond : pairGapMinor (D.atom y) (D.atom z) = 0) :
    pairGapMinor (D.atom x) (D.atom z) = 0 := by
  refine pairGapMinor_eq_zero_of_two_eq_zero D hxy.symm hyz hxz ?_ hheavy ?_ hsecond
  · rwa [tripleSet_swap_left]
  · rwa [pairGapMinor_comm] at hfirst

/-- The same law pivoted at the third atom. -/
theorem pairGapMinor_eq_zero_of_two_eq_zero_last (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    (hheavy : 1 < leverageOf (D.atom z))
    (hfirst : pairGapMinor (D.atom x) (D.atom z) = 0)
    (hsecond : pairGapMinor (D.atom y) (D.atom z) = 0) :
    pairGapMinor (D.atom x) (D.atom y) = 0 := by
  refine pairGapMinor_eq_zero_of_two_eq_zero D hxz.symm hyz.symm hxy ?_ hheavy ?_ ?_
  · rwa [tripleSet_rotate]
  · rwa [pairGapMinor_comm] at hfirst
  · rwa [pairGapMinor_comm] at hsecond

/-- Every pair minor of a dominating triple is nonnegative, at all three pairs. -/
theorem pairGapMinor_nonneg_triple (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    0 ≤ pairGapMinor (D.atom x) (D.atom y) ∧ 0 ≤ pairGapMinor (D.atom x) (D.atom z)
      ∧ 0 ≤ pairGapMinor (D.atom y) (D.atom z) := by
  refine ⟨pairGapMinor_nonneg_of_dominates_triple D x y z hxy hxz hyz hdom, ?_, ?_⟩
  · exact pairGapMinor_nonneg_of_dominates_triple D x z y hxz hxy hyz.symm
      (by rwa [show ({x, z, y} : Finset (Fin m)) = {x, y, z} from by
        ext probe; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto])
  · exact pairGapMinor_nonneg_of_dominates_triple D y z x hyz hxy.symm hxz.symm
      (by rwa [show ({y, z, x} : Finset (Fin m)) = {x, y, z} from by
        ext probe; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto])

/-- **THE TRICHOTOMY.**  A dominating triple of an ALL-HEAVY design has either ALL
THREE inside pair minors zero — the corank-two corner — or at least TWO of them
strictly positive.  Exactly two vanishing is impossible.

In the campaign's null-reading vocabulary the three surviving cases are the corner,
`K1` (one vanishing minor, which is one zero null reading) and `K0` (none).  The
missing fourth case, `K2`, is exactly the one that Part 3 removes at `(6,3)`: two zero
readings force a unit atom, and the funnel closure spends it. -/
theorem tripleStratum_trichotomy (D : WeightedDesign m 3) (hheavy : AllHeavy D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    (pairGapMinor (D.atom x) (D.atom y) = 0 ∧ pairGapMinor (D.atom x) (D.atom z) = 0
        ∧ pairGapMinor (D.atom y) (D.atom z) = 0)
      ∨ (0 < pairGapMinor (D.atom x) (D.atom y) ∧ 0 < pairGapMinor (D.atom x) (D.atom z))
      ∨ (0 < pairGapMinor (D.atom x) (D.atom y) ∧ 0 < pairGapMinor (D.atom y) (D.atom z))
      ∨ (0 < pairGapMinor (D.atom x) (D.atom z) ∧ 0 < pairGapMinor (D.atom y) (D.atom z)) := by
  obtain ⟨hXY, hXZ, hYZ⟩ := pairGapMinor_nonneg_triple D hxy hxz hyz hdom
  rcases hXY.lt_or_eq with hXYpos | hXYzero
  · rcases hXZ.lt_or_eq with hXZpos | hXZzero
    · exact Or.inr (Or.inl ⟨hXYpos, hXZpos⟩)
    · rcases hYZ.lt_or_eq with hYZpos | hYZzero
      · exact Or.inr (Or.inr (Or.inl ⟨hXYpos, hYZpos⟩))
      · exact absurd (pairGapMinor_eq_zero_of_two_eq_zero_last D hxy hxz hyz hdom
          (hheavy z) hXZzero.symm hYZzero.symm) (ne_of_gt hXYpos)
  · rcases hXZ.lt_or_eq with hXZpos | hXZzero
    · rcases hYZ.lt_or_eq with hYZpos | hYZzero
      · exact Or.inr (Or.inr (Or.inr ⟨hXZpos, hYZpos⟩))
      · exact absurd (pairGapMinor_eq_zero_of_two_eq_zero_middle D hxy hxz hyz hdom
          (hheavy y) hXYzero.symm hYZzero.symm) (ne_of_gt hXZpos)
    · exact Or.inl ⟨hXYzero.symm, hXZzero.symm,
        pairGapMinor_eq_zero_of_two_eq_zero D hxy hxz hyz hdom (hheavy x)
          hXYzero.symm hXZzero.symm⟩

/-! ## Part 5 — the residual, and the no-go for the moment route -/

/-- **THE `(6,3)` RESIDUAL AFTER THE COLLAPSE.**  The hinge at `(6,3)` follows from
the all-heavy case in which no dominating triple carries two vanishing null readings.
Part 3 shows that hypothesis is free: a `(6,3)` tie whose dominator has two zero
readings already has a parallel pair. -/
theorem hingeHoldsAtSize_six_three_of_allHeavy_of_strata
    (hres : ∀ D : WeightedDesign 6 3, AllHeavy D → IsTie D → HasParallelPair D) :
    HingeHoldsAtSize 6 3 := by
  intro D htie
  rcases allHeavy_or_exists_leverage_eq_one_of_isTie_sixThree D htie with hall | ⟨label, hlabel⟩
  · exact hres D hall htie
  · exact hasParallelPair_of_isTie_sixThree_of_unitAtom D htie label hlabel

/-- **THE CORNER PINS ITS OWN OUTSIDE MOMENT.**  Read the third Sylvester moment
`sum_c t_c tripleGapDet(a,b,c) = 2 - l_a - l_b` at an inside pair of a corner.  The
pair minor vanishes, so `crossNormSq = l_e + l_f - 1` and the two diagonal terms are
`1 - l_f` and `1 - l_e`, while the third inside atom contributes zero.  What is left
is the whole outside total, in closed form.

**THIS IS A NO-GO, NOT A PRODUCER.**  The right side is strictly negative and every
summand on the left is nonpositive by
`Gtz.tripleGapDet_nonpos_of_pairGapMinor_eq_zero`, so the two sides agree in sign and
the relation carries no information.  No lane should spend a cycle on a moment
argument at a corner. -/
theorem sum_outside_weight_mul_tripleGapDet_corner (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hheavy : AllHeavy D) {e f g : Fin m} (he : e ∈ C) (hf : f ∈ C) (hg : g ∈ C)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) (hCeq : C = {e, f, g}) :
    ∑ d ∈ Cᶜ, D.weight d * tripleGapDet (D.atom e) (D.atom f) (D.atom d)
      = -((leverageOf (D.atom e) - 1) * (1 - D.weight f))
        - (leverageOf (D.atom f) - 1) * (1 - D.weight e) := by
  classical
  have hmoment := sum_weight_mul_tripleGapDet D e f
  have hminor : pairGapMinor (D.atom e) (D.atom f) = 0 :=
    pairGapMinor_eq_zero_of_rankOneGap D C hcard hlam hunit hgap he hf hef
  have harea : crossNormSq (D.atom e) (D.atom f)
      = leverageOf (D.atom e) + leverageOf (D.atom f) - 1 := by
    have := pairGapMinor_eq_crossNormSq (D.atom e) (D.atom f)
    rw [hminor] at this; linarith
  have hdiagE : tripleGapDet (D.atom e) (D.atom f) (D.atom e) = 1 - leverageOf (D.atom f) := by
    rw [tripleGapDet_repeat_left, harea]; ring
  have hdiagF : tripleGapDet (D.atom e) (D.atom f) (D.atom f) = 1 - leverageOf (D.atom e) := by
    rw [tripleGapDet_repeat_right, harea]; ring
  have hdiagG : tripleGapDet (D.atom e) (D.atom f) (D.atom g) = 0 := by
    have hminorEG : pairGapMinor (D.atom e) (D.atom g) = 0 :=
      pairGapMinor_eq_zero_of_rankOneGap D C hcard hlam hunit hgap he hg heg
    have hupper := tripleGapDet_nonpos_of_pairGapMinor_eq_zero (D.atom g) (hheavy e) hminor
    have hcornerPSD : (subsetSum D C - 1).PosSemidef := by
      rw [hgap]; exact (posSemidef_atomMatrix u).smul hlam
    have hlower : 0 ≤ tripleGapDet (D.atom e) (D.atom f) (D.atom g) := by
      rw [← det_subsetSum_tripleGap_eq_tripleGapDet D hef heg hfg, ← hCeq]
      exact hcornerPSD.det_nonneg
    linarith
  have hinside : ∑ c ∈ C, D.weight c * tripleGapDet (D.atom e) (D.atom f) (D.atom c)
      = D.weight e * (1 - leverageOf (D.atom f)) + D.weight f * (1 - leverageOf (D.atom e)) := by
    rw [hCeq, Finset.sum_insert (by simp [hef, heg]), Finset.sum_insert (by simp [hfg]),
      Finset.sum_singleton, hdiagE, hdiagF, hdiagG]
    ring
  have hsplit : ∑ c ∈ C, D.weight c * tripleGapDet (D.atom e) (D.atom f) (D.atom c)
      + ∑ d ∈ Cᶜ, D.weight d * tripleGapDet (D.atom e) (D.atom f) (D.atom d)
      = 2 - leverageOf (D.atom e) - leverageOf (D.atom f) := by
    rw [Finset.sum_add_sum_compl]; exact hmoment
  rw [hinside] at hsplit
  linarith

/-- The quadratic form of an unweighted subset sum, as a total of squared readings. -/
theorem dotProduct_subsetSum_mulVec_sq (D : WeightedDesign m 3) (C : Finset (Fin m))
    (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (subsetSum D C *ᵥ probe) = ∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2 := by
  rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
    dotProduct_comm probe (D.atom c)]
  ring

/-- **THE CORNER IS AN UNWEIGHTED TIGHT FRAME ON ITS OWN PLANE.**  For every probe
orthogonal to the axis the three inside atoms resolve the probe exactly, with NO
weights: `sum_{c in C} <g_c,y>^2 = |y|^2`.  The corner is over-tight along the axis
and exactly tight on the plane, which is the sharpest structural statement the
corank-two stratum admits. -/
theorem corner_planeProbe_tight (D : WeightedDesign m 3) {C : Finset (Fin m)}
    {lam : ℝ} {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {y : Fin 3 → ℝ} (hperp : u ⬝ᵥ y = 0) :
    ∑ c ∈ C, (D.atom c ⬝ᵥ y) ^ 2 = y ⬝ᵥ y := by
  have hquad : y ⬝ᵥ ((subsetSum D C - 1) *ᵥ y) = lam * (u ⬝ᵥ y) ^ 2 := by
    rw [hgap, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul, dotProduct_comm y u]
    ring
  rw [hperp] at hquad
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_subsetSum_mulVec_sq D C y] at hquad
  have hcongr : ∑ c ∈ C, (D.atom c ⬝ᵥ y) ^ 2 = ∑ c ∈ C, (D.atom c ⬝ᵥ y) ^ 2 := rfl
  linarith [hquad]

/-- **THE AXIS CARRIES THE WHOLE CORANK.**  The three inside atoms read the axis to a
total of `1 + lam`.  With `Gtz.corner_planeProbe_tight` this pins the inside triple
completely: an orthonormal basis stretched along the axis by `sqrt(1 + lam)`. -/
theorem corner_axisProbe_total (D : WeightedDesign m 3) {C : Finset (Fin m)}
    {lam : ℝ} {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ∑ c ∈ C, (D.atom c ⬝ᵥ u) ^ 2 = 1 + lam := by
  have hquad : u ⬝ᵥ ((subsetSum D C - 1) *ᵥ u) = lam * (u ⬝ᵥ u) ^ 2 := by
    rw [hgap, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul]
    ring
  rw [hunit] at hquad
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_subsetSum_mulVec_sq D C u, hunit] at hquad
  linarith [hquad]

end Gtz

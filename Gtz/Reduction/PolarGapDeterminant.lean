/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.PolarShadowFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000

/-!
# The gap determinant: the kill margin is pole free

The arithmetic kill of the polar lane reads four bounds at a pole and a
triple: the shadow trace, the plane Gram determinant, the pole surplus and
the Schur test.  This file proves that the margin of the Schur test is the
leverage times the DETERMINANT of the gap matrix `subsetSum T - 1`, a
quantity that does not see the pole at all.  The pole is a certificate
frame and nothing more.

## 1. The gap determinant

`Gtz.polarGapDet` is a division-free polynomial in the atom pairings: the
squared bracket of the triple, minus the three pair Gram complements, plus
the three leverages, minus one.  `Gtz.subsetSum_triple_sub_one_det` proves
that it IS the determinant of `subsetSum {x, y, z} - 1`.

## 2. The frame identity

`Gtz.polarPlaneDet_mul_surplus_sub_adjugate`: at every pole of positive
leverage,

  `planeDet * (mass - leverage) - adjugate = leverage * polarGapDet`.

The left side is the margin of the arithmetic test.  Thus the SIGN of the
kill margin is the same at every pole.  The identity fails at the level of
free Gram scalars: its correction term is the four-atom Gram determinant,
which vanishes exactly because the atoms live in rank three.  The proof
works at coordinate level for that reason.

## 3. The excess is gone

`Gtz.exists_excess_of_trace_planeDet` manufactures the excess of the two
cover bounds from two strict inequalities: a shadow trace above two and a
positive plane determinant.  Thus `Gtz.not_isTie_of_planeInvariants` kills
the tie from FOUR SCALAR INEQUALITIES with no existential quantifier, and
`Gtz.not_isTie_of_polarGapDet` replaces the Schur test by the positivity of
the gap determinant.

## 4. The pole dissolves

`Gtz.posDef_of_planeShadowSchur` extracts the strict dominator from the
four bounds, and `Gtz.planeInvariants_of_posDef` runs the converse: a
strictly dominating triple satisfies the four bounds AT EVERY POLE of
positive leverage.  The composition
`Gtz.polarShadowSchur_pole_transport` transports the kill from any one pole
to every other pole.  The measured refusal poles of the predecessor are
membership artifacts: a pole refuses exactly when it sits inside every
determinant-positive triple, and the transported kill does not care.

## 5. The tie laws

At a tie the dominating triple is singular, thus
`Gtz.exists_polarGapDet_eq_zero_of_isTie`: EVERY TIE SITS ON THE
DETERMINANT HYPERSURFACE `polarGapDet = 0`.  The moment identities price
the whole determinant family: `Gtz.sum_weight_pairing_sq_total` is the
squared Parseval trace and `Gtz.sum_weight_tripleBracket_sq_total` is the
Cauchy-Binet law of a weighted Parseval frame,

  `∑ ∑ ∑ w w w * bracket ^ 2 = 6`,

proved with no determinant theory through the bracket transport
`Gtz.sum_weight_tripleBracket_sq_pair`.

## 6. The tenth narrowing

`Gtz.PolarGapSelection` asks for a pole and a triple with a shadow trace
above two, a positive plane determinant, a strict pole surplus and a
positive gap determinant — four scalar clauses, no excess, no adjugate.
`Gtz.PolarWrapGapSelection` pins the triple to a wrapping triple of the
circular order.  Each closes `Gtz.GtzWeighted 6 3` and
`Gtz.GtzWeightedAll 3` alone, each is false at size five, and the diamond
guardrail transports.

The probes calibrate the reformulation.  On the 3749 real near-tie
endpoints the four clauses agree with the landed kill at all 224940
pole-triple pairs, the manufactured excess never fails, and a wrapping
triple clears all four clauses at some pole of every endpoint.  The
weighted average of the gap determinant over the twenty triples is negative
at every endpoint, thus no averaging selection can close the residual: the
selection must consume the circular order.

## 7. The surplus clause is free

`Gtz.planeAdjugate_sos_law` writes the coupling adjugate times the coupling
excess as the plane determinant times the squared probe energy plus one
square, with the landed plane Cayley-Hamilton law as the only input.  Thus
`Gtz.polarShadowAdjugate_nonneg_of_cover`: the adjugate form is nonnegative
under any covered plane, and `Gtz.leverage_lt_of_gapCore` derives the strict
pole surplus from the other three clauses.  `Gtz.PolarGapCoreSelection` and
`Gtz.PolarWrapGapCoreSelection` are the residuals with THREE scalar clauses:
a shadow trace above two, a positive plane determinant and a positive gap
determinant.  Each closes the cell and all of rank three alone through
`Gtz.not_isTie_of_polarGapDetCore`, and each is false at size five.

## 8. The sharp form, and what it says about the route

`Gtz.posDef_iff_planeGapCore`: at every pole of positive leverage a triple
dominates strictly IF AND ONLY IF the three core clauses hold.  The core
target is therefore the sharpest form at this interface, and the polar
arithmetic residual is a faithful REFORMULATION of the deciding cell, not a
weakening of it.  What the chain has bought is a change of vocabulary --
from a spectral statement about a three by three matrix to three polynomial
inequalities in the pairings -- and the remaining content is the SELECTION
of the pole and the triple, which no bound can supply.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## Part 1: the gap determinant -/

section GapDet

/-- Three distinct labels form a card-three set. -/
theorem card_triple_eq {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ({x, y, z} : Finset (Fin m)).card = 3 := by
  have hx : x ∉ ({y, z} : Finset (Fin m)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hxy, hxz⟩
  have hy : y ∉ ({z} : Finset (Fin m)) := by
    simp only [Finset.mem_singleton]
    exact hyz
  rw [Finset.card_insert_of_notMem hx, Finset.card_insert_of_notMem hy,
    Finset.card_singleton]

/-- A sum over three distinct labels is the three-term total. -/
theorem sum_triple_eq {M : Type*} [AddCommMonoid M] {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (f : Fin m → M) :
    ∑ c ∈ ({x, y, z} : Finset (Fin m)), f c = f x + (f y + f z) := by
  have hx : x ∉ ({y, z} : Finset (Fin m)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hxy, hxz⟩
  have hy : y ∉ ({z} : Finset (Fin m)) := by
    simp only [Finset.mem_singleton]
    exact hyz
  rw [Finset.sum_insert hx, Finset.sum_insert hy, Finset.sum_singleton]

/-- **THE GAP DETERMINANT.**  A division-free polynomial in the pairings of a
triple of atoms: the squared bracket, minus the three pair Gram complements,
plus the three leverages, minus one.  It does not see any pole. -/
noncomputable def polarGapDet (design : WeightedDesign m 3) (x y z : Fin m) : ℝ :=
  tripleBracket (design.atom x) (design.atom y) (design.atom z) ^ 2
    - ((design.atom x ⬝ᵥ design.atom x) * (design.atom y ⬝ᵥ design.atom y)
        - (design.atom x ⬝ᵥ design.atom y) ^ 2)
    - ((design.atom y ⬝ᵥ design.atom y) * (design.atom z ⬝ᵥ design.atom z)
        - (design.atom y ⬝ᵥ design.atom z) ^ 2)
    - ((design.atom z ⬝ᵥ design.atom z) * (design.atom x ⬝ᵥ design.atom x)
        - (design.atom z ⬝ᵥ design.atom x) ^ 2)
    + (design.atom x ⬝ᵥ design.atom x) + (design.atom y ⬝ᵥ design.atom y)
    + (design.atom z ⬝ᵥ design.atom z) - 1

/-- The gap determinant is invariant under the cyclic turn of its triple. -/
theorem polarGapDet_cycle (design : WeightedDesign m 3) (x y z : Fin m) :
    polarGapDet design x y z = polarGapDet design y z x := by
  simp only [polarGapDet, tripleBracket_eq, dotProduct, Fin.sum_univ_three]
  ring

/-- The gap determinant is invariant under the swap of its last two labels. -/
theorem polarGapDet_swap (design : WeightedDesign m 3) (x y z : Fin m) :
    polarGapDet design x y z = polarGapDet design x z y := by
  simp only [polarGapDet, tripleBracket_eq, dotProduct, Fin.sum_univ_three]
  ring

/-- **THE GAP DETERMINANT IS THE DETERMINANT.**  The determinant of the gap
matrix of a triple is the gap determinant polynomial. -/
theorem subsetSum_triple_sub_one_det (design : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (subsetSum design ({x, y, z} : Finset (Fin m)) - 1).det
      = polarGapDet design x y z := by
  have hsum : subsetSum design ({x, y, z} : Finset (Fin m))
      = atomMatrix (design.atom x)
        + (atomMatrix (design.atom y) + atomMatrix (design.atom z)) :=
    sum_triple_eq hxy hxz hyz fun c => atomMatrix (design.atom c)
  rw [hsum, polarGapDet, Matrix.det_fin_three]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, atomMatrix,
    Matrix.vecMulVec_apply, tripleBracket_eq, dotProduct, Fin.sum_univ_three,
    Fin.reduceEq, reduceIte]
  ring

end GapDet

/-! ## Part 2: the frame identity

The margin of the arithmetic test at any pole is the leverage times the gap
determinant.  The identity holds at coordinate level only: at the level of
free Gram scalars its correction term is the Gram determinant of the four
atoms, which vanishes because the atoms live in rank three. -/

section FrameIdentity

/-- **THE FOUR-ATOM GRAM DETERMINANT VANISHES.**  Four vectors of rank three
are dependent, thus the expanded determinant of their Gram matrix is zero.
This is the rank constraint that separates the frame identity from its free
Gram scalar form. -/
theorem gramFour_read_vanishes (p u v w : Fin 3 → ℝ) :
    (p ⬝ᵥ p) * (u ⬝ᵥ u) * (v ⬝ᵥ v) * (w ⬝ᵥ w)
        - (p ⬝ᵥ p) * (u ⬝ᵥ u) * (v ⬝ᵥ w) ^ 2
        - (p ⬝ᵥ p) * (v ⬝ᵥ v) * (u ⬝ᵥ w) ^ 2
        - (p ⬝ᵥ p) * (w ⬝ᵥ w) * (u ⬝ᵥ v) ^ 2
        + 2 * (p ⬝ᵥ p) * (u ⬝ᵥ v) * (v ⬝ᵥ w) * (u ⬝ᵥ w)
        - (u ⬝ᵥ u) * (v ⬝ᵥ v) * (w ⬝ᵥ p) ^ 2
        - (u ⬝ᵥ u) * (w ⬝ᵥ w) * (v ⬝ᵥ p) ^ 2
        + 2 * (u ⬝ᵥ u) * (v ⬝ᵥ p) * (v ⬝ᵥ w) * (w ⬝ᵥ p)
        - (v ⬝ᵥ v) * (w ⬝ᵥ w) * (u ⬝ᵥ p) ^ 2
        + 2 * (v ⬝ᵥ v) * (u ⬝ᵥ p) * (w ⬝ᵥ p) * (u ⬝ᵥ w)
        + 2 * (w ⬝ᵥ w) * (u ⬝ᵥ p) * (u ⬝ᵥ v) * (v ⬝ᵥ p)
        + (u ⬝ᵥ p) ^ 2 * (v ⬝ᵥ w) ^ 2
        - 2 * (u ⬝ᵥ p) * (u ⬝ᵥ v) * (v ⬝ᵥ w) * (w ⬝ᵥ p)
        - 2 * (u ⬝ᵥ p) * (v ⬝ᵥ p) * (v ⬝ᵥ w) * (u ⬝ᵥ w)
        + (u ⬝ᵥ v) ^ 2 * (w ⬝ᵥ p) ^ 2
        - 2 * (u ⬝ᵥ v) * (v ⬝ᵥ p) * (w ⬝ᵥ p) * (u ⬝ᵥ w)
        + (v ⬝ᵥ p) ^ 2 * (u ⬝ᵥ w) ^ 2 = 0 := by
  simp only [dotProduct, Fin.sum_univ_three]
  ring

/-- **THE SCALAR MARGIN LAW.**  The margin of the arithmetic test, written in
free pairing scalars, is the leverage times the gap polynomial minus the
four-atom Gram determinant.  On rank-three data the correction term vanishes
and the frame identity follows. -/
theorem polarSchur_margin_scalar (L Lx Ly Lz txy tyz txz tx ty tz : ℝ)
    (hL : L ≠ 0) :
    (1 - ((Lx - tx ^ 2 / L) + ((Ly - ty ^ 2 / L) + (Lz - tz ^ 2 / L)))
        + (((Lx - tx ^ 2 / L) * (Lx - tx ^ 2 / L) - (Lx - tx * tx / L) ^ 2
            + (((Lx - tx ^ 2 / L) * (Ly - ty ^ 2 / L) - (txy - tx * ty / L) ^ 2)
              + ((Lx - tx ^ 2 / L) * (Lz - tz ^ 2 / L)
                - (txz - tx * tz / L) ^ 2)))
          + ((((Ly - ty ^ 2 / L) * (Lx - tx ^ 2 / L) - (txy - ty * tx / L) ^ 2)
              + ((Ly - ty ^ 2 / L) * (Ly - ty ^ 2 / L) - (Ly - ty * ty / L) ^ 2
                + ((Ly - ty ^ 2 / L) * (Lz - tz ^ 2 / L)
                  - (tyz - ty * tz / L) ^ 2)))
            + (((Lz - tz ^ 2 / L) * (Lx - tx ^ 2 / L) - (txz - tz * tx / L) ^ 2)
              + ((Lz - tz ^ 2 / L) * (Ly - ty ^ 2 / L) - (tyz - tz * ty / L) ^ 2
                + ((Lz - tz ^ 2 / L) * (Lz - tz ^ 2 / L)
                  - (Lz - tz * tz / L) ^ 2))))) / 2)
      * ((tx ^ 2 + (ty ^ 2 + tz ^ 2)) - L)
      - ((((Lx - tx ^ 2 / L) + ((Ly - ty ^ 2 / L) + (Lz - tz ^ 2 / L))) - 1)
          * (tx * tx * (Lx - tx * tx / L)
              + (tx * ty * (txy - tx * ty / L) + tx * tz * (txz - tx * tz / L))
            + ((ty * tx * (txy - ty * tx / L)
                + (ty * ty * (Ly - ty * ty / L)
                  + ty * tz * (tyz - ty * tz / L)))
              + (tz * tx * (txz - tz * tx / L)
                + (tz * ty * (tyz - tz * ty / L)
                  + tz * tz * (Lz - tz * tz / L)))))
        - ((tx * (Lx - tx * tx / L)
              + (ty * (txy - tx * ty / L) + tz * (txz - tx * tz / L))) ^ 2
          + ((tx * (txy - ty * tx / L)
              + (ty * (Ly - ty * ty / L) + tz * (tyz - ty * tz / L))) ^ 2
            + (tx * (txz - tz * tx / L)
              + (ty * (tyz - tz * ty / L) + tz * (Lz - tz * tz / L))) ^ 2)))
      = L * ((Lx * Ly * Lz + 2 * txy * tyz * txz - Lx * tyz ^ 2 - Ly * txz ^ 2
            - Lz * txy ^ 2)
          - (Lx * Ly - txy ^ 2) - (Ly * Lz - tyz ^ 2) - (Lz * Lx - txz ^ 2)
          + Lx + Ly + Lz - 1)
        - (L * Lx * Ly * Lz - L * Lx * tyz ^ 2 - L * Ly * txz ^ 2
          - L * Lz * txy ^ 2 + 2 * L * txy * tyz * txz
          - Lx * Ly * tz ^ 2 - Lx * Lz * ty ^ 2 + 2 * Lx * ty * tyz * tz
          - Ly * Lz * tx ^ 2 + 2 * Ly * tx * tz * txz + 2 * Lz * tx * txy * ty
          + tx ^ 2 * tyz ^ 2 - 2 * tx * txy * tyz * tz
          - 2 * tx * ty * tyz * txz + txy ^ 2 * tz ^ 2
          - 2 * txy * ty * tz * txz + ty ^ 2 * txz ^ 2) := by
  field_simp
  ring

/-- **THE KILL MARGIN IS THE GAP DETERMINANT.**  At every pole of positive
leverage and every triple of distinct labels,

  `planeDet * (mass - leverage) - adjugate = leverage * polarGapDet`.

The sign of the arithmetic test is thus the same at every pole: the pole is a
frame, not an ingredient. -/
theorem polarPlaneDet_mul_surplus_sub_adjugate (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    polarPlaneDet design pole ({x, y, z} : Finset (Fin m))
        * ((∑ c ∈ ({x, y, z} : Finset (Fin m)),
              (design.atom c ⬝ᵥ design.atom pole) ^ 2)
          - design.atom pole ⬝ᵥ design.atom pole)
      - polarShadowAdjugate design pole ({x, y, z} : Finset (Fin m))
      = (design.atom pole ⬝ᵥ design.atom pole) * polarGapDet design x y z := by
  have hL : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  have hexp : ∀ f : Fin m → ℝ,
      ∑ c ∈ ({x, y, z} : Finset (Fin m)), f c = f x + (f y + f z) :=
    fun f => sum_triple_eq hxy hxz hyz f
  rw [polarPlaneDet, polarShadowAdjugate, polarGapDet,
    tripleBracket_sq_eq_gramDet]
  simp only [hexp]
  simp only [planeShadowSq, planeShadowPairing]
  rw [dotProduct_comm (design.atom y) (design.atom x),
    dotProduct_comm (design.atom z) (design.atom y),
    dotProduct_comm (design.atom z) (design.atom x)]
  linear_combination
    polarSchur_margin_scalar (design.atom pole ⬝ᵥ design.atom pole)
        (design.atom x ⬝ᵥ design.atom x) (design.atom y ⬝ᵥ design.atom y)
        (design.atom z ⬝ᵥ design.atom z) (design.atom x ⬝ᵥ design.atom y)
        (design.atom y ⬝ᵥ design.atom z) (design.atom x ⬝ᵥ design.atom z)
        (design.atom x ⬝ᵥ design.atom pole) (design.atom y ⬝ᵥ design.atom pole)
        (design.atom z ⬝ᵥ design.atom pole) hL
      - gramFour_read_vanishes (design.atom pole) (design.atom x)
          (design.atom y) (design.atom z)

end FrameIdentity

/-! ## Part 3: the excess is gone

Two strict scalar inequalities manufacture the excess of the two cover
bounds, thus the kill runs on four scalar inequalities with no existential
quantifier. -/

section ExcessFree

/-- **THE MANUFACTURED EXCESS.**  A shadow trace above two and a positive
plane determinant supply an excess that clears both cover bounds.  The excess
is the smaller of `planeDet / (trace - 2)` and `(trace - 2) / 2`. -/
theorem exists_excess_of_trace_planeDet {S G : ℝ} (htrace : 2 < S)
    (hdet : 0 < 1 - S + G) :
    ∃ excess : ℝ, 0 < excess ∧ 2 * (1 + excess) ≤ S
      ∧ (1 + excess) * S - (1 + excess) ^ 2 ≤ G := by
  set excess := min ((1 - S + G) / (S - 2)) ((S - 2) / 2) with hexcess
  have hgap : (0 : ℝ) < S - 2 := by linarith
  have hpos : 0 < excess := lt_min (div_pos hdet hgap) (by linarith)
  have hhalf : excess ≤ (S - 2) / 2 := min_le_right _ _
  have hshare : excess * (S - 2) ≤ 1 - S + G := by
    have hle : excess ≤ (1 - S + G) / (S - 2) := min_le_left _ _
    rw [le_div_iff₀ hgap] at hle
    linarith
  exact ⟨excess, hpos, by linarith, by nlinarith [sq_nonneg excess]⟩

/-- **THE EXCESS-FREE KILL.**  Four scalar inequalities at a pole and a card
three subset kill the tie: a shadow trace above two, a positive plane
determinant, a strict pole surplus, and the arithmetic test. -/
theorem not_isTie_of_planeInvariants (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {selected : Finset (Fin m)} (hcard : selected.card = 3)
    (htrace : 2 < ∑ c ∈ selected, planeShadowSq design pole c)
    (hdet : 0 < polarPlaneDet design pole selected)
    (hz : design.atom pole ⬝ᵥ design.atom pole
        < ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
    (htest : polarShadowAdjugate design pole selected
        < polarPlaneDet design pole selected
          * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
            - design.atom pole ⬝ᵥ design.atom pole)) :
    ¬ IsTie design := by
  rw [polarPlaneDet_eq] at hdet
  obtain ⟨excess, hexcessPos, htraceCover, hgramCover⟩ :=
    exists_excess_of_trace_planeDet htrace hdet
  exact not_isTie_of_planeShadowSchur_rank_three design hpole hcard hexcessPos
    htraceCover hgramCover hz htest

/-- **THE GAP DETERMINANT KILL.**  The arithmetic test replaced by the
positivity of the pole-free gap determinant. -/
theorem not_isTie_of_polarGapDet (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (htrace : 2 < ∑ c ∈ ({x, y, z} : Finset (Fin m)), planeShadowSq design pole c)
    (hdet : 0 < polarPlaneDet design pole ({x, y, z} : Finset (Fin m)))
    (hz : design.atom pole ⬝ᵥ design.atom pole
        < ∑ c ∈ ({x, y, z} : Finset (Fin m)),
            (design.atom c ⬝ᵥ design.atom pole) ^ 2)
    (hgap : 0 < polarGapDet design x y z) :
    ¬ IsTie design := by
  have hident := polarPlaneDet_mul_surplus_sub_adjugate design hpole hxy hxz hyz
  have hmargin : 0 < (design.atom pole ⬝ᵥ design.atom pole)
      * polarGapDet design x y z := mul_pos hpole hgap
  exact not_isTie_of_planeInvariants design hpole (card_triple_eq hxy hxz hyz)
    htrace hdet hz (by linarith)

end ExcessFree

/-! ## Part 4: the strict dominator from the four bounds

The landed kill derives the strict dominator internally and spends it on the
tie.  This part extracts it, because the pole transport needs the dominator
itself. -/

section Dominator

/-- The quadratic read of a gap matrix. -/
theorem subsetSum_sub_one_read (design : WeightedDesign m 3)
    (selected : Finset (Fin m)) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe)
      = (∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    subsetSum_form_eq_sum_sq]

/-- **THE FOUR BOUNDS PRODUCE THE STRICT DOMINATOR.**  This is the landed kill
with the tie step removed. -/
theorem posDef_of_planeShadowSchur (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (selected : Finset (Fin m)) {excess : ℝ} (hexcessPos : 0 < excess)
    (htrace : 2 * (1 + excess) ≤ ∑ c ∈ selected, planeShadowSq design pole c)
    (hgram : (1 + excess) * (∑ c ∈ selected, planeShadowSq design pole c)
        - (1 + excess) ^ 2 ≤ polarPlaneGramDet design pole selected)
    (hz : design.atom pole ⬝ᵥ design.atom pole
        < ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
    (htest : polarShadowAdjugate design pole selected
        < polarPlaneDet design pole selected
          * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
            - design.atom pole ⬝ᵥ design.atom pole)) :
    (subsetSum design selected - 1).PosDef := by
  have hcover := polarPlaneCover_of_traceGramDet design hpole selected htrace hgram
  have hplaneDetPos := polarPlaneDet_pos_of_traceGramDet design pole selected
    hexcessPos htrace hgram
  have hkappa : 0 < (design.atom pole ⬝ᵥ design.atom pole)
      * polarPlaneDet design pole selected := mul_pos hpole hplaneDetPos
  have hVu : polarCouplingVec design pole selected
        ⬝ᵥ polarCrossWitnessVec design pole selected
      < ((design.atom pole ⬝ᵥ design.atom pole) * polarPlaneDet design pole selected)
        * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
          - design.atom pole ⬝ᵥ design.atom pole) := by
    rw [polarCouplingVec_dotProduct_polarCrossWitnessVec design hpole selected]
    calc (design.atom pole ⬝ᵥ design.atom pole)
          * polarShadowAdjugate design pole selected
        < (design.atom pole ⬝ᵥ design.atom pole)
            * (polarPlaneDet design pole selected
              * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
                - design.atom pole ⬝ᵥ design.atom pole)) :=
          mul_lt_mul_of_pos_left htest hpole
      _ = ((design.atom pole ⬝ᵥ design.atom pole)
              * polarPlaneDet design pole selected)
            * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
              - design.atom pole ⬝ᵥ design.atom pole) := by ring
  exact posDef_of_polarWitnessSchur_scaled design hpole hexcessPos hcover hz hkappa
    (polarCrossWitnessVec_dotProduct_pole design hpole selected)
    (polarCrossWitnessVec_witness design hpole selected) hVu

end Dominator

/-! ## Part 5: the pole dissolves

A strict dominator satisfies the four bounds at EVERY pole of positive
leverage.  The extraction reads the dominator at the quarter-turn frame of an
anchor of positive shadow, and the anchor exists because a dominator cannot
sit inside one line. -/

section Transport

/-- **THE ANCHOR EXISTS.**  A strict dominator holds a label of positive
shadow at every pole of positive leverage: if every shadow of the selected
set vanished, some plane probe would read the dominator negatively. -/
theorem exists_anchor_planeShadowSq_pos_of_posDef (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {selected : Finset (Fin m)}
    (hposDef : (subsetSum design selected - 1).PosDef) :
    ∃ anchor ∈ selected, 0 < planeShadowSq design pole anchor := by
  classical
  by_contra hcontra
  push Not at hcontra
  have hzero : ∀ c ∈ selected, planeShadowSq design pole c = 0 := fun c hc =>
    le_antisymm (hcontra c hc) (planeShadowSq_nonneg design pole c hpole)
  have hprobe : ∃ probe : Fin 3 → ℝ,
      probe ⬝ᵥ design.atom pole = 0 ∧ 0 < probe ⬝ᵥ probe := by
    set u0 := bracketNormal (design.atom pole) ![1, 0, 0] with hu0
    set u1 := bracketNormal (design.atom pole) ![0, 1, 0] with hu1
    set u2 := bracketNormal (design.atom pole) ![0, 0, 1] with hu2
    have henergy : (u0 ⬝ᵥ u0) + (u1 ⬝ᵥ u1) + (u2 ⬝ᵥ u2)
        = 2 * (design.atom pole ⬝ᵥ design.atom pole) := by
      rw [hu0, hu1, hu2, bracketNormal_lagrange, bracketNormal_lagrange,
        bracketNormal_lagrange]
      simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      ring
    have hcases : 0 < u0 ⬝ᵥ u0 ∨ 0 < u1 ⬝ᵥ u1 ∨ 0 < u2 ⬝ᵥ u2 := by
      by_contra hnone
      push Not at hnone
      have h0 := selfDotProduct_nonneg u0
      have h1 := selfDotProduct_nonneg u1
      have h2 := selfDotProduct_nonneg u2
      have := hnone.1
      have := hnone.2.1
      have := hnone.2.2
      linarith
    rcases hcases with hpos | hpos | hpos
    · exact ⟨u0, by rw [hu0]; exact bracketNormal_dotProduct_left _ _, hpos⟩
    · exact ⟨u1, by rw [hu1]; exact bracketNormal_dotProduct_left _ _, hpos⟩
    · exact ⟨u2, by rw [hu2]; exact bracketNormal_dotProduct_left _ _, hpos⟩
  obtain ⟨probe, hprobePole, hprobeEnergy⟩ := hprobe
  have hprobeNe : probe ≠ 0 := by
    intro hzero'
    rw [hzero', dotProduct_comm, dotProduct_zero] at hprobeEnergy
    exact lt_irrefl 0 hprobeEnergy
  have hread := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobeNe
  rw [star_trivial, subsetSum_sub_one_read design selected probe] at hread
  have hcap : ∀ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2 = 0 := by
    intro c hc
    have hshadow : design.atom c ⬝ᵥ probe
        = planeShadowVec design pole c ⬝ᵥ probe :=
      (planeShadowVec_dotProduct_polar design pole c hprobePole).symm
    have hcs := dotProduct_sq_le_mul_self (planeShadowVec design pole c) probe
    rw [planeShadowVec_dotProduct_self design hpole c, hzero c hc, zero_mul] at hcs
    have hnonneg := sq_nonneg (planeShadowVec design pole c ⬝ᵥ probe)
    rw [hshadow]
    linarith
  rw [Finset.sum_congr rfl hcap, Finset.sum_const_zero] at hread
  linarith

/-- **THE STRICT FRAME FORM.**  The dominator read at every nonzero frame
probe is strictly positive, thus the frame form of the cover converse is
strict at every nonzero coefficient pair. -/
theorem polarFrameForm_pos_of_posDef (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {anchor : Fin m} (hanchor : 0 < planeShadowSq design pole anchor)
    {selected : Finset (Fin m)}
    (hposDef : (subsetSum design selected - 1).PosDef)
    {alpha beta : ℝ} (hne : ¬ (alpha = 0 ∧ beta = 0)) :
    0 < alpha ^ 2 * (polarFramePairSq design pole anchor selected
          - planeShadowSq design pole anchor)
        + 2 * alpha * beta * polarFrameCross design pole anchor selected
      + beta ^ 2 * (polarFrameBracketSq design pole anchor selected
          - (design.atom pole ⬝ᵥ design.atom pole)
            * planeShadowSq design pole anchor) := by
  have hcoeff : 0 < alpha ^ 2 + beta ^ 2 * (design.atom pole ⬝ᵥ design.atom pole) := by
    rcases not_and_or.mp hne with halpha | hbeta
    · have := sq_pos_of_ne_zero halpha
      nlinarith [sq_nonneg beta, hpole]
    · have := sq_pos_of_ne_zero hbeta
      nlinarith [sq_nonneg alpha, hpole]
  have henergy := polarFrameProbe_dotProduct_self design hpole anchor alpha beta
  have hprobeNe : polarFrameProbe design pole anchor alpha beta ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_comm, dotProduct_zero] at henergy
    nlinarith [mul_pos hcoeff hanchor]
  have hread := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobeNe
  rw [star_trivial, subsetSum_sub_one_read design selected] at hread
  rw [henergy] at hread
  have hexpand : ∑ c ∈ selected,
      (design.atom c ⬝ᵥ polarFrameProbe design pole anchor alpha beta) ^ 2
      = alpha ^ 2 * polarFramePairSq design pole anchor selected
        + 2 * alpha * beta * polarFrameCross design pole anchor selected
        + beta ^ 2 * polarFrameBracketSq design pole anchor selected := by
    rw [polarFramePairSq, polarFrameCross, polarFrameBracketSq, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by
      rw [atom_dotProduct_polarFrameProbe design pole anchor d alpha beta]
      ring
  rw [hexpand] at hread
  nlinarith [hread]

/-- **THE SHADOW TRACE OF A DOMINATOR IS ABOVE TWO** at every pole of
positive leverage. -/
theorem sum_planeShadowSq_gt_two_of_posDef (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {selected : Finset (Fin m)}
    (hposDef : (subsetSum design selected - 1).PosDef) :
    2 < ∑ c ∈ selected, planeShadowSq design pole c := by
  obtain ⟨anchor, -, hanchor⟩ :=
    exists_anchor_planeShadowSq_pos_of_posDef design hpole hposDef
  have hone := polarFrameForm_pos_of_posDef design hpole hanchor hposDef
    (alpha := 1) (beta := 0) (by simp)
  have htwo := polarFrameForm_pos_of_posDef design hpole hanchor hposDef
    (alpha := 0) (beta := 1) (by simp)
  have hid := polarFrame_trace_identity design hpole anchor selected
  have hLsh : 0 < (design.atom pole ⬝ᵥ design.atom pole)
      * planeShadowSq design pole anchor := mul_pos hpole hanchor
  nlinarith [hone, htwo, hid, hLsh, hpole]

/-- **THE PLANE DETERMINANT OF A DOMINATOR IS POSITIVE** at every pole of
positive leverage. -/
theorem polarPlaneDet_pos_of_posDef (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {selected : Finset (Fin m)}
    (hposDef : (subsetSum design selected - 1).PosDef) :
    0 < polarPlaneDet design pole selected := by
  obtain ⟨anchor, -, hanchor⟩ :=
    exists_anchor_planeShadowSq_pos_of_posDef design hpole hposDef
  set diagOne := polarFramePairSq design pole anchor selected
    - planeShadowSq design pole anchor with hdiagOne
  set diagTwo := polarFrameBracketSq design pole anchor selected
    - (design.atom pole ⬝ᵥ design.atom pole) * planeShadowSq design pole anchor
    with hdiagTwo
  set cross := polarFrameCross design pole anchor selected with hcross
  have hone : 0 < diagOne := by
    have := polarFrameForm_pos_of_posDef design hpole hanchor hposDef
      (alpha := 1) (beta := 0) (by simp)
    nlinarith [this]
  have hdisc : cross ^ 2 < diagOne * diagTwo := by
    have hkey := polarFrameForm_pos_of_posDef design hpole hanchor hposDef
      (alpha := -cross) (beta := diagOne) (by
        intro hpair
        exact absurd hpair.2 (ne_of_gt hone))
    nlinarith [hkey, hone]
  have htraceId := polarFrame_trace_identity design hpole anchor selected
  have hgramId := polarFrame_gram_identity design hpole anchor selected
  have hscale : 0 < (design.atom pole ⬝ᵥ design.atom pole)
      * planeShadowSq design pole anchor ^ 2 := by positivity
  have hident : ((design.atom pole ⬝ᵥ design.atom pole)
        * planeShadowSq design pole anchor ^ 2)
      * (polarPlaneGramDet design pole selected
          - (∑ c ∈ selected, planeShadowSq design pole c) + 1)
      = diagOne * diagTwo - cross ^ 2 := by
    rw [hdiagOne, hdiagTwo, hcross]
    linear_combination hgramId - planeShadowSq design pole anchor * htraceId
  rw [polarPlaneDet_eq]
  nlinarith [hident, hdisc, hscale]

/-- **THE POLE SURPLUS OF A DOMINATOR IS STRICT** at every pole of positive
leverage. -/
theorem leverage_lt_sum_pairing_sq_of_posDef (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {selected : Finset (Fin m)}
    (hposDef : (subsetSum design selected - 1).PosDef) :
    design.atom pole ⬝ᵥ design.atom pole
      < ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2 := by
  have hpoleNe : design.atom pole ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hpole
    exact lt_irrefl 0 hpole
  have hread := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hpoleNe
  rw [star_trivial, subsetSum_sub_one_read design selected] at hread
  linarith

/-- **THE FOUR BOUNDS AT EVERY POLE.**  A strict dominator of three labels
satisfies the shadow trace bound, the plane determinant bound, the pole
surplus and the arithmetic test at EVERY pole of positive leverage. -/
theorem planeInvariants_of_posDef (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hposDef : (subsetSum design ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    2 < ∑ c ∈ ({x, y, z} : Finset (Fin m)), planeShadowSq design pole c
      ∧ 0 < polarPlaneDet design pole ({x, y, z} : Finset (Fin m))
      ∧ design.atom pole ⬝ᵥ design.atom pole
          < ∑ c ∈ ({x, y, z} : Finset (Fin m)),
              (design.atom c ⬝ᵥ design.atom pole) ^ 2
      ∧ polarShadowAdjugate design pole ({x, y, z} : Finset (Fin m))
          < polarPlaneDet design pole ({x, y, z} : Finset (Fin m))
            * ((∑ c ∈ ({x, y, z} : Finset (Fin m)),
                  (design.atom c ⬝ᵥ design.atom pole) ^ 2)
              - design.atom pole ⬝ᵥ design.atom pole) := by
  have hdet := hposDef.det_pos
  rw [subsetSum_triple_sub_one_det design hxy hxz hyz] at hdet
  have hident := polarPlaneDet_mul_surplus_sub_adjugate design hpole hxy hxz hyz
  have hmargin : 0 < (design.atom pole ⬝ᵥ design.atom pole)
      * polarGapDet design x y z := mul_pos hpole hdet
  exact ⟨sum_planeShadowSq_gt_two_of_posDef design hpole hposDef,
    polarPlaneDet_pos_of_posDef design hpole hposDef,
    leverage_lt_sum_pairing_sq_of_posDef design hpole hposDef, by linarith⟩

/-- The gap determinant of a strict dominator is positive. -/
theorem polarGapDet_pos_of_posDef (design : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hposDef : (subsetSum design ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    0 < polarGapDet design x y z := by
  have hdet := hposDef.det_pos
  rwa [subsetSum_triple_sub_one_det design hxy hxz hyz] at hdet

/-- **THE POLE TRANSPORT.**  The four bounds of the arithmetic kill at ONE
pole transport to EVERY pole of positive leverage.  The pole is a certificate
frame: a refusing pole is a pole that sits inside every strictly dominating
triple, and the kill selects another one. -/
theorem polarShadowSchur_pole_transport (design : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {poleA : Fin m} (hpoleA : 0 < design.atom poleA ⬝ᵥ design.atom poleA)
    {excess : ℝ} (hexcessPos : 0 < excess)
    (htrace : 2 * (1 + excess)
        ≤ ∑ c ∈ ({x, y, z} : Finset (Fin m)), planeShadowSq design poleA c)
    (hgram : (1 + excess)
          * (∑ c ∈ ({x, y, z} : Finset (Fin m)), planeShadowSq design poleA c)
        - (1 + excess) ^ 2
      ≤ polarPlaneGramDet design poleA ({x, y, z} : Finset (Fin m)))
    (hz : design.atom poleA ⬝ᵥ design.atom poleA
        < ∑ c ∈ ({x, y, z} : Finset (Fin m)),
            (design.atom c ⬝ᵥ design.atom poleA) ^ 2)
    (htest : polarShadowAdjugate design poleA ({x, y, z} : Finset (Fin m))
        < polarPlaneDet design poleA ({x, y, z} : Finset (Fin m))
          * ((∑ c ∈ ({x, y, z} : Finset (Fin m)),
                (design.atom c ⬝ᵥ design.atom poleA) ^ 2)
            - design.atom poleA ⬝ᵥ design.atom poleA))
    {poleB : Fin m} (hpoleB : 0 < design.atom poleB ⬝ᵥ design.atom poleB) :
    2 < ∑ c ∈ ({x, y, z} : Finset (Fin m)), planeShadowSq design poleB c
      ∧ 0 < polarPlaneDet design poleB ({x, y, z} : Finset (Fin m))
      ∧ design.atom poleB ⬝ᵥ design.atom poleB
          < ∑ c ∈ ({x, y, z} : Finset (Fin m)),
              (design.atom c ⬝ᵥ design.atom poleB) ^ 2
      ∧ polarShadowAdjugate design poleB ({x, y, z} : Finset (Fin m))
          < polarPlaneDet design poleB ({x, y, z} : Finset (Fin m))
            * ((∑ c ∈ ({x, y, z} : Finset (Fin m)),
                  (design.atom c ⬝ᵥ design.atom poleB) ^ 2)
              - design.atom poleB ⬝ᵥ design.atom poleB) :=
  planeInvariants_of_posDef design hpoleB hxy hxz hyz
    (posDef_of_planeShadowSchur design hpoleA ({x, y, z} : Finset (Fin m))
      hexcessPos htrace hgram hz htest)

end Transport

/-! ## Part 6: the tie laws and the moment identities

Every tie sits on the determinant hypersurface, and the weighted moments of
the determinant family are Parseval facts. -/

section TieLaws

variable {size rank : ℕ}

/-- **THE TIE SITS ON THE DETERMINANT HYPERSURFACE.**  The dominating triple
of a tie of rank three has gap determinant exactly zero. -/
theorem exists_polarGapDet_eq_zero_of_isTie (design : WeightedDesign m 3)
    (htie : IsTie design) :
    ∃ x y z : Fin m, x ≠ y ∧ x ≠ z ∧ y ≠ z
      ∧ Dominates design ({x, y, z} : Finset (Fin m))
      ∧ polarGapDet design x y z = 0 := by
  obtain ⟨dominating, hcard, hdom⟩ := htie.1
  obtain ⟨x, y, z, hxy, hxz, hyz, hset⟩ := Finset.card_eq_three.mp hcard
  subst hset
  refine ⟨x, y, z, hxy, hxz, hyz, hdom, ?_⟩
  have hnotPD := htie.2 ({x, y, z} : Finset (Fin m)) (card_triple_eq hxy hxz hyz)
  have hdetZero : (subsetSum design ({x, y, z} : Finset (Fin m)) - 1).det = 0 := by
    by_contra hne
    exact hnotPD (hdom.posDef_iff_det_ne_zero.mpr hne)
  rwa [subsetSum_triple_sub_one_det design hxy hxz hyz] at hdetZero

/-- **THE SQUARED PARSEVAL TRACE.**  The doubly weighted squared pairings of
a design total the rank. -/
theorem sum_weight_pairing_sq_total (design : WeightedDesign size rank) :
    ∑ c, ∑ d, design.weight c * design.weight d
        * (design.atom c ⬝ᵥ design.atom d) ^ 2 = (rank : ℝ) := by
  have hinner : ∀ c : Fin size,
      ∑ d, design.weight c * design.weight d
          * (design.atom c ⬝ᵥ design.atom d) ^ 2
        = design.weight c * (design.atom c ⬝ᵥ design.atom c) := by
    intro c
    have hrow := sum_weight_polarPairing_sq design c
    calc ∑ d, design.weight c * design.weight d
          * (design.atom c ⬝ᵥ design.atom d) ^ 2
        = design.weight c * ∑ d, design.weight d
            * (design.atom d ⬝ᵥ design.atom c) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun d _ => by
            rw [dotProduct_comm (design.atom c) (design.atom d)]
            ring
      _ = design.weight c * (design.atom c ⬝ᵥ design.atom c) := by rw [hrow]
  rw [Finset.sum_congr rfl fun c _ => hinner c]
  have hleverage := sum_weighted_leverage design
  rw [← hleverage]
  exact Finset.sum_congr rfl fun c _ => by rw [leverageOf_eq_dotProduct]

/-- **THE BRACKET TRANSPORT.**  The weighted squared brackets of a fixed pair
against every atom total the pair's Gram complement.  This is the inner layer
of the Cauchy-Binet law, and it needs no determinant theory: one application
of the pair transport of Parseval collapses the bracket square. -/
theorem sum_weight_tripleBracket_sq_pair (design : WeightedDesign m 3)
    (x y : Fin m) :
    ∑ e, design.weight e
        * tripleBracket (design.atom x) (design.atom y) (design.atom e) ^ 2
      = (design.atom x ⬝ᵥ design.atom x) * (design.atom y ⬝ᵥ design.atom y)
        - (design.atom x ⬝ᵥ design.atom y) ^ 2 := by
  have hterm : ∀ e : Fin m,
      design.weight e
          * tripleBracket (design.atom x) (design.atom y) (design.atom e) ^ 2
        = (design.atom x ⬝ᵥ design.atom x) * (design.atom y ⬝ᵥ design.atom y)
            * (design.weight e * (design.atom e ⬝ᵥ design.atom e))
          + (2 * (design.atom x ⬝ᵥ design.atom y))
            * (design.weight e * ((design.atom e ⬝ᵥ design.atom x)
                * (design.atom e ⬝ᵥ design.atom y)))
          - (design.atom x ⬝ᵥ design.atom x)
            * (design.weight e * (design.atom e ⬝ᵥ design.atom y) ^ 2)
          - (design.atom y ⬝ᵥ design.atom y)
            * (design.weight e * (design.atom e ⬝ᵥ design.atom x) ^ 2)
          - (design.atom x ⬝ᵥ design.atom y) ^ 2
            * (design.weight e * (design.atom e ⬝ᵥ design.atom e)) := by
    intro e
    rw [tripleBracket_sq_eq_gramDet]
    rw [dotProduct_comm (design.atom x) (design.atom e),
      dotProduct_comm (design.atom y) (design.atom e)]
    ring
  rw [Finset.sum_congr rfl fun e _ => hterm e]
  have hmass : ∑ e, design.weight e * (design.atom e ⬝ᵥ design.atom e)
      = (3 : ℝ) := by
    calc ∑ e, design.weight e * (design.atom e ⬝ᵥ design.atom e)
        = ∑ e, design.weight e * leverageOf (design.atom e) :=
          Finset.sum_congr rfl fun e _ => by rw [leverageOf_eq_dotProduct]
      _ = ((3 : ℕ) : ℝ) := sum_weighted_leverage design
      _ = (3 : ℝ) := by norm_num
  have hpair : ∑ e, design.weight e * ((design.atom e ⬝ᵥ design.atom x)
        * (design.atom e ⬝ᵥ design.atom y))
      = design.atom x ⬝ᵥ design.atom y :=
    (dotProduct_eq_sum_weight_mul_pair design (design.atom x)
      (design.atom y)).symm
  have hrowX := sum_weight_polarPairing_sq design x
  have hrowY := sum_weight_polarPairing_sq design y
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hmass, hpair, hrowX, hrowY]
  ring

/-- **THE CAUCHY-BINET LAW OF A WEIGHTED PARSEVAL FRAME.**  The triply
weighted squared brackets of a rank-three design total six.  Two layers of
transport prove it with no determinant theory. -/
theorem sum_weight_tripleBracket_sq_total (design : WeightedDesign m 3) :
    ∑ x, ∑ y, ∑ e, design.weight x * design.weight y * design.weight e
        * tripleBracket (design.atom x) (design.atom y) (design.atom e) ^ 2
      = 6 := by
  have hinner : ∀ x y : Fin m,
      ∑ e, design.weight x * design.weight y * design.weight e
          * tripleBracket (design.atom x) (design.atom y) (design.atom e) ^ 2
        = design.weight x * design.weight y
          * ((design.atom x ⬝ᵥ design.atom x) * (design.atom y ⬝ᵥ design.atom y)
            - (design.atom x ⬝ᵥ design.atom y) ^ 2) := by
    intro x y
    rw [← sum_weight_tripleBracket_sq_pair design x y, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y _ => hinner x y]
  have hsplit : ∀ x y : Fin m,
      design.weight x * design.weight y
          * ((design.atom x ⬝ᵥ design.atom x) * (design.atom y ⬝ᵥ design.atom y)
            - (design.atom x ⬝ᵥ design.atom y) ^ 2)
        = (design.weight x * (design.atom x ⬝ᵥ design.atom x))
            * (design.weight y * (design.atom y ⬝ᵥ design.atom y))
          - design.weight x * design.weight y
            * (design.atom x ⬝ᵥ design.atom y) ^ 2 := fun x y => by ring
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hsplit x y]
  have hmass : ∑ e : Fin m, design.weight e * (design.atom e ⬝ᵥ design.atom e)
      = (3 : ℝ) := by
    calc ∑ e, design.weight e * (design.atom e ⬝ᵥ design.atom e)
        = ∑ e, design.weight e * leverageOf (design.atom e) :=
          Finset.sum_congr rfl fun e _ => by rw [leverageOf_eq_dotProduct]
      _ = ((3 : ℕ) : ℝ) := sum_weighted_leverage design
      _ = (3 : ℝ) := by norm_num
  have hsq := sum_weight_pairing_sq_total design
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hmass, hsq]
  norm_num

/-- **THE PAIR GRAM MOMENT.**  The doubly weighted pair Gram complements of a
design total `rank ^ 2 - rank`.  With the trace and the Cauchy-Binet law this
completes the moment triple of the determinant family. -/
theorem sum_weight_gram_pair_total (design : WeightedDesign size rank) :
    ∑ c, ∑ d, design.weight c * design.weight d
        * ((design.atom c ⬝ᵥ design.atom c) * (design.atom d ⬝ᵥ design.atom d)
          - (design.atom c ⬝ᵥ design.atom d) ^ 2)
      = (rank : ℝ) ^ 2 - (rank : ℝ) := by
  have hmass : ∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom c)
      = (rank : ℝ) := by
    calc ∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom c)
        = ∑ c, design.weight c * leverageOf (design.atom c) :=
          Finset.sum_congr rfl fun c _ => by rw [leverageOf_eq_dotProduct]
      _ = (rank : ℝ) := sum_weighted_leverage design
  have hsq := sum_weight_pairing_sq_total design
  have hsplit : ∀ c d : Fin size,
      design.weight c * design.weight d
          * ((design.atom c ⬝ᵥ design.atom c) * (design.atom d ⬝ᵥ design.atom d)
            - (design.atom c ⬝ᵥ design.atom d) ^ 2)
        = (design.weight c * (design.atom c ⬝ᵥ design.atom c))
            * (design.weight d * (design.atom d ⬝ᵥ design.atom d))
          - design.weight c * design.weight d
            * (design.atom c ⬝ᵥ design.atom d) ^ 2 := fun c d => by ring
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => hsplit c d]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hmass, hsq]
  ring

/-- **THE ARITHMETIC TIE LAW IN INVARIANT FORM.**  At a tie, every pole of
positive leverage and every triple of distinct labels refuse one of the four
clauses: the shadow trace stays at two, the plane determinant closes, the
pole mass stays at the leverage, or the gap determinant closes. -/
theorem isTie_planeInvariants_alternative (design : WeightedDesign m 3)
    (htie : IsTie design) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∑ c ∈ ({x, y, z} : Finset (Fin m)), planeShadowSq design pole c ≤ 2
      ∨ polarPlaneDet design pole ({x, y, z} : Finset (Fin m)) ≤ 0
      ∨ ∑ c ∈ ({x, y, z} : Finset (Fin m)),
          (design.atom c ⬝ᵥ design.atom pole) ^ 2
            ≤ design.atom pole ⬝ᵥ design.atom pole
      ∨ polarGapDet design x y z ≤ 0 := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨htrace, hdet, hz, hgap⟩ := hcontra
  exact not_isTie_of_polarGapDet design hpole hxy hxz hyz htrace hdet hz hgap
    htie

/-- **THE SHARPEST SINGLE READING.**  At a tie, a triple that clears the two
cover invariants and the pole surplus has a nonpositive gap determinant. -/
theorem polarGapDet_nonpos_of_isTie (design : WeightedDesign m 3)
    (htie : IsTie design) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (htrace : 2 < ∑ c ∈ ({x, y, z} : Finset (Fin m)), planeShadowSq design pole c)
    (hdet : 0 < polarPlaneDet design pole ({x, y, z} : Finset (Fin m)))
    (hz : design.atom pole ⬝ᵥ design.atom pole
        < ∑ c ∈ ({x, y, z} : Finset (Fin m)),
            (design.atom c ⬝ᵥ design.atom pole) ^ 2) :
    polarGapDet design x y z ≤ 0 := by
  by_contra hgap
  push Not at hgap
  exact not_isTie_of_polarGapDet design hpole hxy hxz hyz htrace hdet hz hgap
    htie

end TieLaws

/-! ## Part 7: the tenth narrowing

The selection target in gap determinant form: four scalar clauses, no
excess, no adjugate.  The wrapping variant pins the triple to the circular
order.  Each closes the deciding cell and all of rank three alone. -/

section GapSelection

variable {size : ℕ}

/-- **THE GAP SELECTION TARGET.**  At every primitive tie of rank three some
pole of leverage above one and some triple of distinct labels carry a shadow
trace above two, a positive plane determinant, a strict pole surplus and a
positive gap determinant. -/
def PolarGapSelection (size : ℕ) : Prop :=
  ∀ design : WeightedDesign size 3, IsPrimitiveDesign design → IsTie design →
    ∃ pole x y z : Fin size,
      1 < design.atom pole ⬝ᵥ design.atom pole
        ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z
        ∧ 2 < ∑ c ∈ ({x, y, z} : Finset (Fin size)), planeShadowSq design pole c
        ∧ 0 < polarPlaneDet design pole ({x, y, z} : Finset (Fin size))
        ∧ design.atom pole ⬝ᵥ design.atom pole
            < ∑ c ∈ ({x, y, z} : Finset (Fin size)),
                (design.atom c ⬝ᵥ design.atom pole) ^ 2
        ∧ 0 < polarGapDet design x y z

/-- **THE WRAPPING GAP TARGET.**  The gap selection target with the triple
pinned to a wrapping triple of the circular order.  The probes read it: a
wrapping triple clears all four clauses at some pole of every measured
endpoint. -/
def PolarWrapGapSelection (size : ℕ) : Prop :=
  ∀ design : WeightedDesign size 3, IsPrimitiveDesign design → IsTie design →
    ∃ pole x y z : Fin size,
      1 < design.atom pole ⬝ᵥ design.atom pole
        ∧ PolarWrapping design pole x y z
        ∧ 2 < ∑ c ∈ ({x, y, z} : Finset (Fin size)), planeShadowSq design pole c
        ∧ 0 < polarPlaneDet design pole ({x, y, z} : Finset (Fin size))
        ∧ design.atom pole ⬝ᵥ design.atom pole
            < ∑ c ∈ ({x, y, z} : Finset (Fin size)),
                (design.atom c ⬝ᵥ design.atom pole) ^ 2
        ∧ 0 < polarGapDet design x y z

/-- The gap target implies the arithmetic selection target: the excess is
manufactured and the test is the frame identity. -/
theorem polarShadowSchurSelection_of_polarGapSelection
    (hgap : PolarGapSelection size) : PolarShadowSchurSelection size := by
  intro design hprimitive htie
  obtain ⟨pole, x, y, z, hlong, hxy, hxz, hyz, htrace, hdet, hz, hgapPos⟩ :=
    hgap design hprimitive htie
  have hpole : 0 < design.atom pole ⬝ᵥ design.atom pole :=
    lt_trans zero_lt_one hlong
  have hdet' := hdet
  rw [polarPlaneDet_eq] at hdet'
  obtain ⟨excess, hexcessPos, htraceCover, hgramCover⟩ :=
    exists_excess_of_trace_planeDet htrace hdet'
  have hident := polarPlaneDet_mul_surplus_sub_adjugate design hpole hxy hxz hyz
  have hmargin : 0 < (design.atom pole ⬝ᵥ design.atom pole)
      * polarGapDet design x y z := mul_pos hpole hgapPos
  exact ⟨pole, ({x, y, z} : Finset (Fin size)), excess, hlong,
    card_triple_eq hxy hxz hyz, hexcessPos, htraceCover, hgramCover, hz,
    by linarith⟩

/-- The wrapping gap target implies the landed wrapping kill target. -/
theorem polarWrapSelection_of_polarWrapGapSelection
    (hwrap : PolarWrapGapSelection size) : PolarWrapSelection size := by
  intro design hprimitive htie
  obtain ⟨pole, x, y, z, hlong, hwrapping, htrace, hdet, hz, hgapPos⟩ :=
    hwrap design hprimitive htie
  have hpole : 0 < design.atom pole ⬝ᵥ design.atom pole :=
    lt_trans zero_lt_one hlong
  have hxy := polarWrapping_ne_first_second design hpole hwrapping
  have hxz := polarWrapping_ne_first_third design hpole hwrapping
  have hyz := polarWrapping_ne_second_third design hpole hwrapping
  have hdet' := hdet
  rw [polarPlaneDet_eq] at hdet'
  obtain ⟨excess, hexcessPos, htraceCover, hgramCover⟩ :=
    exists_excess_of_trace_planeDet htrace hdet'
  have hident := polarPlaneDet_mul_surplus_sub_adjugate design hpole hxy hxz hyz
  have hmargin : 0 < (design.atom pole ⬝ᵥ design.atom pole)
      * polarGapDet design x y z := mul_pos hpole hgapPos
  exact ⟨pole, x, y, z, excess, hlong, hwrapping, hexcessPos, htraceCover,
    hgramCover, hz, by linarith⟩

/-- The wrapping gap target implies the gap target. -/
theorem polarGapSelection_of_polarWrapGapSelection
    (hwrap : PolarWrapGapSelection size) : PolarGapSelection size := by
  intro design hprimitive htie
  obtain ⟨pole, x, y, z, hlong, hwrapping, htrace, hdet, hz, hgapPos⟩ :=
    hwrap design hprimitive htie
  have hpole : 0 < design.atom pole ⬝ᵥ design.atom pole :=
    lt_trans zero_lt_one hlong
  exact ⟨pole, x, y, z, hlong,
    polarWrapping_ne_first_second design hpole hwrapping,
    polarWrapping_ne_first_third design hpole hwrapping,
    polarWrapping_ne_second_third design hpole hwrapping,
    htrace, hdet, hz, hgapPos⟩

/-- The hinge from the gap target. -/
theorem hingeHoldsAtSize_of_polarGapSelection
    (hgap : PolarGapSelection size) : HingeHoldsAtSize size 3 :=
  hingeHoldsAtSize_of_polarShadowSchurSelection
    (polarShadowSchurSelection_of_polarGapSelection hgap)

/-- **THE DECIDING CELL FROM THE GAP TARGET ALONE.** -/
theorem gtzWeighted_six_three_of_polarGapSelection
    (hgap : PolarGapSelection 6) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_polarShadowSchurSelection
    (polarShadowSchurSelection_of_polarGapSelection hgap)

/-- **ALL OF RANK THREE FROM THE GAP TARGET ALONE.** -/
theorem gtzWeightedAll_three_of_polarGapSelection
    (hgap : PolarGapSelection 6) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_polarShadowSchurSelection
    (polarShadowSchurSelection_of_polarGapSelection hgap)

/-- **THE DECIDING CELL FROM THE WRAPPING GAP TARGET ALONE.** -/
theorem gtzWeighted_six_three_of_polarWrapGapSelection
    (hwrap : PolarWrapGapSelection 6) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_polarWrapSelection
    (polarWrapSelection_of_polarWrapGapSelection hwrap)

/-- **ALL OF RANK THREE FROM THE WRAPPING GAP TARGET ALONE.** -/
theorem gtzWeightedAll_three_of_polarWrapGapSelection
    (hwrap : PolarWrapGapSelection 6) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_polarWrapSelection
    (polarWrapSelection_of_polarWrapGapSelection hwrap)

/-- The gap target is false at size five, thus the calibration transports. -/
theorem not_polarGapSelection_five : ¬ PolarGapSelection 5 :=
  fun hgap => not_polarShadowSchurSelection_five
    (polarShadowSchurSelection_of_polarGapSelection hgap)

/-- The wrapping gap target is false at size five. -/
theorem not_polarWrapGapSelection_five : ¬ PolarWrapGapSelection 5 :=
  fun hwrap => not_polarWrapSelection_five
    (polarWrapSelection_of_polarWrapGapSelection hwrap)

/-- **THE GUARDRAIL ON THE GAP ROUTES.**  The `(6,3)` tie in the tree is not
primitive, thus it touches neither target, and the size-five instances stay
refuted. -/
theorem sixSplitDiamondDesign_spares_polarGapSelection :
    ¬ RankSuccShrinks 6 3 ∧ IsTie sixSplitDiamondDesign
      ∧ ¬ IsPrimitiveDesign sixSplitDiamondDesign
      ∧ ¬ PolarGapSelection 5 ∧ ¬ PolarWrapGapSelection 5 :=
  ⟨not_rankSuccShrinks_six_three, sixSplitDiamondDesign_isTie,
    not_isPrimitiveDesign_sixSplitDiamondDesign, not_polarGapSelection_five,
    not_polarWrapGapSelection_five⟩

end GapSelection

/-! ## Part 8: the surplus clause is free

The pole surplus of the gap targets follows from the other three clauses.
The engine is one product law: the coupling adjugate times the coupling
excess is the plane determinant times the squared coupling energy, plus one
square.  The law is a scalar consequence of the landed plane Cayley-Hamilton
identity and of the Lagrange identity of the cross product, thus the proof
carries no new polynomial work. -/

section SurplusFree

/-- A plane probe reads the survivor plane form as its own squared atom
readings. -/
theorem planeReadVec_dotProduct_read (design : WeightedDesign m 3)
    (pole : Fin m) (selected : Finset (Fin m)) {probe : Fin 3 → ℝ}
    (hprobe : probe ⬝ᵥ design.atom pole = 0) :
    probe ⬝ᵥ planeReadVec design pole selected probe
      = ∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2 := by
  rw [planeReadVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [dotProduct_smul, smul_eq_mul,
    dotProduct_comm probe (planeShadowVec design pole d),
    planeShadowVec_dotProduct_polar design pole d hprobe]
  ring

/-- **THE ENERGY OF THE PLANE READ.**  The Cayley-Hamilton law of the
survivor plane form read at the probe: the energy of the plane read is the
shadow trace times the reading, minus the plane Gram determinant times the
energy of the probe. -/
theorem planeReadVec_norm_read (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (selected : Finset (Fin m)) {probe : Fin 3 → ℝ}
    (hprobe : probe ⬝ᵥ design.atom pole = 0) :
    planeReadVec design pole selected probe
        ⬝ᵥ planeReadVec design pole selected probe
      = (∑ c ∈ selected, planeShadowSq design pole c)
          * (probe ⬝ᵥ planeReadVec design pole selected probe)
        - polarPlaneGramDet design pole selected * (probe ⬝ᵥ probe) := by
  have hreadPole : planeReadVec design pole selected probe ⬝ᵥ design.atom pole
      = 0 := planeReadVec_dotProduct_pole design hpole selected probe
  have hsymm := planeReadVec_dotProduct_symm design pole selected hprobe hreadPole
  have hch := planeReadVec_planeReadVec design hpole selected hprobe
  calc planeReadVec design pole selected probe
        ⬝ᵥ planeReadVec design pole selected probe
      = probe ⬝ᵥ planeReadVec design pole selected
          (planeReadVec design pole selected probe) := by rw [← hsymm]
    _ = probe ⬝ᵥ ((∑ c ∈ selected, planeShadowSq design pole c)
            • planeReadVec design pole selected probe
          - polarPlaneGramDet design pole selected • probe) := by rw [hch]
    _ = (∑ c ∈ selected, planeShadowSq design pole c)
          * (probe ⬝ᵥ planeReadVec design pole selected probe)
        - polarPlaneGramDet design pole selected * (probe ⬝ᵥ probe) := by
        rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul,
          smul_eq_mul]

/-- **THE ADJUGATE PRODUCT LAW.**  The coupling adjugate times the coupling
excess is the plane determinant times the squared probe energy, plus the
squared cross product of the probe with its plane read.  This is the
two-dimensional adjugate positivity, written with no eigenvalue. -/
theorem planeAdjugate_sos_law (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (selected : Finset (Fin m)) {probe : Fin 3 → ℝ}
    (hprobe : probe ⬝ᵥ design.atom pole = 0) :
    (((∑ c ∈ selected, planeShadowSq design pole c) - 1) * (probe ⬝ᵥ probe)
        - ∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2)
      * ((∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)
      = polarPlaneDet design pole selected * (probe ⬝ᵥ probe) ^ 2
        + bracketNormal probe (planeReadVec design pole selected probe)
          ⬝ᵥ bracketNormal probe (planeReadVec design pole selected probe) := by
  have hread := planeReadVec_dotProduct_read design pole selected hprobe
  have hnorm := planeReadVec_norm_read design hpole selected hprobe
  have hlagrange := bracketNormal_lagrange probe
    (planeReadVec design pole selected probe)
    (planeReadVec design pole selected probe)
  rw [hlagrange, hnorm, hread, polarPlaneDet_eq]
  ring

/-- **THE COUPLING ADJUGATE IS NONNEGATIVE UNDER A COVER.**  A plane cover
with a positive excess makes the shadow adjugate form nonnegative: the
product law supplies the sign and the cover keeps the excess factor
positive. -/
theorem polarShadowAdjugate_nonneg_of_cover (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (selected : Finset (Fin m)) {excess : ℝ} (hexcessPos : 0 < excess)
    (hcover : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + excess) * (probe ⬝ᵥ probe)
        ≤ ∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2)
    (hdet : 0 < polarPlaneDet design pole selected) :
    0 ≤ polarShadowAdjugate design pole selected := by
  have hVpole : polarCouplingVec design pole selected ⬝ᵥ design.atom pole = 0 :=
    polarCouplingVec_dotProduct_pole design hpole selected
  have hsos := planeAdjugate_sos_law design hpole selected hVpole
  have hcoverV := hcover (polarCouplingVec design pole selected) hVpole
  have hadj := polarShadowAdjugate_eq_coupling design hpole selected
  have hVnonneg : (0 : ℝ) ≤ polarCouplingVec design pole selected
      ⬝ᵥ polarCouplingVec design pole selected :=
    selfDotProduct_nonneg (polarCouplingVec design pole selected)
  rcases eq_or_lt_of_le hVnonneg with hzero | hpos
  · have hVzero : polarCouplingVec design pole selected = 0 :=
      eq_zero_of_dotProduct_self_eq_zero hzero.symm
    rw [hadj, hVzero]
    simp
  · have hgap : 0 < (∑ c ∈ selected,
          (design.atom c ⬝ᵥ polarCouplingVec design pole selected) ^ 2)
        - polarCouplingVec design pole selected
            ⬝ᵥ polarCouplingVec design pole selected := by
      nlinarith [hcoverV, hpos, hexcessPos]
    have hsq := selfDotProduct_nonneg
      (bracketNormal (polarCouplingVec design pole selected)
        (planeReadVec design pole selected
          (polarCouplingVec design pole selected)))
    have hprod : 0 ≤ ((∑ c ∈ selected, planeShadowSq design pole c) - 1)
          * (polarCouplingVec design pole selected
              ⬝ᵥ polarCouplingVec design pole selected)
        - ∑ c ∈ selected,
            (design.atom c ⬝ᵥ polarCouplingVec design pole selected) ^ 2 := by
      nlinarith [hsos, hsq, hdet, hpos, hgap]
    rw [hadj]
    linarith


/-- **THE SURPLUS IS FREE.**  A shadow trace above two, a positive plane
determinant and a positive gap determinant force the strict pole surplus:
the frame identity writes the surplus as the gap determinant plus the
adjugate over the plane determinant, and both are nonnegative. -/
theorem leverage_lt_of_gapCore (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (htrace : 2 < ∑ c ∈ ({x, y, z} : Finset (Fin m)), planeShadowSq design pole c)
    (hdet : 0 < polarPlaneDet design pole ({x, y, z} : Finset (Fin m)))
    (hgap : 0 < polarGapDet design x y z) :
    design.atom pole ⬝ᵥ design.atom pole
      < ∑ c ∈ ({x, y, z} : Finset (Fin m)),
          (design.atom c ⬝ᵥ design.atom pole) ^ 2 := by
  have hdet' := hdet
  rw [polarPlaneDet_eq] at hdet'
  obtain ⟨excess, hexcessPos, htraceCover, hgramCover⟩ :=
    exists_excess_of_trace_planeDet htrace hdet'
  have hcover := polarPlaneCover_of_traceGramDet design hpole
    ({x, y, z} : Finset (Fin m)) htraceCover hgramCover
  have hadjNonneg := polarShadowAdjugate_nonneg_of_cover design hpole
    ({x, y, z} : Finset (Fin m)) hexcessPos hcover hdet
  have hident := polarPlaneDet_mul_surplus_sub_adjugate design hpole hxy hxz hyz
  have hmargin : 0 < (design.atom pole ⬝ᵥ design.atom pole)
      * polarGapDet design x y z := mul_pos hpole hgap
  nlinarith [hident, hmargin, hadjNonneg, hdet]

/-- **THE THREE-CLAUSE KILL.**  A pole of positive leverage and a triple of
distinct labels with a shadow trace above two, a positive plane determinant
and a positive gap determinant kill the tie.  The pole surplus is derived,
not assumed. -/
theorem not_isTie_of_polarGapDetCore (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (htrace : 2 < ∑ c ∈ ({x, y, z} : Finset (Fin m)), planeShadowSq design pole c)
    (hdet : 0 < polarPlaneDet design pole ({x, y, z} : Finset (Fin m)))
    (hgap : 0 < polarGapDet design x y z) :
    ¬ IsTie design :=
  not_isTie_of_polarGapDet design hpole hxy hxz hyz htrace hdet
    (leverage_lt_of_gapCore design hpole hxy hxz hyz htrace hdet hgap) hgap

end SurplusFree

/-! ## Part 9: the core targets

The surplus clause leaves the selection targets.  Three scalar clauses
remain: the shadow trace, the plane determinant and the gap determinant. -/

section CoreSelection

variable {size : ℕ}

/-- **THE CORE GAP TARGET.**  Three scalar clauses at a pole and a triple of
distinct labels: a shadow trace above two, a positive plane determinant and
a positive gap determinant. -/
def PolarGapCoreSelection (size : ℕ) : Prop :=
  ∀ design : WeightedDesign size 3, IsPrimitiveDesign design → IsTie design →
    ∃ pole x y z : Fin size,
      1 < design.atom pole ⬝ᵥ design.atom pole
        ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z
        ∧ 2 < ∑ c ∈ ({x, y, z} : Finset (Fin size)), planeShadowSq design pole c
        ∧ 0 < polarPlaneDet design pole ({x, y, z} : Finset (Fin size))
        ∧ 0 < polarGapDet design x y z

/-- **THE CORE WRAPPING TARGET.**  The core clauses at a wrapping triple of
the circular order. -/
def PolarWrapGapCoreSelection (size : ℕ) : Prop :=
  ∀ design : WeightedDesign size 3, IsPrimitiveDesign design → IsTie design →
    ∃ pole x y z : Fin size,
      1 < design.atom pole ⬝ᵥ design.atom pole
        ∧ PolarWrapping design pole x y z
        ∧ 2 < ∑ c ∈ ({x, y, z} : Finset (Fin size)), planeShadowSq design pole c
        ∧ 0 < polarPlaneDet design pole ({x, y, z} : Finset (Fin size))
        ∧ 0 < polarGapDet design x y z

/-- The core target implies the gap target: the surplus is derived. -/
theorem polarGapSelection_of_polarGapCoreSelection
    (hcore : PolarGapCoreSelection size) : PolarGapSelection size := by
  intro design hprimitive htie
  obtain ⟨pole, x, y, z, hlong, hxy, hxz, hyz, htrace, hdet, hgap⟩ :=
    hcore design hprimitive htie
  have hpole : 0 < design.atom pole ⬝ᵥ design.atom pole :=
    lt_trans zero_lt_one hlong
  exact ⟨pole, x, y, z, hlong, hxy, hxz, hyz, htrace, hdet,
    leverage_lt_of_gapCore design hpole hxy hxz hyz htrace hdet hgap, hgap⟩

/-- The core wrapping target implies the wrapping gap target. -/
theorem polarWrapGapSelection_of_polarWrapGapCoreSelection
    (hcore : PolarWrapGapCoreSelection size) : PolarWrapGapSelection size := by
  intro design hprimitive htie
  obtain ⟨pole, x, y, z, hlong, hwrapping, htrace, hdet, hgap⟩ :=
    hcore design hprimitive htie
  have hpole : 0 < design.atom pole ⬝ᵥ design.atom pole :=
    lt_trans zero_lt_one hlong
  have hxy := polarWrapping_ne_first_second design hpole hwrapping
  have hxz := polarWrapping_ne_first_third design hpole hwrapping
  have hyz := polarWrapping_ne_second_third design hpole hwrapping
  exact ⟨pole, x, y, z, hlong, hwrapping, htrace, hdet,
    leverage_lt_of_gapCore design hpole hxy hxz hyz htrace hdet hgap, hgap⟩

/-- **THE DECIDING CELL FROM THE CORE TARGET ALONE.** -/
theorem gtzWeighted_six_three_of_polarGapCoreSelection
    (hcore : PolarGapCoreSelection 6) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_polarGapSelection
    (polarGapSelection_of_polarGapCoreSelection hcore)

/-- **ALL OF RANK THREE FROM THE CORE TARGET ALONE.** -/
theorem gtzWeightedAll_three_of_polarGapCoreSelection
    (hcore : PolarGapCoreSelection 6) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_polarGapSelection
    (polarGapSelection_of_polarGapCoreSelection hcore)

/-- **THE DECIDING CELL FROM THE CORE WRAPPING TARGET ALONE.** -/
theorem gtzWeighted_six_three_of_polarWrapGapCoreSelection
    (hcore : PolarWrapGapCoreSelection 6) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_polarWrapGapSelection
    (polarWrapGapSelection_of_polarWrapGapCoreSelection hcore)

/-- **ALL OF RANK THREE FROM THE CORE WRAPPING TARGET ALONE.** -/
theorem gtzWeightedAll_three_of_polarWrapGapCoreSelection
    (hcore : PolarWrapGapCoreSelection 6) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_polarWrapGapSelection
    (polarWrapGapSelection_of_polarWrapGapCoreSelection hcore)

/-- The core target is false at size five. -/
theorem not_polarGapCoreSelection_five : ¬ PolarGapCoreSelection 5 :=
  fun hcore => not_polarGapSelection_five
    (polarGapSelection_of_polarGapCoreSelection hcore)

/-- The core wrapping target is false at size five. -/
theorem not_polarWrapGapCoreSelection_five : ¬ PolarWrapGapCoreSelection 5 :=
  fun hcore => not_polarWrapGapSelection_five
    (polarWrapGapSelection_of_polarWrapGapCoreSelection hcore)

/-- **THE GUARDRAIL ON THE CORE ROUTES.** -/
theorem sixSplitDiamondDesign_spares_polarGapCore :
    ¬ RankSuccShrinks 6 3 ∧ IsTie sixSplitDiamondDesign
      ∧ ¬ IsPrimitiveDesign sixSplitDiamondDesign
      ∧ ¬ PolarGapCoreSelection 5 ∧ ¬ PolarWrapGapCoreSelection 5 :=
  ⟨not_rankSuccShrinks_six_three, sixSplitDiamondDesign_isTie,
    not_isPrimitiveDesign_sixSplitDiamondDesign, not_polarGapCoreSelection_five,
    not_polarWrapGapCoreSelection_five⟩

end CoreSelection

/-! ## Part 10: the sharp form

The three core clauses are not merely sufficient for the kill: at every pole
of positive leverage they CHARACTERIZE the strict dominator.  Thus no weaker
true form of the core target exists at this interface, and the residual of
the polar arithmetic route is a faithful reformulation of the cell rather
than a narrowing of it. -/

section SharpForm

/-- **THE THREE CLAUSES BUILD THE DOMINATOR.**  The manufactured excess opens
both cover bounds, the surplus is free and the frame identity supplies the
arithmetic test. -/
theorem posDef_of_planeGapCore (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (htrace : 2 < ∑ c ∈ ({x, y, z} : Finset (Fin m)), planeShadowSq design pole c)
    (hdet : 0 < polarPlaneDet design pole ({x, y, z} : Finset (Fin m)))
    (hgap : 0 < polarGapDet design x y z) :
    (subsetSum design ({x, y, z} : Finset (Fin m)) - 1).PosDef := by
  have hdetGram := hdet
  rw [polarPlaneDet_eq] at hdetGram
  obtain ⟨excess, hexcessPos, htraceCover, hgramCover⟩ :=
    exists_excess_of_trace_planeDet htrace hdetGram
  have hz := leverage_lt_of_gapCore design hpole hxy hxz hyz htrace hdet hgap
  have hident := polarPlaneDet_mul_surplus_sub_adjugate design hpole hxy hxz hyz
  have hmargin : 0 < (design.atom pole ⬝ᵥ design.atom pole)
      * polarGapDet design x y z := mul_pos hpole hgap
  exact posDef_of_planeShadowSchur design hpole
    ({x, y, z} : Finset (Fin m)) hexcessPos htraceCover hgramCover hz
    (by linarith)

/-- **THE SHARP FORM.**  At every pole of positive leverage a triple of
distinct labels dominates strictly IF AND ONLY IF its shadow trace passes
two, its plane determinant is positive and its gap determinant is positive.
The pole is a free parameter of the left side and appears in two clauses of
the right side, thus the equivalence also proves the pole transport. -/
theorem posDef_iff_planeGapCore (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (subsetSum design ({x, y, z} : Finset (Fin m)) - 1).PosDef
      ↔ (2 < ∑ c ∈ ({x, y, z} : Finset (Fin m)), planeShadowSq design pole c
        ∧ 0 < polarPlaneDet design pole ({x, y, z} : Finset (Fin m))
        ∧ 0 < polarGapDet design x y z) := by
  constructor
  · intro hposDef
    obtain ⟨htrace, hdet, -, -⟩ :=
      planeInvariants_of_posDef design hpole hxy hxz hyz hposDef
    exact ⟨htrace, hdet, polarGapDet_pos_of_posDef design hxy hxz hyz hposDef⟩
  · rintro ⟨htrace, hdet, hgap⟩
    exact posDef_of_planeGapCore design hpole hxy hxz hyz htrace hdet hgap

end SharpForm

end Gtz

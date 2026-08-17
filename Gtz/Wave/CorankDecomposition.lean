/-
# The corank of the weak dominator: a two-sided needle and the death of corank three

A tie owns a triple `C0` with `subsetSum D C0 - 1` positive semidefinite and
not positive definite.  That gap matrix is singular, so its corank is `1`, `2`
or `3`, and the three values are three genuinely different geometries.  Corank
three means `subsetSum D C0 = 1` on the nose: the three atoms of `C0` are an
orthonormal basis.  This file kills that case at `(6,3)`, unconditionally.

## What is new here

The landed needle law `Gtz.exists_gapNeedle_of_isTie`
(`Gtz.Ties.ComplementJawWindow`) prices the gap of a tie through ONE uniform
weight cap `tau` and returns `(1 - 2 * tau) / tau`.  That constant is positive
only when `tau < 1/2`.  A `(6,3)` design may carry a weight of `9/10`, and
there the landed bound reads `1 - 2 * tau < 0` and says nothing.

This file replaces the one cap by TWO: `inner`, a cap on the weights INSIDE
`C0`, and `outer`, a cap on the weights OUTSIDE it.  The constant becomes
`1 - inner - outer`.  The gain is not cosmetic.  The maximum weight on `C0`
and the maximum weight on its complement sit at two DIFFERENT labels, and a
design of size at least three carries a third positive weight beside them.  So

  `inner + outer < 1`  ALWAYS,

with no light-weight hypothesis at all.  `Gtz.exists_splitWeightCaps_add_lt_one`
is that statement, and it is the only new ingredient the corank-three kill
needs.  Everything else is the landed complement engine, reused.

## The corank-three kill

Feed the two-sided needle a gap that vanishes.  The right side becomes
`inner * 0 = 0`, the left side is `(1 - inner - outer) * (probe ⬝ᵥ probe)` with
`probe` nonzero, and `1 - inner - outer > 0`.  Contradiction.  Hence

  `Gtz.subsetSum_ne_one_of_isTie`: at a tie, no subset with a `k`-sized
  complement and at least two members has `subsetSum D C0 = 1`.

At `(6,3)` every triple has a triple complement, so
`Gtz.subsetSum_ne_one_of_isTie_sixThree` says the gap of a `(6,3)` tie is
never the zero matrix, at ANY triple.  The tree already owned this on the
off-conic stratum only —
`Gtz.subsetSum_sub_one_ne_zero_of_hasNoCommonQuadric`
(`Gtz.Design.OrthogonalConicAndTwinRefutation`) carries the hypothesis
`HasNoCommonQuadric design.atom`.  The statement here carries no stratum
hypothesis and no primitivity hypothesis.

## Why this cannot prove `(5,3)`

`Gtz.diamondDesign` is a PRIMITIVE `(5,3)` tie, so no argument may exclude it.
The hypothesis that blocks the transfer is `hcompl : C0ᶜ.card = k`.  At
`(6,3)` a triple has a triple complement, and that complement is a legal
competitor the tie condition must refuse.  At `(5,3)` the complement of a
triple has two members, so no competitor exists and every theorem below is
silent.  One hypothesis carries the whole difference between the two cells.

## Calibration, measured

Exact rational computation over the four ties the tree owns gives the corank
of the gap at every weakly dominating triple:

* `Gtz.tetraDesign` at `(4,3)`, four dominating triples, corank `1` at each
* `Gtz.diamondDesign` at `(5,3)`, eight dominating triples, corank `1` at each
* `Gtz.nonUniformLeverageTieDesign` at `(6,3)`, ten dominating triples,
  corank `1` at each
* `Gtz.sixSplitDiamondDesign` at `(6,3)`, the split of the diamond, corank `1`

Every known tie sits at corank one.  Corank three is now closed at `(6,3)`.
The residue of the trichotomy is corank one and corank two, and the `(5,3)`
diamond lives in corank one.  So corank one is the case a `(6,3)` proof must
break and a `(5,3)` proof cannot.

## The vacuity guard

`Gtz.OnPathRegistryCollapse.elim_primitive_isTie_of_hinge` makes every Prop of
shape `∀ D, IsPrimitiveDesign D → IsTie D → _` equal to the frontier.  No
statement in this file has that shape.  Each one quantifies over a dominating
subset and concludes an inequality about the gap MATRIX, and each antecedent
is inhabited: `Gtz.nonUniformLeverageTieDesign` is a `(6,3)` tie, and its ten
dominating triples satisfy every hypothesis below.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.Certificates.ResidueDissolution
import Gtz.Reduction.RayleighCertificate
import Gtz.Reduction.RealVolumeFloor
import Gtz.Ties.TotalTieCorankOne
import Gtz.Ties.ComplementJawWindow
import Gtz.Ties.NonUniformLeverageTie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## Part 1. The two-sided needle

The landed needle caps every weight by one number.  Splitting the cap along
the partition `C0` / `C0ᶜ` costs nothing in the proof and buys a constant that
is positive without hypotheses. -/

/-- **The two-sided offside mass.**  At a tie, the complement of any subset
with a `k`-sized complement fails to be strict, so the landed engine returns a
direction carrying `1 - outer` of the weighted mass on `C0`.  Capping the
weights of `C0` by `inner` turns that into a bound on the plain squared
pairings. -/
theorem exists_twoSidedMass_of_isTie (D : WeightedDesign m k) (htie : IsTie D)
    (C0 : Finset (Fin m)) (hcompl : C0ᶜ.card = k)
    (inner outer : ℝ) (houterPos : 0 < outer)
    (hin : ∀ label ∈ C0, D.weight label ≤ inner)
    (hout : ∀ label ∈ C0ᶜ, D.weight label ≤ outer) :
    ∃ probe : Fin k → ℝ, probe ≠ 0 ∧
      (1 - outer) * (probe ⬝ᵥ probe)
        ≤ inner * ∑ label ∈ C0, (D.atom label ⬝ᵥ probe) ^ 2 := by
  obtain ⟨probe, hne, hmass⟩ := exists_offside_mass_of_not_posDef D C0ᶜ outer
    houterPos hout (htie.2 C0ᶜ hcompl)
  rw [compl_compl] at hmass
  refine ⟨probe, hne, ?_⟩
  calc (1 - outer) * (probe ⬝ᵥ probe)
      ≤ ∑ label ∈ C0, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2 := hmass
    _ ≤ ∑ label ∈ C0, inner * (D.atom label ⬝ᵥ probe) ^ 2 :=
        Finset.sum_le_sum fun label hmem =>
          mul_le_mul_of_nonneg_right (hin label hmem) (sq_nonneg _)
    _ = inner * ∑ label ∈ C0, (D.atom label ⬝ᵥ probe) ^ 2 :=
        (Finset.mul_sum _ _ _).symm

/-- **The two-sided needle.**  The sharpening of
`Gtz.exists_gapNeedle_of_isTie`: the single cap `tau` becomes an inside cap
`inner` and an outside cap `outer`, and the constant `1 - 2 * tau` becomes
`1 - inner - outer`.  Setting `inner = outer = tau` recovers the landed
statement exactly, so nothing is lost and the positivity of the constant is
gained. -/
theorem exists_twoSidedNeedle_of_isTie (D : WeightedDesign m k) (htie : IsTie D)
    (C0 : Finset (Fin m)) (hcompl : C0ᶜ.card = k)
    (inner outer : ℝ) (houterPos : 0 < outer)
    (hin : ∀ label ∈ C0, D.weight label ≤ inner)
    (hout : ∀ label ∈ C0ᶜ, D.weight label ≤ outer) :
    ∃ probe : Fin k → ℝ, probe ≠ 0 ∧
      (1 - inner - outer) * (probe ⬝ᵥ probe)
        ≤ inner * (probe ⬝ᵥ ((subsetSum D C0 - 1) *ᵥ probe)) := by
  obtain ⟨probe, hne, hmass⟩ := exists_twoSidedMass_of_isTie D htie C0 hcompl
    inner outer houterPos hin hout
  refine ⟨probe, hne, ?_⟩
  have hform : probe ⬝ᵥ ((subsetSum D C0 - 1) *ᵥ probe)
      = (∑ label ∈ C0, (D.atom label ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe :=
    dominationGap_form D C0 probe
  rw [hform, mul_sub]
  linarith [hmass]

/-! ## Part 2. The structural positivity of the two-sided constant

This is the new ingredient.  The maximum weight on `C0` and the maximum weight
on `C0ᶜ` sit at two distinct labels.  If `C0` holds a second label, that label
carries positive weight too, and the three weights together stay below the
total mass `1`. -/

/-- **Split weight caps with a positive constant.**  Every design whose subset
`C0` has at least two members and a nonempty complement admits an inside cap
and an outside cap whose sum is STRICTLY below one.  The caps are the two
maxima, and the strictness comes from the second member of `C0`, whose weight
is positive and is counted by neither maximum. -/
theorem exists_splitWeightCaps_add_lt_one (D : WeightedDesign m k)
    (C0 : Finset (Fin m)) (htwo : 2 ≤ C0.card) (hcomplNe : C0ᶜ.Nonempty) :
    ∃ inner outer : ℝ, 0 < inner ∧ 0 < outer ∧ inner + outer < 1
      ∧ (∀ label ∈ C0, D.weight label ≤ inner)
      ∧ (∀ label ∈ C0ᶜ, D.weight label ≤ outer) := by
  classical
  have hC0Ne : C0.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨insideMax, hinsideMem, hinsideMax⟩ :=
    C0.exists_max_image D.weight hC0Ne
  obtain ⟨outsideMax, houtsideMem, houtsideMax⟩ :=
    C0ᶜ.exists_max_image D.weight hcomplNe
  -- A second member of `C0`, distinct from the label carrying the inside maximum.
  obtain ⟨second, hsecondMem, hsecondNe⟩ :
      ∃ second ∈ C0, second ≠ insideMax := by
    by_contra hcon
    push_neg at hcon
    have hsub : C0 ⊆ {insideMax} := fun label hlabel =>
      Finset.mem_singleton.mpr (hcon label hlabel)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    omega
  have hInsideOutsideNe : insideMax ≠ outsideMax := by
    intro heq
    exact (Finset.mem_compl.mp houtsideMem) (heq ▸ hinsideMem)
  have hSecondOutsideNe : second ≠ outsideMax := by
    intro heq
    exact (Finset.mem_compl.mp houtsideMem) (heq ▸ hsecondMem)
  -- The three distinct labels carry at most the whole mass.
  have htriple : D.weight insideMax + D.weight outsideMax + D.weight second ≤ 1 := by
    have hsum : ∑ label ∈ ({insideMax, outsideMax, second} : Finset (Fin m)),
        D.weight label
        = D.weight insideMax + D.weight outsideMax + D.weight second := by
      rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          exact ⟨hInsideOutsideNe, fun heq => hsecondNe heq.symm⟩),
        Finset.sum_insert (by
          simp only [Finset.mem_singleton]
          exact fun heq => hSecondOutsideNe heq.symm),
        Finset.sum_singleton]
      ring
    have hle := sum_weight_subset_le_one D
      ({insideMax, outsideMax, second} : Finset (Fin m))
    linarith [hsum ▸ hle]
  refine ⟨D.weight insideMax, D.weight outsideMax, D.weight_pos _, D.weight_pos _,
    ?_, hinsideMax, houtsideMax⟩
  linarith [htriple, D.weight_pos second]

/-! ## Part 3. The gap floor at a tie

Composing Part 1 and Part 2: at a tie, every subset with a `k`-sized
complement and at least two members reads a direction on which the gap form is
STRICTLY positive, with an explicit positive floor built from two weights. -/

/-- **The unconditional gap floor.**  At a tie, every subset `C0` with at
least two members and a `k`-sized complement carries a nonzero direction whose
gap form is bounded below by a positive multiple of the direction's norm.  No
light-weight hypothesis appears: the constant is positive by
`Gtz.exists_splitWeightCaps_add_lt_one`. -/
theorem exists_positive_gapFloor_of_isTie (D : WeightedDesign m k) (htie : IsTie D)
    (C0 : Finset (Fin m)) (htwo : 2 ≤ C0.card) (hcompl : C0ᶜ.card = k) (hk : 1 ≤ k) :
    ∃ (inner outer : ℝ) (probe : Fin k → ℝ),
      0 < inner ∧ 0 < outer ∧ inner + outer < 1 ∧ probe ≠ 0 ∧
        (1 - inner - outer) * (probe ⬝ᵥ probe)
          ≤ inner * (probe ⬝ᵥ ((subsetSum D C0 - 1) *ᵥ probe)) := by
  have hcomplNe : C0ᶜ.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨inner, outer, hinnerPos, houterPos, hsum, hin, hout⟩ :=
    exists_splitWeightCaps_add_lt_one D C0 htwo hcomplNe
  obtain ⟨probe, hne, hneedle⟩ := exists_twoSidedNeedle_of_isTie D htie C0 hcompl
    inner outer houterPos hin hout
  exact ⟨inner, outer, probe, hinnerPos, houterPos, hsum, hne, hneedle⟩

/-- **The gap form is strictly positive somewhere.**  The floor read without
the constants: at a tie, the gap of every subset with a `k`-sized complement
and at least two members is strictly positive in some direction.  In
particular the gap matrix is not the zero matrix. -/
theorem exists_pos_gapForm_of_isTie (D : WeightedDesign m k) (htie : IsTie D)
    (C0 : Finset (Fin m)) (htwo : 2 ≤ C0.card) (hcompl : C0ᶜ.card = k) (hk : 1 ≤ k) :
    ∃ probe : Fin k → ℝ, probe ≠ 0 ∧
      0 < probe ⬝ᵥ ((subsetSum D C0 - 1) *ᵥ probe) := by
  obtain ⟨inner, outer, probe, hinnerPos, _, hsum, hne, hfloor⟩ :=
    exists_positive_gapFloor_of_isTie D htie C0 htwo hcompl hk
  refine ⟨probe, hne, ?_⟩
  have hpp : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hne
  nlinarith [hfloor, hpp, hinnerPos, hsum]

/-! ## Part 4. Corank three is empty

The gap of a weakly dominating triple has corank three exactly when it is the
zero matrix, that is when `subsetSum D C0 = 1`.  Part 3 forbids that. -/

/-- **No tie carries a vanishing gap.**  At a tie, no subset with at least two
members and a `k`-sized complement satisfies `subsetSum D C0 = 1`.  This is
the corank-three case of the gap trichotomy, and it is closed with no stratum
hypothesis, no primitivity hypothesis and no light-weight hypothesis. -/
theorem subsetSum_ne_one_of_isTie (D : WeightedDesign m k) (htie : IsTie D)
    (C0 : Finset (Fin m)) (htwo : 2 ≤ C0.card) (hcompl : C0ᶜ.card = k) (hk : 1 ≤ k) :
    subsetSum D C0 ≠ 1 := by
  intro heq
  obtain ⟨probe, hne, hpos⟩ := exists_pos_gapForm_of_isTie D htie C0 htwo hcompl hk
  rw [heq, sub_self, Matrix.zero_mulVec, dotProduct_zero] at hpos
  exact lt_irrefl 0 hpos

/-- **The gap of a tie is a nonzero matrix.**  The same statement read on the
gap directly. -/
theorem subsetSum_sub_one_ne_zero_of_isTie (D : WeightedDesign m k) (htie : IsTie D)
    (C0 : Finset (Fin m)) (htwo : 2 ≤ C0.card) (hcompl : C0ᶜ.card = k) (hk : 1 ≤ k) :
    subsetSum D C0 - 1 ≠ 0 := by
  intro heq
  exact subsetSum_ne_one_of_isTie D htie C0 htwo hcompl hk (sub_eq_zero.mp heq)

/-! ### The `(6,3)` instance

At `(6,3)` a triple has a triple complement, so the cardinality hypotheses are
free and the statement holds at EVERY triple of EVERY tie. -/

-- The complement of a triple in `Fin 6` is a triple:
-- `Gtz.card_compl_eq_three_of_card_eq_three` (`Gtz.Design.UThreeSixDisjunction`).

/-- **Corank three is empty at `(6,3)`, unconditionally.**  No `(6,3)` tie has
a triple whose atom sum is the identity.  Equivalently, by
`Gtz.subsetSum_eq_one_iff_orthonormalTriple`, no triple of a `(6,3)` tie is an
orthonormal basis of the three-dimensional space.

The tree already owned this on the off-conic stratum, through
`Gtz.subsetSum_sub_one_ne_zero_of_hasNoCommonQuadric`, which assumes
`HasNoCommonQuadric design.atom`.  Here there is no stratum hypothesis. -/
theorem subsetSum_ne_one_of_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    (C0 : Finset (Fin 6)) (hcard : C0.card = 3) :
    subsetSum D C0 ≠ 1 :=
  subsetSum_ne_one_of_isTie D htie C0 (by omega)
    (card_compl_eq_three_of_card_eq_three C0 hcard) (by omega)

/-- **The gap matrix of a `(6,3)` tie never vanishes.** -/
theorem subsetSum_sub_one_ne_zero_of_isTie_sixThree (D : WeightedDesign 6 3)
    (htie : IsTie D) (C0 : Finset (Fin 6)) (hcard : C0.card = 3) :
    subsetSum D C0 - 1 ≠ 0 :=
  subsetSum_sub_one_ne_zero_of_isTie D htie C0 (by omega)
    (card_compl_eq_three_of_card_eq_three C0 hcard) (by omega)

/-- **Every triple of a `(6,3)` tie has a strictly positive gap direction.**
The residue of the corank trichotomy: the gap is positive semidefinite,
singular, and nonzero, so its rank is one or two and its corank is two or one.
Corank three is gone. -/
theorem exists_pos_gapForm_of_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    (C0 : Finset (Fin 6)) (hcard : C0.card = 3) :
    ∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧
      0 < probe ⬝ᵥ ((subsetSum D C0 - 1) *ᵥ probe) :=
  exists_pos_gapForm_of_isTie D htie C0 (by omega)
    (card_compl_eq_three_of_card_eq_three C0 hcard) (by omega)

/-! ## Part 5. The corank-two reading

Corank two means the gap is `lam` times a rank-one projector.  The needle
prices that single eigenvalue from below, with the same unconditional
constant. -/

/-- **The corank-two eigenvalue floor.**  If the gap of `C0` at a tie is the
rank-one form `lam • atomMatrix gapDir` with `gapDir` a unit vector, then
`inner * lam` is at least `1 - inner - outer`.  With the maximal caps of
`Gtz.exists_splitWeightCaps_add_lt_one` the right side is positive, so `lam`
is bounded away from zero: a corank-two tie cannot have a small gap. -/
theorem le_mul_lam_of_isTie_of_rankOneGap (D : WeightedDesign m k) (htie : IsTie D)
    (C0 : Finset (Fin m)) (hcompl : C0ᶜ.card = k)
    (inner outer lam : ℝ) (houterPos : 0 < outer) (hinnerNonneg : 0 ≤ inner)
    (hlam : 0 ≤ lam)
    (gapDir : Fin k → ℝ) (hunit : gapDir ⬝ᵥ gapDir = 1)
    (hgap : subsetSum D C0 - 1 = lam • atomMatrix gapDir)
    (hin : ∀ label ∈ C0, D.weight label ≤ inner)
    (hout : ∀ label ∈ C0ᶜ, D.weight label ≤ outer) :
    1 - inner - outer ≤ inner * lam := by
  obtain ⟨probe, hne, hneedle⟩ := exists_twoSidedNeedle_of_isTie D htie C0 hcompl
    inner outer houterPos hin hout
  have hpp : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hne
  -- The gap form on the rank-one shape is `lam * (gapDir ⬝ᵥ probe) ^ 2`.
  have hform : probe ⬝ᵥ ((subsetSum D C0 - 1) *ᵥ probe)
      = lam * (gapDir ⬝ᵥ probe) ^ 2 := by
    rw [hgap, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm probe gapDir]
    ring
  -- Cauchy-Schwarz caps that square by the norm, because `gapDir` is a unit vector.
  have hcs : (gapDir ⬝ᵥ probe) ^ 2 ≤ probe ⬝ᵥ probe := by
    have := dotProduct_sq_le_mul gapDir probe
    rw [hunit, one_mul] at this
    exact this
  rw [hform] at hneedle
  have hstep : inner * (lam * (gapDir ⬝ᵥ probe) ^ 2)
      ≤ (inner * lam) * (probe ⬝ᵥ probe) := by
    have hil : 0 ≤ inner * lam := mul_nonneg hinnerNonneg hlam
    calc inner * (lam * (gapDir ⬝ᵥ probe) ^ 2)
        = (inner * lam) * (gapDir ⬝ᵥ probe) ^ 2 := by ring
      _ ≤ (inner * lam) * (probe ⬝ᵥ probe) := mul_le_mul_of_nonneg_left hcs hil
  exact le_of_mul_le_mul_right (le_trans hneedle hstep) hpp

/-! ## Part 6. The leverage floor on a dominating triple

Cauchy-Schwarz turns the gap floor into a floor on the SUM of leverages over
the dominating subset.  The tree's unconditional ledger bound
`Gtz.leverage_one_le_of_isTie_sixThree` gives `1 ≤ leverage` for each of the
six atoms, hence `3` for a triple.  The bound here is `(1 - outer) / inner`,
which at uniform weights `1/6` reads `5`. -/

-- The leverage of an atom is its self dot product:
-- `Gtz.leverageOf_eq_dotProduct_self` (`Gtz.Design.NearPencilTransport`).

/-- **The leverage floor of a dominating subset at a tie.**  At a tie, the
leverages of the atoms of `C0` sum to at least `(1 - outer) / inner`, written
here without division as `1 - outer ≤ inner * ∑ leverage`.  This strengthens
the per-atom ledger floor whenever `(1 - outer) / inner` exceeds the
cardinality of `C0`. -/
theorem sum_leverage_floor_of_isTie (D : WeightedDesign m k) (htie : IsTie D)
    (C0 : Finset (Fin m)) (hcompl : C0ᶜ.card = k)
    (inner outer : ℝ) (houterPos : 0 < outer) (hinnerNonneg : 0 ≤ inner)
    (hin : ∀ label ∈ C0, D.weight label ≤ inner)
    (hout : ∀ label ∈ C0ᶜ, D.weight label ≤ outer) :
    1 - outer ≤ inner * ∑ label ∈ C0, leverageOf (D.atom label) := by
  obtain ⟨probe, hne, hmass⟩ := exists_twoSidedMass_of_isTie D htie C0 hcompl
    inner outer houterPos hin hout
  have hpp : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hne
  -- Cauchy-Schwarz on each atom: `(g ⬝ᵥ probe) ^ 2 ≤ leverage * (probe ⬝ᵥ probe)`.
  have hterm : ∑ label ∈ C0, (D.atom label ⬝ᵥ probe) ^ 2
      ≤ (∑ label ∈ C0, leverageOf (D.atom label)) * (probe ⬝ᵥ probe) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun label _ => ?_
    rw [leverageOf_eq_dotProduct_self]
    exact dotProduct_sq_le_mul (D.atom label) probe
  have hchain : (1 - outer) * (probe ⬝ᵥ probe)
      ≤ inner * ((∑ label ∈ C0, leverageOf (D.atom label)) * (probe ⬝ᵥ probe)) :=
    le_trans hmass (mul_le_mul_of_nonneg_left hterm hinnerNonneg)
  nlinarith [hchain, hpp]

/-- **The `(6,3)` leverage floor.**  Every triple of a `(6,3)` tie carries
leverage sum at least `(1 - outer) / inner` for the split caps.  With the
maximal caps this is strictly greater than `1`, and at uniform weights `1/6`
it reads `5`, against the ledger's `3`. -/
theorem sum_leverage_floor_of_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    (C0 : Finset (Fin 6)) (hcard : C0.card = 3) :
    ∃ inner outer : ℝ, 0 < inner ∧ 0 < outer ∧ inner + outer < 1
      ∧ 1 - outer ≤ inner * ∑ label ∈ C0, leverageOf (D.atom label) := by
  have hcompl := card_compl_eq_three_of_card_eq_three C0 hcard
  have hcomplNe : C0ᶜ.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨inner, outer, hinnerPos, houterPos, hsum, hin, hout⟩ :=
    exists_splitWeightCaps_add_lt_one D C0 (by omega) hcomplNe
  exact ⟨inner, outer, hinnerPos, houterPos, hsum,
    sum_leverage_floor_of_isTie D htie C0 hcompl inner outer houterPos
      hinnerPos.le hin hout⟩

/-! ## Part 7. The trichotomy residue, named against the gap matrix

The three coranks are exhaustive because the gap of a weakly dominating subset
is positive semidefinite and singular.  Part 4 removes corank three.  What
remains is stated here as a property of the GAP, never as a property of the
shape `IsPrimitiveDesign D → IsTie D → _`, which the registry collapse would
make equal to the whole frontier. -/

/-- **The residual corank cell at `(6,3)`.**  A tie's gap at a triple is
positive semidefinite, is not positive definite, and is not zero.  The three
clauses together say the corank is one or two, and the cell is exactly the
residue this file leaves open. -/
def GapIsSingularNonzeroAt (D : WeightedDesign 6 3) (C0 : Finset (Fin 6)) : Prop :=
  (subsetSum D C0 - 1).PosSemidef ∧ ¬ (subsetSum D C0 - 1).PosDef
    ∧ subsetSum D C0 - 1 ≠ 0

/-- **Every dominating triple of a `(6,3)` tie sits in the residual cell.**
The corank-three case is discharged inside the proof, so the statement records
a genuine narrowing of the tie locus rather than a renaming of it. -/
theorem gapIsSingularNonzeroAt_of_isTie_of_dominates (D : WeightedDesign 6 3)
    (htie : IsTie D) (C0 : Finset (Fin 6)) (hcard : C0.card = 3)
    (hdom : Dominates D C0) :
    GapIsSingularNonzeroAt D C0 :=
  ⟨hdom, htie.2 C0 hcard, subsetSum_sub_one_ne_zero_of_isTie_sixThree D htie C0 hcard⟩

/-- **The tie owns a residual-cell triple.**  Reading the first clause of
`IsTie`, every `(6,3)` tie carries a triple in the residual cell.  The
antecedent is inhabited by `Gtz.nonUniformLeverageTieDesign`. -/
theorem exists_gapIsSingularNonzeroAt_of_isTie (D : WeightedDesign 6 3) (htie : IsTie D) :
    ∃ C0 : Finset (Fin 6), C0.card = 3 ∧ GapIsSingularNonzeroAt D C0 := by
  obtain ⟨C0, hcard, hdom⟩ := htie.1
  exact ⟨C0, hcard, gapIsSingularNonzeroAt_of_isTie_of_dominates D htie C0 hcard hdom⟩

/-! ## Part 8. The antecedent is inhabited

The registry's standing trap is a theorem whose hypothesis no object
satisfies.  `Gtz.nonUniformLeverageTieDesign` is a landed `(6,3)` tie, so the
corank-three kill has content at a concrete design.  Exact rational
computation puts the corank of its gap at `1` at each of its ten weakly
dominating triples, which agrees with the theorem. -/

/-- **The corank-three kill, read at a landed tie.**  No triple of
`Gtz.nonUniformLeverageTieDesign` has atom sum equal to the identity.  The
statement carries no hypothesis beyond the cardinality of the triple, so the
general theorem above is not vacuous. -/
theorem subsetSum_ne_one_nonUniformLeverageTieDesign
    (C0 : Finset (Fin 6)) (hcard : C0.card = 3) :
    subsetSum nonUniformLeverageTieDesign C0 ≠ 1 :=
  subsetSum_ne_one_of_isTie_sixThree nonUniformLeverageTieDesign
    nonUniformLeverageTieDesign_isTie C0 hcard

/-- **The residual cell is inhabited.**  `Gtz.nonUniformLeverageTieDesign`
carries a triple whose gap is positive semidefinite, singular and nonzero. -/
theorem exists_gapIsSingularNonzeroAt_nonUniformLeverageTieDesign :
    ∃ C0 : Finset (Fin 6), C0.card = 3
      ∧ GapIsSingularNonzeroAt nonUniformLeverageTieDesign C0 :=
  exists_gapIsSingularNonzeroAt_of_isTie nonUniformLeverageTieDesign
    nonUniformLeverageTieDesign_isTie

end Gtz

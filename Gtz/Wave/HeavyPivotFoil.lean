import Gtz.Wave.QuadDropSign

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12800000

/-!
# The heavy pivot is the false ingredient of the plane route

The pivot passage `Gtz.atomPivotSchur_cover` turns a pivot slot and a pair of
slots into a covering triple.  A route to the `(6,3)` cell must SELECT the
pivot and the pair.  The campaign proposed to select the pivot by the heavy
pigeonhole `Gtz.exists_heavy_leverage_slot`, which supplies a slot with
`3 t_p <= G_pp` at every datum, and then to select the pair by the plane
theorem `Gtz.exists_dominatingPlanePair_margin`.

**The heavy selection is FALSE.**  This module refutes it at an exact rational
tight frame of six atoms with entries in fifths, at rational scales of mass
one.  The refutation does NOT touch the cell, and it does NOT touch the plane
selection: at the same datum the cell holds with room, and the covering triple
passes the plane test at the inflated scale.

## The foil

The six atoms are the six rows of an integer matrix over five whose three
columns are orthogonal of squared length twenty five:

  `(1, -1, 1)/5`, `(3, -3, -2)/5`, `(2, 3, -3)/5`,
  `(-1, 1, -1)/5`, `(-3, -2, -3)/5`, `(1, -1, 1)/5`.

The scales are `1/30, 3/10, 3/10, 1/30, 3/10, 1/30`, of mass one.  The Gram
diagonal reads `3/25` at the slots zero, three and five, and `22/25` at the
slots one, two and four.  The heavy test therefore reads

  `3/25 - 3 * (1/30) = 1/50` at the slots zero, three and five,
  `22/25 - 3 * (3/10) = -(1/50)` at the slots one, two and four,

so the heavy slots are EXACTLY zero, three and five.  The three heavy atoms
are parallel, because the atom of slot five repeats the atom of slot zero and
the atom of slot three is its negative.  A triple that holds two heavy slots
spans a plane, and a triple that holds one heavy slot misses the identity by
`11/15` at one of three probes.  No covering triple holds a heavy slot.

## The foil does not refute the cell

The triple of the slots one, two and four covers every direction, with the
strict margin `29/15` on the diagonal of its shifted form.  The same triple
passes the plane test at the pivot one with the margin `23/77`, so the LIVE
pivot selection survives the foil.  The pivot passage itself asks only
`t_p < G_pp`, and every heavy slot of the foil is live, so the refutation
lands on the heavy pigeonhole and on nothing else.

## Why the two tests are not comparable

Layer six lands the exact gap between the plane test at the inflated scale
`1/(1 - t_p)` and the cover test at the pivot.  Both are two by two forms in
the pair, written with the Schur complement of the pivot.  Their difference is

  `t_p * ( (g_1 c_1 + g_2 c_2)^2 / (G_pp (G_pp - t_p))
            - (t_1 c_1^2 + t_2 c_2^2) / (1 - t_p) )`,

a rank one form minus a positive diagonal form.  It is positive along the
coupling and negative across it.  Neither test implies the other.  At the
vector `(g_2, -(g_1))`, which the coupling reads as zero, the gap is exactly
`-(t_p (t_1 g_2^2 + t_2 g_1^2) / (1 - t_p))`, strictly negative at a live
coupling.  A covering triple therefore need NOT sit inside the feasible set of
the plane theorem, and a plane feasible pair need NOT cover.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomTripleRead`, `Gtz.atomTripleCovers` — the cover reading of a triple
  and the cover test, in ambient coordinates.
* `Gtz.AtomHeavyPivotCoverClosed`, `Gtz.AtomLivePivotCoverClosed`,
  `Gtz.AtomHeavyPivotPlaneCoverClosed`, `Gtz.AtomLivePivotPlaneCoverClosed` —
  the four selection criteria of the pivot route.
* `Gtz.atomHeavyPivotCoverClosed_of_heavyPlane`,
  `Gtz.atomLivePivotCoverClosed_of_livePlane`,
  `Gtz.atomLivePivotCoverClosed_of_heavyPivotCover` — the implications between
  them.  The heavy criteria are the strong ones.
* `Gtz.atomVertexCoverClosed_of_livePivotCover`,
  `Gtz.gtzWeighted_six_three_of_livePivotCover`,
  `Gtz.gtzWeighted_six_three_of_livePivotPlaneCover` — **THE LIVE ROUTE STILL
  CLOSES THE CELL.**
* `Gtz.heavyFoilAtom`, `Gtz.heavyFoilScale`, `Gtz.heavyFoilScale_pos`,
  `Gtz.heavyFoilScale_sum`, `Gtz.heavyFoilAtom_isTightFrame`,
  `Gtz.heavyFoilGram`, `Gtz.heavyFoilGram_eq` — the foil and its Gram, in
  closed form.
* `Gtz.heavyFoilAtom_five_eq_zero`, `Gtz.heavyFoilAtom_three_eq_neg` — the
  three heavy atoms are parallel.
* `Gtz.heavyFoil_heavy_iff` — **THE HEAVY SLOTS ARE EXACTLY ZERO, THREE AND
  FIVE**, and the heavy margin is `1/50` against `-(1/50)`.
* `Gtz.heavyFoil_live` — every slot of the foil is live, so the pivot passage
  applies at each of them.
* `Gtz.heavyFoilProbe`, `Gtz.heavyFoilEnergy`, `Gtz.heavyFoilRead`,
  `Gtz.heavyFoilProbe_energy`, `Gtz.heavyFoilRead_eq` — the six probes and the
  thirty six readings, in closed form.
* `Gtz.heavyFoil_triple_fails` — **EVERY TRIPLE THROUGH A HEAVY SLOT MISSES A
  PROBE.**
* `Gtz.not_atomHeavyPivotCoverClosed`,
  `Gtz.not_atomHeavyPivotPlaneCoverClosed` — **THE REFUTATION**, for the heavy
  selection and for the full heavy plane route above it.
* `Gtz.heavyFoil_cover_oneTwoFour`, `Gtz.heavyFoilAtom_hasVertexCover` — the
  foil carries a covering triple, so it refutes the selection and not the cell.
* `Gtz.heavyFoil_plane_oneTwoFour` — the covering triple passes the plane test
  at the pivot one and at the inflated scale, so the foil refutes the heavy
  ingredient and not the plane ingredient.
* `Gtz.planeCoverGap`, `Gtz.planeCoverGap_polar`,
  `Gtz.planeCoverGap_polar_neg` — **THE GAP BETWEEN THE PLANE TEST AND THE
  COVER TEST**, as an identity and as a strict sign across the coupling.

## Vacuity

The refutation is an exact rational computation at one named configuration.
The live criteria are not refuted here, and layer two proves that they still
carry the cell, so the repair is a genuine weakening and not a retreat.
-/

namespace Gtz

open Matrix

/-! ## Layer 0 — the entries of a short table -/

section TableEntries

/-- The entries of a table at the indices that a cons does not reduce on its
own.  The tail is a variable, so these match a table that the simplifier has
already put in its expanded shape. -/
theorem foilCons3_2 {α : Type*} (a : α) (u : Fin 2 → α) : vecCons a u 2 = u 1 := rfl

theorem foilCons4_2 {α : Type*} (a : α) (u : Fin 3 → α) : vecCons a u 2 = u 1 := rfl

theorem foilCons4_3 {α : Type*} (a : α) (u : Fin 3 → α) : vecCons a u 3 = u 2 := rfl

theorem foilCons5_2 {α : Type*} (a : α) (u : Fin 4 → α) : vecCons a u 2 = u 1 := rfl

theorem foilCons5_3 {α : Type*} (a : α) (u : Fin 4 → α) : vecCons a u 3 = u 2 := rfl

theorem foilCons5_4 {α : Type*} (a : α) (u : Fin 4 → α) : vecCons a u 4 = u 3 := rfl

theorem foilCons6_2 {α : Type*} (a : α) (u : Fin 5 → α) : vecCons a u 2 = u 1 := rfl

theorem foilCons6_3 {α : Type*} (a : α) (u : Fin 5 → α) : vecCons a u 3 = u 2 := rfl

theorem foilCons6_4 {α : Type*} (a : α) (u : Fin 5 → α) : vecCons a u 4 = u 3 := rfl

theorem foilCons6_5 {α : Type*} (a : α) (u : Fin 5 → α) : vecCons a u 5 = u 4 := rfl

end TableEntries

/-! ## Layer 1 — the four selection criteria of the pivot route -/

section Criteria

variable {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}

/-- The COVER READING of a triple of slots at one direction: the scaled squared
readings of the three atoms. -/
noncomputable def atomTripleRead (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (pivot slotOne slotTwo : Fin 6) (direction : Fin 3 → ℝ) : ℝ :=
  (atom pivot ⬝ᵥ direction) ^ 2 / scale pivot
    + (atom slotOne ⬝ᵥ direction) ^ 2 / scale slotOne
    + (atom slotTwo ⬝ᵥ direction) ^ 2 / scale slotTwo

/-- The COVER TEST of a triple: the reading beats the energy at every
direction. -/
def AtomTripleCovers (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (pivot slotOne slotTwo : Fin 6) : Prop :=
  ∀ direction : Fin 3 → ℝ,
    direction ⬝ᵥ direction ≤ atomTripleRead atom scale pivot slotOne slotTwo direction

/-- The PLANE TEST of a pair at a pivot, at the full inflated scale
`1/(1 - t_p)`.  Against a probe that the pivot atom reads as zero, the plane
reading of the pair beats the probe energy after the inflation. -/
def AtomPairPlaneDominates (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (pivot slotOne slotTwo : Fin 6) : Prop :=
  ∀ probe : Fin 3 → ℝ, atom pivot ⬝ᵥ probe = 0 →
    probe ⬝ᵥ probe
      ≤ (1 - scale pivot) * atomPivotPlaneRead atom scale slotOne slotTwo probe

/-- **THE HEAVY PIVOT SELECTION.**  Every datum carries a heavy pivot inside a
covering triple.  The heavy test is the pigeonhole of
`Gtz.exists_heavy_leverage_slot` at rank three and mass one. -/
def AtomHeavyPivotCoverClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 3 * scale pivot ≤ atomGram atom pivot pivot
        ∧ AtomTripleCovers atom scale pivot slotOne slotTwo

/-- **THE LIVE PIVOT SELECTION.**  The same statement with the pivot only
LIVE, which is the hypothesis that `Gtz.atomPivotSchur_cover` consumes. -/
def AtomLivePivotCoverClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ scale pivot < atomGram atom pivot pivot
        ∧ AtomTripleCovers atom scale pivot slotOne slotTwo

/-- **THE FULL HEAVY PLANE ROUTE.**  A heavy pivot, a pair that dominates the
plane of that pivot at the inflated scale, and a covering triple.  This is the
measured finding that the route was staffed on. -/
def AtomHeavyPivotPlaneCoverClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 3 * scale pivot ≤ atomGram atom pivot pivot
        ∧ AtomPairPlaneDominates atom scale pivot slotOne slotTwo
        ∧ AtomTripleCovers atom scale pivot slotOne slotTwo

/-- **THE REPAIRED PLANE ROUTE.**  The same statement with the pivot only
LIVE.  The foil of this module does not touch it. -/
def AtomLivePivotPlaneCoverClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ scale pivot < atomGram atom pivot pivot
        ∧ AtomPairPlaneDominates atom scale pivot slotOne slotTwo
        ∧ AtomTripleCovers atom scale pivot slotOne slotTwo

/-- The full heavy route carries the heavy selection. -/
theorem atomHeavyPivotCoverClosed_of_heavyPlane
    (hroute : AtomHeavyPivotPlaneCoverClosed) : AtomHeavyPivotCoverClosed := by
  intro atom scale hpos hmass hframe
  obtain ⟨pivot, slotOne, slotTwo, hpy, hpw, hyw, hheavy, -, hcover⟩ :=
    hroute atom scale hpos hmass hframe
  exact ⟨pivot, slotOne, slotTwo, hpy, hpw, hyw, hheavy, hcover⟩

/-- The repaired route carries the live selection. -/
theorem atomLivePivotCoverClosed_of_livePlane
    (hroute : AtomLivePivotPlaneCoverClosed) : AtomLivePivotCoverClosed := by
  intro atom scale hpos hmass hframe
  obtain ⟨pivot, slotOne, slotTwo, hpy, hpw, hyw, hlive, -, hcover⟩ :=
    hroute atom scale hpos hmass hframe
  exact ⟨pivot, slotOne, slotTwo, hpy, hpw, hyw, hlive, hcover⟩

/-- **THE HEAVY SELECTION IS THE STRONGER ONE.**  A heavy pivot at mass one is
live, because three scales of a positive vector of mass one total less than
the mass. -/
theorem atomLivePivotCoverClosed_of_heavyPivotCover
    (hheavy : AtomHeavyPivotCoverClosed) : AtomLivePivotCoverClosed := by
  intro atom scale hpos hmass hframe
  obtain ⟨pivot, slotOne, slotTwo, hpy, hpw, hyw, hbig, hcover⟩ :=
    hheavy atom scale hpos hmass hframe
  refine ⟨pivot, slotOne, slotTwo, hpy, hpw, hyw, ?_, hcover⟩
  have hscale : 0 < scale pivot := hpos pivot
  linarith [hbig, hscale]

/-- **THE LIVE ROUTE CLOSES THE CELL.**  A live pivot inside a covering triple
supplies the integral cover of three slots. -/
theorem atomVertexCoverClosed_of_livePivotCover
    (hlive : AtomLivePivotCoverClosed) : AtomVertexCoverClosed := by
  classical
  intro atom scale hpos hmass hframe
  obtain ⟨pivot, slotOne, slotTwo, hpy, hpw, hyw, -, hcover⟩ :=
    hlive atom scale hpos hmass hframe
  refine ⟨{pivot, slotOne, slotTwo}, ?_, fun direction => ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hpy, hpw]), Finset.card_pair hyw]
  · have hsum : (∑ slot ∈ ({pivot, slotOne, slotTwo} : Finset (Fin 6)),
        (atom slot ⬝ᵥ direction) ^ 2 / scale slot)
        = (atom pivot ⬝ᵥ direction) ^ 2 / scale pivot
          + (atom slotOne ⬝ᵥ direction) ^ 2 / scale slotOne
          + (atom slotTwo ⬝ᵥ direction) ^ 2 / scale slotTwo := by
      rw [Finset.sum_insert (by simp [hpy, hpw]), Finset.sum_insert (by simp [hyw]),
        Finset.sum_singleton, add_assoc]
    rw [hsum]
    exact hcover direction

/-- **THE HEAVY ROUTE CLOSES THE CELL.**  It is stronger than the live one. -/
theorem atomVertexCoverClosed_of_heavyPivotCover
    (hheavy : AtomHeavyPivotCoverClosed) : AtomVertexCoverClosed :=
  atomVertexCoverClosed_of_livePivotCover
    (atomLivePivotCoverClosed_of_heavyPivotCover hheavy)

/-- **THE CELL FROM THE LIVE PIVOT SELECTION.** -/
theorem gtzWeighted_six_three_of_livePivotCover
    (hlive : AtomLivePivotCoverClosed) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_atomVertexCover (atomVertexCoverClosed_of_livePivotCover hlive)

/-- **THE CELL FROM THE REPAIRED PLANE ROUTE.**

**#BOGUS — THIS DOOR CANNOT OPEN.**  `Gtz.not_atomLivePivotPlaneCoverClosed`
(Gtz/Wave/PlaneRouteFoil.lean:348) refutes the hypothesis, with no hypothesis of
its own.  `Gtz.unopenableAtomDoors` (Gtz/Wave/WiringDoorLedger.lean) records the
pair.  Read the index in Gtz/Wave/WiringSynonymClass.lean before you spend a
cycle here. -/
theorem gtzWeighted_six_three_of_livePivotPlaneCover
    (hroute : AtomLivePivotPlaneCoverClosed) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_livePivotCover (atomLivePivotCoverClosed_of_livePlane hroute)

end Criteria

/-! ## Layer 1 — the foil -/

section Foil

/-- **THE FOIL.**  Six atoms in fifths.  The three columns of the integer
matrix over five are orthogonal of squared length twenty five, so the six
atoms resolve the identity.  The atoms of the slots zero, three and five are
parallel. -/
noncomputable def heavyFoilAtom : Fin 6 → (Fin 3 → ℝ) :=
  ![![1 / 5, -(1 / 5), 1 / 5],
    ![3 / 5, -(3 / 5), -(2 / 5)],
    ![2 / 5, 3 / 5, -(3 / 5)],
    ![-(1 / 5), 1 / 5, -(1 / 5)],
    ![-(3 / 5), -(2 / 5), -(3 / 5)],
    ![1 / 5, -(1 / 5), 1 / 5]]

/-- The scales of the foil.  Three slots carry `1/30` and three carry `3/10`,
of mass one. -/
noncomputable def heavyFoilScale : Fin 6 → ℝ :=
  ![1 / 30, 3 / 10, 3 / 10, 1 / 30, 3 / 10, 1 / 30]

theorem heavyFoilAtom_zero : heavyFoilAtom 0 = ![1 / 5, -(1 / 5), 1 / 5] := rfl

theorem heavyFoilAtom_one : heavyFoilAtom 1 = ![3 / 5, -(3 / 5), -(2 / 5)] := rfl

theorem heavyFoilAtom_two : heavyFoilAtom 2 = ![2 / 5, 3 / 5, -(3 / 5)] := rfl

theorem heavyFoilAtom_three : heavyFoilAtom 3 = ![-(1 / 5), 1 / 5, -(1 / 5)] := rfl

theorem heavyFoilAtom_four : heavyFoilAtom 4 = ![-(3 / 5), -(2 / 5), -(3 / 5)] := rfl

theorem heavyFoilAtom_five : heavyFoilAtom 5 = ![1 / 5, -(1 / 5), 1 / 5] := rfl

theorem heavyFoilScale_zero : heavyFoilScale 0 = 1 / 30 := rfl

theorem heavyFoilScale_one : heavyFoilScale 1 = 3 / 10 := rfl

theorem heavyFoilScale_two : heavyFoilScale 2 = 3 / 10 := rfl

theorem heavyFoilScale_three : heavyFoilScale 3 = 1 / 30 := rfl

theorem heavyFoilScale_four : heavyFoilScale 4 = 3 / 10 := rfl

theorem heavyFoilScale_five : heavyFoilScale 5 = 1 / 30 := rfl

/-- **THE ATOM OF SLOT FIVE REPEATS THE ATOM OF SLOT ZERO.** -/
theorem heavyFoilAtom_five_eq_zero : heavyFoilAtom 5 = heavyFoilAtom 0 := rfl

/-- **THE ATOM OF SLOT THREE IS THE NEGATIVE OF THE ATOM OF SLOT ZERO.** -/
theorem heavyFoilAtom_three_eq_neg (index : Fin 3) :
    heavyFoilAtom 3 index = -(heavyFoilAtom 0 index) := by
  rw [heavyFoilAtom_three, heavyFoilAtom_zero]
  fin_cases index <;> norm_num [foilCons3_2]

theorem heavyFoilScale_pos (slot : Fin 6) : 0 < heavyFoilScale slot := by
  fin_cases slot <;> norm_num [heavyFoilScale, foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]

theorem heavyFoilScale_sum : (∑ slot, heavyFoilScale slot) = 1 := by
  simp [Fin.sum_univ_six, heavyFoilScale, foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]
  norm_num

/-- **THE FOIL IS A TIGHT FRAME.**  The three columns of the integer matrix
are orthogonal of squared length twenty five. -/
theorem heavyFoilAtom_isTightFrame (probe direction : Fin 3 → ℝ) :
    (∑ slot, (heavyFoilAtom slot ⬝ᵥ probe) * (heavyFoilAtom slot ⬝ᵥ direction))
      = probe ⬝ᵥ direction := by
  simp [Fin.sum_univ_six, heavyFoilAtom, dotProduct, Fin.sum_univ_three, foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]
  ring

/-- The Gram of the foil, as a table of twenty fifths. -/
noncomputable def heavyFoilGram : Fin 6 → Fin 6 → ℝ :=
  ![![3 / 25, 4 / 25, -(4 / 25), -(3 / 25), -(4 / 25), 3 / 25],
    ![4 / 25, 22 / 25, 3 / 25, -(4 / 25), 3 / 25, 4 / 25],
    ![-(4 / 25), 3 / 25, 22 / 25, 4 / 25, -(3 / 25), -(4 / 25)],
    ![-(3 / 25), -(4 / 25), 4 / 25, 3 / 25, 4 / 25, -(3 / 25)],
    ![-(4 / 25), 3 / 25, -(3 / 25), 4 / 25, 22 / 25, -(4 / 25)],
    ![3 / 25, 4 / 25, -(4 / 25), -(3 / 25), -(4 / 25), 3 / 25]]

/-- **THE GRAM OF THE FOIL, IN CLOSED FORM.** -/
theorem heavyFoilGram_eq (rowSlot colSlot : Fin 6) :
    atomGram heavyFoilAtom rowSlot colSlot = heavyFoilGram rowSlot colSlot := by
  fin_cases rowSlot <;> fin_cases colSlot <;>
    norm_num [atomGram, heavyFoilAtom, heavyFoilGram, dotProduct, Fin.sum_univ_three,
      foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]

/-- The Gram diagonal of the foil reads `3/25` at three slots and `22/25` at
the other three. -/
theorem heavyFoilGram_diag (slot : Fin 6) :
    atomGram heavyFoilAtom slot slot
      = ![3 / 25, 22 / 25, 22 / 25, 3 / 25, 22 / 25, 3 / 25] slot := by
  fin_cases slot <;>
    norm_num [atomGram, heavyFoilAtom, dotProduct, Fin.sum_univ_three,
      foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]

end Foil

/-! ## Layer 2 — the heavy slots of the foil are exactly zero, three and five -/

section HeavySet

/-- **THE HEAVY TEST OF THE FOIL.**  The heavy slots are exactly zero, three
and five.  The heavy margin is `1/50`, and the light deficit is `1/50`. -/
theorem heavyFoil_heavy_iff (slot : Fin 6) :
    3 * heavyFoilScale slot ≤ atomGram heavyFoilAtom slot slot
      ↔ (slot = 0 ∨ slot = 3 ∨ slot = 5) := by
  rw [heavyFoilGram_diag]
  fin_cases slot <;> norm_num [heavyFoilScale, foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5] <;> decide

theorem heavyFoil_heavy_zero :
    3 * heavyFoilScale 0 ≤ atomGram heavyFoilAtom 0 0 :=
  (heavyFoil_heavy_iff 0).mpr (Or.inl rfl)

theorem heavyFoil_heavy_three :
    3 * heavyFoilScale 3 ≤ atomGram heavyFoilAtom 3 3 :=
  (heavyFoil_heavy_iff 3).mpr (Or.inr (Or.inl rfl))

theorem heavyFoil_heavy_five :
    3 * heavyFoilScale 5 ≤ atomGram heavyFoilAtom 5 5 :=
  (heavyFoil_heavy_iff 5).mpr (Or.inr (Or.inr rfl))

/-- The heavy margin of the foil, at the three heavy slots. -/
theorem heavyFoil_heavy_margin (slot : Fin 6)
    (hslot : slot = 0 ∨ slot = 3 ∨ slot = 5) :
    atomGram heavyFoilAtom slot slot - 3 * heavyFoilScale slot = 1 / 50 := by
  rcases hslot with rfl | rfl | rfl <;>
    rw [heavyFoilGram_diag] <;> norm_num [heavyFoilScale, foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]

/-- The light deficit of the foil, at the three light slots. -/
theorem heavyFoil_light_deficit (slot : Fin 6)
    (hslot : slot = 1 ∨ slot = 2 ∨ slot = 4) :
    atomGram heavyFoilAtom slot slot - 3 * heavyFoilScale slot = -(1 / 50) := by
  rcases hslot with rfl | rfl | rfl <;>
    rw [heavyFoilGram_diag] <;> norm_num [heavyFoilScale, foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]

/-- **EVERY SLOT OF THE FOIL IS LIVE.**  The pivot passage
`Gtz.atomPivotSchur_cover` therefore applies at each of them, and the
refutation lands on the heavy pigeonhole and on nothing else. -/
theorem heavyFoil_live (slot : Fin 6) :
    heavyFoilScale slot < atomGram heavyFoilAtom slot slot := by
  rw [heavyFoilGram_diag]
  fin_cases slot <;> norm_num [heavyFoilScale, foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]

end HeavySet

/-! ## Layer 3 — the six probes and the thirty six readings -/

section Probes

/-- The six probes of the refutation.  The first three are orthogonal to the
common direction of the three heavy atoms and to one light atom each.  The
last three separate the three pairs of light slots. -/
noncomputable def heavyFoilProbe : Fin 6 → (Fin 3 → ℝ) :=
  ![![1, 1, 0], ![0, 1, 1], ![1, 0, -1], ![1, 1, 1], ![1, 1, -1], ![1, -1, -1]]

/-- The energy of the six probes. -/
noncomputable def heavyFoilEnergy : Fin 6 → ℝ := ![2, 2, 2, 3, 3, 3]

/-- The reading table of the foil: the row is the probe and the column is the
slot.  The three heavy slots share one column, because their atoms are
parallel and their scales agree. -/
noncomputable def heavyFoilRead : Fin 6 → Fin 6 → ℝ :=
  ![![0, 0, 10 / 3, 0, 10 / 3, 0],
    ![0, 10 / 3, 0, 0, 10 / 3, 0],
    ![0, 10 / 3, 10 / 3, 0, 0, 0],
    ![6 / 5, 8 / 15, 8 / 15, 6 / 5, 128 / 15, 6 / 5],
    ![6 / 5, 8 / 15, 128 / 15, 6 / 5, 8 / 15, 6 / 5],
    ![6 / 5, 128 / 15, 8 / 15, 6 / 5, 8 / 15, 6 / 5]]

/-- The energy of each probe, in closed form. -/
theorem heavyFoilProbe_energy (probeIndex : Fin 6) :
    heavyFoilProbe probeIndex ⬝ᵥ heavyFoilProbe probeIndex = heavyFoilEnergy probeIndex := by
  fin_cases probeIndex <;>
    norm_num [heavyFoilProbe, heavyFoilEnergy, dotProduct, Fin.sum_univ_three,
      foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]

/-- **THE THIRTY SIX READINGS, IN CLOSED FORM.** -/
theorem heavyFoilRead_eq (probeIndex slot : Fin 6) :
    (heavyFoilAtom slot ⬝ᵥ heavyFoilProbe probeIndex) ^ 2 / heavyFoilScale slot
      = heavyFoilRead probeIndex slot := by
  fin_cases probeIndex <;> fin_cases slot <;>
    norm_num [heavyFoilAtom, heavyFoilScale, heavyFoilProbe, heavyFoilRead,
      dotProduct, Fin.sum_univ_three, foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]

end Probes

/-! ## Layer 4 — every triple through a heavy slot misses a probe -/

section TripleFailure

/-- **EVERY TRIPLE THROUGH A HEAVY SLOT MISSES A PROBE.**  A triple with two
heavy slots spans a plane and reads zero at one of the first three probes.  A
triple with one heavy slot reads `34/15` against the energy three at one of
the last three probes. -/
theorem heavyFoil_triple_fails (pivot slotOne slotTwo : Fin 6)
    (hpivot : pivot = 0 ∨ pivot = 3 ∨ pivot = 5)
    (hpy : pivot ≠ slotOne) (hpw : pivot ≠ slotTwo) (hyw : slotOne ≠ slotTwo) :
    ∃ probeIndex : Fin 6,
      heavyFoilRead probeIndex pivot + heavyFoilRead probeIndex slotOne
          + heavyFoilRead probeIndex slotTwo
        < heavyFoilEnergy probeIndex := by
  rcases hpivot with rfl | rfl | rfl <;>
    fin_cases slotOne <;> fin_cases slotTwo <;>
    first
      | (exfalso; revert hpy; decide)
      | (exfalso; revert hpw; decide)
      | (exfalso; revert hyw; decide)
      | (refine ⟨0, ?_⟩; norm_num [heavyFoilRead, heavyFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]; done)
      | (refine ⟨1, ?_⟩; norm_num [heavyFoilRead, heavyFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]; done)
      | (refine ⟨2, ?_⟩; norm_num [heavyFoilRead, heavyFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]; done)
      | (refine ⟨3, ?_⟩; norm_num [heavyFoilRead, heavyFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]; done)
      | (refine ⟨4, ?_⟩; norm_num [heavyFoilRead, heavyFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]; done)
      | (refine ⟨5, ?_⟩; norm_num [heavyFoilRead, heavyFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5])

/-- **NO TRIPLE THROUGH A HEAVY SLOT COVERS.**  The reading of the triple at
the missed probe is strictly below the probe energy. -/
theorem heavyFoil_heavyTriple_not_covers (pivot slotOne slotTwo : Fin 6)
    (hheavy : 3 * heavyFoilScale pivot ≤ atomGram heavyFoilAtom pivot pivot)
    (hpy : pivot ≠ slotOne) (hpw : pivot ≠ slotTwo) (hyw : slotOne ≠ slotTwo) :
    ¬ AtomTripleCovers heavyFoilAtom heavyFoilScale pivot slotOne slotTwo := by
  intro hcover
  obtain ⟨probeIndex, hlt⟩ :=
    heavyFoil_triple_fails pivot slotOne slotTwo
      ((heavyFoil_heavy_iff pivot).mp hheavy) hpy hpw hyw
  have hread := hcover (heavyFoilProbe probeIndex)
  rw [atomTripleRead, heavyFoilProbe_energy, heavyFoilRead_eq, heavyFoilRead_eq,
    heavyFoilRead_eq] at hread
  linarith

end TripleFailure

/-! ## Layer 5 — the refutation -/

section Refutation

/-- **THE HEAVY PIVOT SELECTION IS FALSE.**  At the foil the heavy slots are
exactly zero, three and five, their atoms are parallel, and every triple that
holds one of them misses a probe.  No heavy pivot sits in a covering triple. -/
theorem not_atomHeavyPivotCoverClosed : ¬ AtomHeavyPivotCoverClosed := by
  intro hclosed
  obtain ⟨pivot, slotOne, slotTwo, hpy, hpw, hyw, hheavy, hcover⟩ :=
    hclosed heavyFoilAtom heavyFoilScale heavyFoilScale_pos heavyFoilScale_sum
      heavyFoilAtom_isTightFrame
  exact heavyFoil_heavyTriple_not_covers pivot slotOne slotTwo hheavy hpy hpw hyw hcover

/-- **THE FULL HEAVY PLANE ROUTE IS FALSE.**  It carries the heavy selection,
which the foil refutes. -/
theorem not_atomHeavyPivotPlaneCoverClosed : ¬ AtomHeavyPivotPlaneCoverClosed :=
  fun hroute => not_atomHeavyPivotCoverClosed (atomHeavyPivotCoverClosed_of_heavyPlane hroute)

end Refutation

/-! ## Layer 6 — the foil does not refute the cell -/

section Calibration

/-- **THE FOIL CARRIES A COVERING TRIPLE.**  The three light slots one, two
and four dominate every direction.  The shifted form reads `29/15` on the
diagonal and `6/15` off it, and it is strictly positive. -/
theorem heavyFoil_cover_oneTwoFour (direction : Fin 3 → ℝ) :
    direction ⬝ᵥ direction
      ≤ (heavyFoilAtom 1 ⬝ᵥ direction) ^ 2 / heavyFoilScale 1
        + (heavyFoilAtom 2 ⬝ᵥ direction) ^ 2 / heavyFoilScale 2
        + (heavyFoilAtom 4 ⬝ᵥ direction) ^ 2 / heavyFoilScale 4 := by
  rw [heavyFoilAtom_one, heavyFoilAtom_two, heavyFoilAtom_four,
    heavyFoilScale_one, heavyFoilScale_two, heavyFoilScale_four]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    foilCons3_2]
  have hkey : (0 : ℝ)
      ≤ 17 * (direction 0 ^ 2 + direction 1 ^ 2 + direction 2 ^ 2)
        + 6 * ((direction 0 + direction 1) ^ 2 + (direction 1 + direction 2) ^ 2
          + (direction 0 - direction 2) ^ 2) := by
    positivity
  nlinarith [hkey, sq_nonneg (direction 0), sq_nonneg (direction 1), sq_nonneg (direction 2)]

/-- **THE FOIL REFUTES THE SELECTION AND NOT THE CELL.** -/
theorem heavyFoilAtom_hasVertexCover :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ direction : Fin 3 → ℝ,
          direction ⬝ᵥ direction
            ≤ ∑ slot ∈ car, (heavyFoilAtom slot ⬝ᵥ direction) ^ 2 / heavyFoilScale slot := by
  classical
  refine ⟨({1, 2, 4} : Finset (Fin 6)), by decide, fun direction => ?_⟩
  have hsum : (∑ slot ∈ ({1, 2, 4} : Finset (Fin 6)),
      (heavyFoilAtom slot ⬝ᵥ direction) ^ 2 / heavyFoilScale slot)
      = (heavyFoilAtom 1 ⬝ᵥ direction) ^ 2 / heavyFoilScale 1
        + (heavyFoilAtom 2 ⬝ᵥ direction) ^ 2 / heavyFoilScale 2
        + (heavyFoilAtom 4 ⬝ᵥ direction) ^ 2 / heavyFoilScale 4 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, add_assoc]
  rw [hsum]
  exact heavyFoil_cover_oneTwoFour direction

/-- **THE COVERING TRIPLE PASSES THE PLANE TEST.**  At the pivot one the pair
of the slots two and four dominates the plane at the full inflated scale
`1/(1 - t_1)`, with the margin `23/77`.  The foil therefore refutes the heavy
ingredient of the route and not the plane ingredient. -/
theorem heavyFoil_plane_oneTwoFour :
    AtomPairPlaneDominates heavyFoilAtom heavyFoilScale 1 2 4 := by
  intro probe hpolar
  rw [atomPivotPlaneRead, heavyFoilAtom_two, heavyFoilAtom_four,
    heavyFoilScale_one, heavyFoilScale_two, heavyFoilScale_four]
  rw [heavyFoilAtom_one] at hpolar
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    foilCons3_2] at hpolar ⊢
  have hthird : probe 2 = 3 / 2 * (probe 0 - probe 1) := by linarith
  rw [hthird]
  have hkey : (0 : ℝ) ≤ 31 * (probe 0 ^ 2 + probe 1 ^ 2) - 30 * (probe 0 * probe 1) := by
    nlinarith [sq_nonneg (probe 0 - probe 1), sq_nonneg (probe 0 + probe 1)]
  nlinarith [hkey]

end Calibration

/-! ## Layer 7 — the plane test and the cover test are not comparable -/

section PlaneCoverGap

/-- **THE GAP BETWEEN THE PLANE TEST AND THE COVER TEST AT A PIVOT.**

Both tests are two by two forms in the pair, written with the Schur complement
of the pivot.  The cover test divides the coupling square by the SHIFTED
diagonal `G_pp - t_p` and compares with the plain scales.  The plane test
divides by the plain diagonal `G_pp` and compares with the INFLATED scales.
Their difference is a rank one form minus a positive diagonal form, scaled by
the pivot scale.

The identity is pure algebra and it consumes no frame law. -/
theorem planeCoverGap (gramPivot scalePivot gramOne gramTwo diagOne diagTwo
    gramPair scaleOne scaleTwo first second : ℝ)
    (hpivot : gramPivot ≠ 0) (hgap : gramPivot - scalePivot ≠ 0)
    (hmass : 1 - scalePivot ≠ 0) :
    ((diagOne - scaleOne / (1 - scalePivot)) * first ^ 2
          + 2 * gramPair * (first * second)
          + (diagTwo - scaleTwo / (1 - scalePivot)) * second ^ 2
          - (gramOne * first + gramTwo * second) ^ 2 / gramPivot)
        - ((diagOne - scaleOne) * first ^ 2
          + 2 * gramPair * (first * second)
          + (diagTwo - scaleTwo) * second ^ 2
          - (gramOne * first + gramTwo * second) ^ 2 / (gramPivot - scalePivot))
      = scalePivot
        * ((gramOne * first + gramTwo * second) ^ 2
              / (gramPivot * (gramPivot - scalePivot))
            - (scaleOne * first ^ 2 + scaleTwo * second ^ 2) / (1 - scalePivot)) := by
  field_simp
  ring

/-- **THE GAP ACROSS THE COUPLING.**  At the vector that the coupling reads as
zero the rank one term drops out, and the gap is the negative of a positive
diagonal reading. -/
theorem planeCoverGap_polar (gramPivot scalePivot gramOne gramTwo diagOne diagTwo
    gramPair scaleOne scaleTwo : ℝ)
    (hpivot : gramPivot ≠ 0) (hgap : gramPivot - scalePivot ≠ 0)
    (hmass : 1 - scalePivot ≠ 0) :
    ((diagOne - scaleOne / (1 - scalePivot)) * gramTwo ^ 2
          + 2 * gramPair * (gramTwo * -gramOne)
          + (diagTwo - scaleTwo / (1 - scalePivot)) * (-gramOne) ^ 2
          - (gramOne * gramTwo + gramTwo * -gramOne) ^ 2 / gramPivot)
        - ((diagOne - scaleOne) * gramTwo ^ 2
          + 2 * gramPair * (gramTwo * -gramOne)
          + (diagTwo - scaleTwo) * (-gramOne) ^ 2
          - (gramOne * gramTwo + gramTwo * -gramOne) ^ 2 / (gramPivot - scalePivot))
      = -(scalePivot * (scaleOne * gramTwo ^ 2 + scaleTwo * gramOne ^ 2)
            / (1 - scalePivot)) := by
  rw [planeCoverGap gramPivot scalePivot gramOne gramTwo diagOne diagTwo gramPair
    scaleOne scaleTwo gramTwo (-gramOne) hpivot hgap hmass]
  have hzero : gramOne * gramTwo + gramTwo * -gramOne = 0 := by ring
  rw [hzero]
  field_simp
  ring

/-- **THE PLANE TEST IS STRICTLY HARDER ACROSS A LIVE COUPLING.**  At a
positive pivot scale below one, and a coupling that is not the zero vector,
the gap across the coupling is strictly negative.  A covering triple therefore
need NOT sit inside the feasible set of the plane theorem. -/
theorem planeCoverGap_polar_neg (scalePivot gramOne gramTwo scaleOne scaleTwo : ℝ)
    (hpos : 0 < scalePivot) (hless : scalePivot < 1)
    (honePos : 0 < scaleOne) (htwoPos : 0 < scaleTwo)
    (hlive : gramOne ≠ 0 ∨ gramTwo ≠ 0) :
    -(scalePivot * (scaleOne * gramTwo ^ 2 + scaleTwo * gramOne ^ 2)
        / (1 - scalePivot)) < 0 := by
  have hmass : 0 < 1 - scalePivot := by linarith
  have hnum : 0 < scaleOne * gramTwo ^ 2 + scaleTwo * gramOne ^ 2 := by
    rcases hlive with hone | htwo
    · have : 0 < gramOne ^ 2 := by positivity
      nlinarith [sq_nonneg gramTwo, mul_nonneg honePos.le (sq_nonneg gramTwo)]
    · have : 0 < gramTwo ^ 2 := by positivity
      nlinarith [sq_nonneg gramOne, mul_nonneg htwoPos.le (sq_nonneg gramOne)]
  have : 0 < scalePivot * (scaleOne * gramTwo ^ 2 + scaleTwo * gramOne ^ 2)
      / (1 - scalePivot) := by positivity
  linarith

end PlaneCoverGap

end Gtz

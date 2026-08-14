import Gtz.Wave.HeavyPivotFoil

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12800000

/-!
# The plane test cannot be part of the selection, at either pivot test

`Gtz.HeavyPivotFoil` refutes the HEAVY half of the pivot route.  The repair
that survives it selects a LIVE pivot instead, and the pivot passage
`Gtz.atomPivotSchur_cover` asks for nothing more.  The remaining question is
the PAIR: the route selects it by the plane theorem, at the full inflated
scale `1/(1 - t_p)`, and the boundary theorem
`Gtz.exists_dominatingPlanePair_boundary` supplies such a pair at every pivot.

**That selection is FALSE as well.**  This module refutes it at a second exact
foil, and the same foil refutes the heavy half again.  What survives is the
bare LIVE selection `Gtz.AtomLivePivotCoverClosed`, with no plane test in it.

## The foil

Six atoms over the square root of thirteen.  The integer table is

  `(-1, -1, -1)` three times, then `(1, 0, -3)`, `(-3, 1, 0)`, `(0, 3, -1)`.

Its three columns are orthogonal of squared length thirteen, so the six atoms
resolve the identity.  The scales are `1/30` three times and `3/10` three
times, of mass one.  The Gram diagonal reads `3/13` at the three repeated
slots and `10/13` at the other three.  The heavy test reads

  `3/13 - 3 * (1/30) = 17/130` at the slots zero, one and two,
  `10/13 - 3 * (3/10) = -(17/130)` at the slots three, four and five,

so the heavy slots are exactly zero, one and two, and their atoms are equal.

## The two refutations at one datum

The ONLY covering triple is the triple of the slots three, four and five.  It
holds no heavy slot, so the heavy selection dies again.  And at each of its
own three slots, taken as the pivot, the remaining pair FAILS the plane test
at the inflated scale, by `28/39` at an explicit polar probe.  No pivot and no
pair pass the plane test and cover together.

The nineteen triples that are not the covering one miss the identity at one of
six explicit probes.  Three of the probes are orthogonal to the repeated atom
and read only one light slot.  The other three read the whole triple and miss
by `4/39`, which is the tightest margin of the foil.

## What survives

`Gtz.AtomLivePivotCoverClosed` is not touched.  At this foil the slots three,
four and five are live and their triple covers, and at the foil of
`Gtz.HeavyPivotFoil` the slots one, two and four are live and their triple
covers.  The live selection still carries the cell, by
`Gtz.gtzWeighted_six_three_of_livePivotCover`.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.planeFoilVec`, `Gtz.planeFoilAtom`, `Gtz.planeFoilScale` — the foil.
* `Gtz.planeFoilAtom_dot`, `Gtz.planeFoilAtom_dot_sq`, `Gtz.planeFoilAtom_gram`
  — the square root of thirteen enters the readings only through its square,
  so every reading and every Gram entry of the foil is rational.
* `Gtz.planeFoilVec_frame`, `Gtz.planeFoilAtom_isTightFrame`,
  `Gtz.planeFoilScale_pos`, `Gtz.planeFoilScale_sum` — the datum is admissible.
* `Gtz.planeFoilGram_diag`, `Gtz.planeFoil_heavy_iff`, `Gtz.planeFoil_live` —
  the heavy slots are exactly zero, one and two, and every slot is live.
* `Gtz.planeFoilProbe`, `Gtz.planeFoilEnergy`, `Gtz.planeFoilRead`,
  `Gtz.planeFoilProbe_energy`, `Gtz.planeFoilRead_eq` — the six probes and the
  thirty six readings, in closed form.
* `Gtz.planeFoilPolar`, `Gtz.planeFoilPolarEnergy`, `Gtz.planeFoilPolarRead`,
  `Gtz.planeFoilPolar_energy`, `Gtz.planeFoilPolar_orth`,
  `Gtz.planeFoilPolarRead_eq` — one polar probe at every pivot, and the thirty
  six polar readings.
* `Gtz.planeFoil_cover_threeFourFive`, `Gtz.planeFoilAtom_hasVertexCover` —
  the covering triple, so the foil refutes the selection and not the cell.
* `Gtz.not_atomLivePivotPlaneCoverClosed` — **THE PLANE SELECTION IS FALSE**,
  at a live pivot and therefore at a heavy pivot as well.
* `Gtz.not_atomHeavyPivotCoverClosed_second`,
  `Gtz.not_atomHeavyPivotPlaneCoverClosed_second` — the same foil kills the
  heavy selection a second time, independently of the foil in fifths.

## Vacuity

The refutation is an exact rational computation at one named configuration.
`Gtz.AtomLivePivotCoverClosed` is not refuted here, and
`Gtz.gtzWeighted_six_three_of_livePivotCover` proves that it still carries the
cell.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the foil over the square root of thirteen -/

section Foil

/-- The INTEGER TABLE of the foil.  Its three columns are orthogonal of
squared length thirteen. -/
noncomputable def planeFoilVec : Fin 6 → (Fin 3 → ℝ) :=
  ![![-1, -1, -1], ![-1, -1, -1], ![-1, -1, -1],
    ![1, 0, -3], ![-3, 1, 0], ![0, 3, -1]]

/-- **THE FOIL.**  The integer table over the square root of thirteen. -/
noncomputable def planeFoilAtom (slot : Fin 6) : Fin 3 → ℝ :=
  fun index => planeFoilVec slot index / Real.sqrt 13

/-- The scales of the foil.  Three slots carry `1/30` and three carry `3/10`,
of mass one. -/
noncomputable def planeFoilScale : Fin 6 → ℝ :=
  ![1 / 30, 1 / 30, 1 / 30, 3 / 10, 3 / 10, 3 / 10]

theorem planeFoilRoot_pos : (0 : ℝ) < Real.sqrt 13 :=
  Real.sqrt_pos.mpr (by norm_num)

theorem planeFoilRoot_sq : Real.sqrt 13 * Real.sqrt 13 = 13 :=
  Real.mul_self_sqrt (by norm_num)

/-- **THE ROOT ENTERS ONLY THROUGH THE READING.**  A reading of the foil is a
reading of the integer table over the root. -/
theorem planeFoilAtom_dot (slot : Fin 6) (probe : Fin 3 → ℝ) :
    planeFoilAtom slot ⬝ᵥ probe = (planeFoilVec slot ⬝ᵥ probe) / Real.sqrt 13 := by
  simp only [planeFoilAtom, dotProduct, Fin.sum_univ_three]
  ring

/-- **EVERY SQUARED READING OF THE FOIL IS RATIONAL.** -/
theorem planeFoilAtom_dot_sq (slot : Fin 6) (probe : Fin 3 → ℝ) :
    (planeFoilAtom slot ⬝ᵥ probe) ^ 2 = (planeFoilVec slot ⬝ᵥ probe) ^ 2 / 13 := by
  rw [planeFoilAtom_dot, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)]

/-- **EVERY GRAM ENTRY OF THE FOIL IS RATIONAL.** -/
theorem planeFoilAtom_gram (rowSlot colSlot : Fin 6) :
    atomGram planeFoilAtom rowSlot colSlot
      = (planeFoilVec rowSlot ⬝ᵥ planeFoilVec colSlot) / 13 := by
  rw [atomGram, planeFoilAtom_dot,
    dotProduct_comm (planeFoilVec rowSlot) (planeFoilAtom colSlot), planeFoilAtom_dot,
    dotProduct_comm (planeFoilVec colSlot) (planeFoilVec rowSlot), div_div,
    planeFoilRoot_sq]

/-- The integer table resolves thirteen times the identity. -/
theorem planeFoilVec_frame (probe direction : Fin 3 → ℝ) :
    (∑ slot, (planeFoilVec slot ⬝ᵥ probe) * (planeFoilVec slot ⬝ᵥ direction))
      = 13 * (probe ⬝ᵥ direction) := by
  simp [Fin.sum_univ_six, planeFoilVec, dotProduct, Fin.sum_univ_three,
    foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
    foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]
  ring

/-- **THE FOIL IS A TIGHT FRAME.** -/
theorem planeFoilAtom_isTightFrame (probe direction : Fin 3 → ℝ) :
    (∑ slot, (planeFoilAtom slot ⬝ᵥ probe) * (planeFoilAtom slot ⬝ᵥ direction))
      = probe ⬝ᵥ direction := by
  have hsplit : (∑ slot, (planeFoilAtom slot ⬝ᵥ probe) * (planeFoilAtom slot ⬝ᵥ direction))
      = (∑ slot, (planeFoilVec slot ⬝ᵥ probe) * (planeFoilVec slot ⬝ᵥ direction))
        / (Real.sqrt 13 * Real.sqrt 13) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun slot _ => by
      rw [planeFoilAtom_dot, planeFoilAtom_dot]; ring
  rw [hsplit, planeFoilVec_frame, planeFoilRoot_sq]
  ring

theorem planeFoilScale_pos (slot : Fin 6) : 0 < planeFoilScale slot := by
  fin_cases slot <;>
    norm_num [planeFoilScale, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]

theorem planeFoilScale_sum : (∑ slot, planeFoilScale slot) = 1 := by
  simp [Fin.sum_univ_six, planeFoilScale, foilCons6_2, foilCons6_3, foilCons6_4,
    foilCons6_5]
  norm_num

/-- The Gram diagonal of the foil reads `3/13` at the three repeated slots and
`10/13` at the other three. -/
theorem planeFoilGram_diag (slot : Fin 6) :
    atomGram planeFoilAtom slot slot
      = ![3 / 13, 3 / 13, 3 / 13, 10 / 13, 10 / 13, 10 / 13] slot := by
  rw [planeFoilAtom_gram]
  fin_cases slot <;>
    norm_num [planeFoilVec, dotProduct, Fin.sum_univ_three, foilCons3_2, foilCons4_2,
      foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3,
      foilCons6_4, foilCons6_5]

/-- **THE HEAVY TEST OF THE FOIL.**  The heavy slots are exactly zero, one and
two, at the margin `17/130`. -/
theorem planeFoil_heavy_iff (slot : Fin 6) :
    3 * planeFoilScale slot ≤ atomGram planeFoilAtom slot slot
      ↔ (slot = 0 ∨ slot = 1 ∨ slot = 2) := by
  rw [planeFoilGram_diag]
  fin_cases slot <;>
    norm_num [planeFoilScale, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5] <;>
    decide

/-- **EVERY SLOT OF THE FOIL IS LIVE.** -/
theorem planeFoil_live (slot : Fin 6) :
    planeFoilScale slot < atomGram planeFoilAtom slot slot := by
  rw [planeFoilGram_diag]
  fin_cases slot <;>
    norm_num [planeFoilScale, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]

end Foil

/-! ## Layer 2 — the six probes that break the nineteen triples -/

section Probes

/-- The six probes.  The first three are orthogonal to the repeated atom and
read exactly one light slot.  The last three read the whole triple. -/
noncomputable def planeFoilProbe : Fin 6 → (Fin 3 → ℝ) :=
  ![![1, 0, -1], ![1, -1, 0], ![0, 1, -1],
    ![1, -7, 4], ![7, -4, -1], ![4, 1, -7]]

/-- The energy of the six probes. -/
noncomputable def planeFoilEnergy : Fin 6 → ℝ := ![2, 2, 2, 66, 66, 66]

/-- The reading table of the foil: the row is the probe and the column is the
slot.  The three repeated slots share one column. -/
noncomputable def planeFoilRead : Fin 6 → Fin 6 → ℝ :=
  ![![0, 0, 0, 160 / 39, 30 / 13, 10 / 39],
    ![0, 0, 0, 10 / 39, 160 / 39, 30 / 13],
    ![0, 0, 0, 30 / 13, 10 / 39, 160 / 39],
    ![120 / 13, 120 / 13, 120 / 13, 1210 / 39, 1000 / 39, 6250 / 39],
    ![120 / 13, 120 / 13, 120 / 13, 1000 / 39, 6250 / 39, 1210 / 39],
    ![120 / 13, 120 / 13, 120 / 13, 6250 / 39, 1210 / 39, 1000 / 39]]

theorem planeFoilProbe_energy (probeIndex : Fin 6) :
    planeFoilProbe probeIndex ⬝ᵥ planeFoilProbe probeIndex = planeFoilEnergy probeIndex := by
  fin_cases probeIndex <;>
    norm_num [planeFoilProbe, planeFoilEnergy, dotProduct, Fin.sum_univ_three,
      foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]

/-- **THE THIRTY SIX READINGS, IN CLOSED FORM.** -/
theorem planeFoilRead_eq (probeIndex slot : Fin 6) :
    (planeFoilAtom slot ⬝ᵥ planeFoilProbe probeIndex) ^ 2 / planeFoilScale slot
      = planeFoilRead probeIndex slot := by
  rw [planeFoilAtom_dot_sq]
  fin_cases probeIndex <;> fin_cases slot <;>
    norm_num [planeFoilVec, planeFoilProbe, planeFoilScale, planeFoilRead,
      dotProduct, Fin.sum_univ_three, foilCons3_2, foilCons4_2, foilCons4_3,
      foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3, foilCons6_4,
      foilCons6_5]

end Probes

/-! ## Layer 3 — one polar probe at every pivot -/

section Polar

/-- The POLAR PROBE of each slot.  The probe of a slot is orthogonal to the
atom of that slot, so the plane test of the route applies to it at that
pivot.  The three repeated slots share one probe. -/
noncomputable def planeFoilPolar : Fin 6 → (Fin 3 → ℝ) :=
  ![![1, -1, 0], ![1, -1, 0], ![1, -1, 0],
    ![3, 2, 1], ![1, 3, 2], ![2, 1, 3]]

/-- The energy of the six polar probes. -/
noncomputable def planeFoilPolarEnergy : Fin 6 → ℝ := ![2, 2, 2, 14, 14, 14]

/-- The reading table at the polar probes: the row is the pivot and the column
is the slot.  Each row reads zero at its own pivot. -/
noncomputable def planeFoilPolarRead : Fin 6 → Fin 6 → ℝ :=
  ![![0, 0, 0, 10 / 39, 160 / 39, 30 / 13],
    ![0, 0, 0, 10 / 39, 160 / 39, 30 / 13],
    ![0, 0, 0, 10 / 39, 160 / 39, 30 / 13],
    ![1080 / 13, 1080 / 13, 1080 / 13, 0, 490 / 39, 250 / 39],
    ![1080 / 13, 1080 / 13, 1080 / 13, 250 / 39, 0, 490 / 39],
    ![1080 / 13, 1080 / 13, 1080 / 13, 490 / 39, 250 / 39, 0]]

theorem planeFoilPolar_energy (pivot : Fin 6) :
    planeFoilPolar pivot ⬝ᵥ planeFoilPolar pivot = planeFoilPolarEnergy pivot := by
  fin_cases pivot <;>
    norm_num [planeFoilPolar, planeFoilPolarEnergy, dotProduct, Fin.sum_univ_three,
      foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]

/-- **EVERY PROBE IS POLAR AT ITS OWN SLOT.** -/
theorem planeFoilPolar_orth (pivot : Fin 6) :
    planeFoilAtom pivot ⬝ᵥ planeFoilPolar pivot = 0 := by
  rw [planeFoilAtom_dot]
  fin_cases pivot <;>
    norm_num [planeFoilVec, planeFoilPolar, dotProduct, Fin.sum_univ_three,
      foilCons3_2, foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
      foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5]

/-- **THE THIRTY SIX POLAR READINGS, IN CLOSED FORM.** -/
theorem planeFoilPolarRead_eq (pivot slot : Fin 6) :
    (planeFoilAtom slot ⬝ᵥ planeFoilPolar pivot) ^ 2 / planeFoilScale slot
      = planeFoilPolarRead pivot slot := by
  rw [planeFoilAtom_dot_sq]
  fin_cases pivot <;> fin_cases slot <;>
    norm_num [planeFoilVec, planeFoilPolar, planeFoilScale, planeFoilPolarRead,
      dotProduct, Fin.sum_univ_three, foilCons3_2, foilCons4_2, foilCons4_3,
      foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3, foilCons6_4,
      foilCons6_5]

end Polar

/-! ## Layer 4 — the covering triple -/

section Cover

/-- **THE FOIL CARRIES A COVERING TRIPLE.**  The three light slots three, four
and five dominate every direction.  The shifted form reads `91` against `30`
on the squared total, so the margin is strict. -/
theorem planeFoil_cover_threeFourFive (direction : Fin 3 → ℝ) :
    direction ⬝ᵥ direction
      ≤ (planeFoilAtom 3 ⬝ᵥ direction) ^ 2 / planeFoilScale 3
        + (planeFoilAtom 4 ⬝ᵥ direction) ^ 2 / planeFoilScale 4
        + (planeFoilAtom 5 ⬝ᵥ direction) ^ 2 / planeFoilScale 5 := by
  rw [planeFoilAtom_dot_sq, planeFoilAtom_dot_sq, planeFoilAtom_dot_sq]
  simp only [planeFoilVec, planeFoilScale, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, foilCons3_2,
    foilCons4_2, foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4,
    foilCons6_3, foilCons6_4, foilCons6_5]
  nlinarith [sq_nonneg (direction 0 - direction 1), sq_nonneg (direction 0 - direction 2),
    sq_nonneg (direction 1 - direction 2), sq_nonneg (direction 0),
    sq_nonneg (direction 1), sq_nonneg (direction 2)]

/-- **THE FOIL REFUTES THE SELECTION AND NOT THE CELL.** -/
theorem planeFoilAtom_hasVertexCover :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ direction : Fin 3 → ℝ,
          direction ⬝ᵥ direction
            ≤ ∑ slot ∈ car, (planeFoilAtom slot ⬝ᵥ direction) ^ 2 / planeFoilScale slot := by
  classical
  refine ⟨({3, 4, 5} : Finset (Fin 6)), by decide, fun direction => ?_⟩
  have hsum : (∑ slot ∈ ({3, 4, 5} : Finset (Fin 6)),
      (planeFoilAtom slot ⬝ᵥ direction) ^ 2 / planeFoilScale slot)
      = (planeFoilAtom 3 ⬝ᵥ direction) ^ 2 / planeFoilScale 3
        + (planeFoilAtom 4 ⬝ᵥ direction) ^ 2 / planeFoilScale 4
        + (planeFoilAtom 5 ⬝ᵥ direction) ^ 2 / planeFoilScale 5 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, add_assoc]
  rw [hsum]
  exact planeFoil_cover_threeFourFive direction

end Cover

/-! ## Layer 5 — the two refutations -/

section Refutation

set_option linter.unusedTactic false in
/-- **THE PLANE SELECTION IS FALSE.**  At the foil no pivot and no pair pass
the plane test at the inflated scale and cover together.  The only covering
triple is the triple of the slots three, four and five, and at each of its own
slots the remaining pair misses the plane test by `28/39`. -/
theorem not_atomLivePivotPlaneCoverClosed : ¬ AtomLivePivotPlaneCoverClosed := by
  intro hclosed
  obtain ⟨pivot, slotOne, slotTwo, hpy, hpw, hyw, -, hplane, hcover⟩ :=
    hclosed planeFoilAtom planeFoilScale planeFoilScale_pos planeFoilScale_sum
      planeFoilAtom_isTightFrame
  have hread : ∀ probeIndex : Fin 6, planeFoilEnergy probeIndex
      ≤ planeFoilRead probeIndex pivot + planeFoilRead probeIndex slotOne
        + planeFoilRead probeIndex slotTwo := by
    intro probeIndex
    have hstep := hcover (planeFoilProbe probeIndex)
    rwa [atomTripleRead, planeFoilProbe_energy, planeFoilRead_eq, planeFoilRead_eq,
      planeFoilRead_eq] at hstep
  have hpolar : planeFoilPolarEnergy pivot
      ≤ (1 - planeFoilScale pivot)
        * (planeFoilPolarRead pivot slotOne + planeFoilPolarRead pivot slotTwo) := by
    have hstep := hplane (planeFoilPolar pivot) (planeFoilPolar_orth pivot)
    rwa [atomPivotPlaneRead, planeFoilPolar_energy, planeFoilPolarRead_eq,
      planeFoilPolarRead_eq] at hstep
  fin_cases pivot <;> fin_cases slotOne <;> fin_cases slotTwo <;>
    first
      | (exfalso; revert hpy; decide)
      | (exfalso; revert hpw; decide)
      | (exfalso; revert hyw; decide)
      | (have hbad := hread 0; norm_num [planeFoilRead, planeFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3,
          foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5] at hbad; done)
      | (have hbad := hread 1; norm_num [planeFoilRead, planeFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3,
          foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5] at hbad; done)
      | (have hbad := hread 2; norm_num [planeFoilRead, planeFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3,
          foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5] at hbad; done)
      | (have hbad := hread 3; norm_num [planeFoilRead, planeFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3,
          foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5] at hbad; done)
      | (have hbad := hread 4; norm_num [planeFoilRead, planeFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3,
          foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5] at hbad; done)
      | (have hbad := hread 5; norm_num [planeFoilRead, planeFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3,
          foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5] at hbad; done)
      | (norm_num [planeFoilPolarRead, planeFoilPolarEnergy, planeFoilScale,
          foilCons3_2, foilCons4_2, foilCons4_3,
          foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5] at hpolar; done)

set_option linter.unusedTactic false in
/-- **THE HEAVY SELECTION IS FALSE, A SECOND TIME.**  The only covering triple
of this foil holds no heavy slot.  The refutation is independent of the foil in
fifths of `Gtz.HeavyPivotFoil`. -/
theorem not_atomHeavyPivotCoverClosed_second : ¬ AtomHeavyPivotCoverClosed := by
  intro hclosed
  obtain ⟨pivot, slotOne, slotTwo, hpy, hpw, hyw, hheavy, hcover⟩ :=
    hclosed planeFoilAtom planeFoilScale planeFoilScale_pos planeFoilScale_sum
      planeFoilAtom_isTightFrame
  have hset := (planeFoil_heavy_iff pivot).mp hheavy
  have hread : ∀ probeIndex : Fin 6, planeFoilEnergy probeIndex
      ≤ planeFoilRead probeIndex pivot + planeFoilRead probeIndex slotOne
        + planeFoilRead probeIndex slotTwo := by
    intro probeIndex
    have hstep := hcover (planeFoilProbe probeIndex)
    rwa [atomTripleRead, planeFoilProbe_energy, planeFoilRead_eq, planeFoilRead_eq,
      planeFoilRead_eq] at hstep
  rcases hset with rfl | rfl | rfl <;>
    fin_cases slotOne <;> fin_cases slotTwo <;>
    first
      | (exfalso; revert hpy; decide)
      | (exfalso; revert hpw; decide)
      | (exfalso; revert hyw; decide)
      | (have hbad := hread 0; norm_num [planeFoilRead, planeFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3,
          foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5] at hbad; done)
      | (have hbad := hread 1; norm_num [planeFoilRead, planeFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3,
          foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5] at hbad; done)
      | (have hbad := hread 2; norm_num [planeFoilRead, planeFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3,
          foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5] at hbad; done)
      | (have hbad := hread 3; norm_num [planeFoilRead, planeFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3,
          foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5] at hbad; done)
      | (have hbad := hread 4; norm_num [planeFoilRead, planeFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3,
          foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5] at hbad; done)
      | (have hbad := hread 5; norm_num [planeFoilRead, planeFoilEnergy, foilCons3_2, foilCons4_2, foilCons4_3,
          foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_2, foilCons6_3, foilCons6_4, foilCons6_5] at hbad; done)

/-- **THE FULL HEAVY PLANE ROUTE IS FALSE, A SECOND TIME.** -/
theorem not_atomHeavyPivotPlaneCoverClosed_second : ¬ AtomHeavyPivotPlaneCoverClosed :=
  fun hroute => not_atomHeavyPivotCoverClosed_second
    (atomHeavyPivotCoverClosed_of_heavyPlane hroute)

end Refutation

end Gtz

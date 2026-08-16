import Gtz.Wave.ThreeLinesHeavyLeverageFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The reading-cover cell is refutable

`Gtz.ThreeLinesReadingCoverCellFires` asks for one card-three selection that
contains a maximal conductance reading at EVERY probe.  That is a transversal
condition, not a designation, so the arguments that killed the five refuted
selectors do not transfer.  This file refutes it directly.

The mechanism is an owner count.  Call a label an OWNER when it is the strict
maximal reader at some probe.  Every owner must belong to the selection, so a
point with four owners admits no card-three cover at all.

* `Gtz.not_readingCoverCell_of_owners` — four owners refute every card-three
  reading cover, at any size and any direction family.
* `Gtz.readingCoverRefuterPoint` — an exact rational chart point at the slide
  one, with the four owners `0`, `1`, `3` and `2` at the four probes
  `(1,0,0)`, `(0,1,0)`, `(0,0,1)` and `(1,1,0)`.
* `Gtz.readingCoverCell_refuted` — the cell does not fire there.
* `Gtz.readingCoverRefuterPoint_vertexBudgetCellFires` — honest bookkeeping:
  the vertex budget cell DOES fire at that point, with every allocation one
  half.  The refutation removes the reading cover as a covering claim, and it
  does not exhibit a residual point.

The three line normals already force part of the transversal.  At the probe
`(1,0,0)` only the labels of the complement `{0,2,4}` read a nonzero value, at
`(0,1,0)` only `{1,2,5}`, and at `(0,0,1)` only `{3,4,5}`.  Those three sets
are exactly the complements of the three dependent lines, so a firing cell
already meets each of them.  The fourth probe `(1,1,0)` is what breaks the
count.
-/

namespace Gtz

open Matrix Finset

/-! ## Owners refute a card-three reading cover -/

/-- **Four owners refute every card-three reading cover.**  If more than three
labels are each the strict maximal reader at a probe of their own, then no
card-three selection contains a maximal reading at every probe.  Generic in the
size and in the direction family. -/
theorem not_readingCoverCell_of_owners {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (owners : Finset (Fin size)) (probeOf : Fin size → (Fin 3 → ℝ))
    (hstrict : ∀ owner ∈ owners, ∀ label : Fin size, label ≠ owner →
      mass label / weight label * (direction label ⬝ᵥ probeOf owner) ^ 2
        < mass owner / weight owner * (direction owner ⬝ᵥ probeOf owner) ^ 2)
    (hcount : 3 < owners.card) :
    ¬ ∃ selected : Finset (Fin size), selected.card = 3 ∧
      ∀ probe : Fin 3 → ℝ, ∃ good ∈ selected, ∀ label : Fin size,
        mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
          ≤ mass good / weight good * (direction good ⬝ᵥ probe) ^ 2 := by
  rintro ⟨selected, hcard, hcover⟩
  have hsub : owners ⊆ selected := by
    intro owner howner
    obtain ⟨good, hmem, hgood⟩ := hcover (probeOf owner)
    by_cases hEq : good = owner
    · exact hEq ▸ hmem
    · exact absurd (hgood owner) (not_le.mpr (hstrict owner howner good hEq))
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  omega

/-- The owner count refutes the three-lines reading-cover cell. -/
theorem not_threeLinesReadingCoverCellFires_of_owners (slide : ℝ)
    (point : DirectionChartPoint 6) (owners : Finset (Fin 6))
    (probeOf : Fin 6 → (Fin 3 → ℝ))
    (hstrict : ∀ owner ∈ owners, ∀ label : Fin 6, label ≠ owner →
      point.mass label / point.weight label
          * (threeLinesDirection slide label ⬝ᵥ probeOf owner) ^ 2
        < point.mass owner / point.weight owner
          * (threeLinesDirection slide owner ⬝ᵥ probeOf owner) ^ 2)
    (hcount : 3 < owners.card) :
    ¬ ThreeLinesReadingCoverCellFires slide point :=
  not_readingCoverCell_of_owners (threeLinesDirection slide) point.mass point.weight
    owners probeOf hstrict hcount

/-! ## The exact witness -/

/-- The refuter masses.  Against the uniform weight they give the conductance
readings `(2, 2, 1, 3, 1/2, 1/2)`. -/
noncomputable def readingCoverRefuterMass : Fin 6 → ℝ
  | 0 => 1 / 3
  | 1 => 1 / 3
  | 2 => 1 / 6
  | 3 => 1 / 2
  | 4 => 1 / 12
  | 5 => 1 / 12

/-- The refuter weights are uniform. -/
noncomputable def readingCoverRefuterWeight : Fin 6 → ℝ := fun _ => 1 / 6

/-- The four probes that expose the four owners.  The first three are the line
normals, the last is the diagonal of the first line. -/
noncomputable def readingCoverRefuterProbe : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![1, 1, 0]
  | 3 => ![0, 0, 1]
  | 4 => ![1, 0, 0]
  | 5 => ![1, 0, 0]

/-- The exact rational chart point that refutes the reading-cover cell. -/
noncomputable def readingCoverRefuterPoint : DirectionChartPoint 6 where
  mass := readingCoverRefuterMass
  weight := readingCoverRefuterWeight
  mass_pos := by intro label; fin_cases label <;> norm_num [readingCoverRefuterMass]
  weight_pos := by intro label; fin_cases label <;> norm_num [readingCoverRefuterWeight]
  weight_sum_one := by
    simp only [readingCoverRefuterWeight, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    norm_num

theorem readingCoverRefuterPoint_mass_eq :
    readingCoverRefuterPoint.mass = readingCoverRefuterMass := rfl

theorem readingCoverRefuterPoint_weight_eq :
    readingCoverRefuterPoint.weight = readingCoverRefuterWeight := rfl

/-- **The four owners.**  At its own probe each of the labels `0`, `1`, `2` and
`3` strictly beats every other label's reading. -/
theorem readingCoverRefuterPoint_owners :
    ∀ owner ∈ ({0, 1, 2, 3} : Finset (Fin 6)), ∀ label : Fin 6, label ≠ owner →
      readingCoverRefuterPoint.mass label / readingCoverRefuterPoint.weight label
          * (threeLinesDirection 1 label ⬝ᵥ readingCoverRefuterProbe owner) ^ 2
        < readingCoverRefuterPoint.mass owner / readingCoverRefuterPoint.weight owner
          * (threeLinesDirection 1 owner ⬝ᵥ readingCoverRefuterProbe owner) ^ 2 := by
  intro owner howner label hne
  fin_cases owner <;> fin_cases label
  all_goals first
    | (exfalso; revert howner; decide)
    | exact absurd rfl hne
    | (simp only [readingCoverRefuterPoint_mass_eq, readingCoverRefuterPoint_weight_eq,
          readingCoverRefuterMass, readingCoverRefuterWeight, readingCoverRefuterProbe,
          threeLinesDirection, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons];
       norm_num)

/-- **The reading-cover cell is refuted.**  At the slide one and at this exact
rational chart point no card-three selection carries a maximal conductance
reading at every probe. -/
theorem readingCoverCell_refuted :
    ¬ ThreeLinesReadingCoverCellFires 1 readingCoverRefuterPoint :=
  not_threeLinesReadingCoverCellFires_of_owners 1 readingCoverRefuterPoint
    {0, 1, 2, 3} readingCoverRefuterProbe readingCoverRefuterPoint_owners (by decide)

/-! ## The witness is covered elsewhere -/

/-- The uniform allocation, every entry one half. -/
noncomputable def halfAllocation : ThreeLinesPositiveAllocation where
  uAA := 1 / 2
  uAB := 1 / 2
  uAC := 1 / 2
  uBA := 1 / 2
  uBB := 1 / 2
  uBC := 1 / 2
  uCA := 1 / 2
  uCB := 1 / 2
  uCC := 1 / 2
  uAA_pos := by norm_num
  uAB_pos := by norm_num
  uAC_pos := by norm_num
  uBA_pos := by norm_num
  uBB_pos := by norm_num
  uBC_pos := by norm_num
  uCA_pos := by norm_num
  uCB_pos := by norm_num
  uCC_pos := by norm_num

/-- **Honest bookkeeping.**  The vertex budget cell fires at the refuter point
with the uniform allocation, so the refutation of the reading cover does not
exhibit a point of the A2 residual.  It removes the reading cover as a covering
claim, nothing more. -/
theorem readingCoverRefuterPoint_vertexBudgetCellFires :
    ThreeLinesVertexBudgetCellFires 1 readingCoverRefuterPoint := by
  refine ⟨halfAllocation, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [halfAllocation, readingCoverRefuterPoint_mass_eq,
      readingCoverRefuterPoint_weight_eq, readingCoverRefuterMass, readingCoverRefuterWeight]

/-- The refuter point therefore carries a strict card-three chart gap. -/
theorem readingCoverRefuterPoint_vertexTriple_posDef :
    (directionChartGap (threeLinesDirection 1) readingCoverRefuterPoint.mass
      readingCoverRefuterPoint.weight ({0, 1, 3} : Finset (Fin 6))).PosDef :=
  posDef_threeLines_vertexCell_of_fires 1 readingCoverRefuterPoint
    readingCoverRefuterPoint_vertexBudgetCellFires

/-- The refuter point is not a counterexample to A2. -/
theorem readingCoverRefuterPoint_exists_posDef :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection 1) readingCoverRefuterPoint.mass
        readingCoverRefuterPoint.weight selected).PosDef :=
  ⟨{0, 1, 3}, by decide, readingCoverRefuterPoint_vertexTriple_posDef⟩

end Gtz

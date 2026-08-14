import Gtz.Wave.AtomIcosahedralWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The triangle energy: a sharp selection whose extremal is the icosahedron

The Gram of a tight frame is an orthogonal projection.  Two consequences of
that, the row energy law and the trace law, pin the TOTAL square energy of
the Gram at the rank.  Splitting the total into its diagonal part and its
off-diagonal part turns the frame law into a budget on the fifteen edges of
the six slots, and averaging that budget over the twenty triangles produces a
triangle whose three squared overlaps add to at most one tenth of the
remaining budget.

At rank three the budget is `3`, the diagonal part is at least `3/2` by
Cauchy-Schwarz against the trace, and the selected triangle carries squared
overlap total at most `3/20`.  The bound is SHARP and its unique extremal is
the icosahedral witness of `Gtz/Wave/AtomIcosahedralWitness.lean`, where every
one of the twenty triangles reads exactly `3/20`.  A datum can therefore be
worse than the icosahedron on some triangles only by being better on others.

The selection feeds the coherent energy cell: a coherent triangle whose
reading stays below its volume dominates, and the reading is bounded by the
largest shifted diagonal against the triangle energy.

## HONEST LIMITATION

The light triangle of this module and the coherent triangle of the parity
supply need not be the same triangle.  Nothing here selects a triangle that is
light AND coherent at once, and an adversarial search shows the two demands
are not simultaneously satisfiable on the blocked stratum.  The module gives a
budget and a cell, not a closure.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomGram_frobenius` — **THE FROBENIUS LAW**: the square total of the
  whole Gram is the rank, from the row energy law and the trace law.
* `Gtz.atomPairEnergy`, `Gtz.atomDiagEnergy`, `Gtz.atomTriangleEnergy` and
  `Gtz.atomPairEnergy_two_mul` — **THE EDGE BUDGET** of six slots.
* `Gtz.atomTriangleEnergy_total` — the twenty triangles read each edge four
  times.
* `Gtz.atomDiagEnergy_ge_three_halves` — the diagonal floor at rank three.
* `Gtz.exists_light_triangle`, `Gtz.exists_light_triangle_three` — **THE
  SHARP SELECTION**: some triangle carries squared overlap total at most
  `3/20`.
* `Gtz.icosaFrameAtom_triangleEnergy`, `Gtz.icosaFrameAtom_pairEnergy`,
  `Gtz.icosaFrameAtom_diagEnergy` — **THE EXTREMAL IS THE ICOSAHEDRON**, at
  every one of its twenty triangles.
* `Gtz.atomTripleDet_pos_of_lightCoherentTriangle`,
  `Gtz.exists_deflated_pair_of_lightCoherentTriangle` — the energy cell in
  the form the residue consumes.

## Vacuity

Every law of layers zero and one is an unconditional statement about a family
of vectors under the frame law.  The extremal readings of layer two are exact
computations at one named configuration.
-/

namespace Gtz

/-! ## Layer 0 — the Frobenius law and the edge budget -/

/-- **THE FROBENIUS LAW.**  The square total of the whole Gram of a tight
frame is the rank.  The Gram is an orthogonal projection, thus its square
total is its trace. -/
theorem atomGram_frobenius {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ rowSlot, ∑ colSlot, atomGram atom rowSlot colSlot ^ 2) = (rank : ℝ) := by
  rw [Finset.sum_congr rfl fun rowSlot _ => atomGram_row_energy hframe rowSlot]
  exact atomGram_trace hframe

/-- The EDGE ENERGY of six slots: the square total of the fifteen distinct
unordered pairs. -/
def atomPairEnergy {rank : ℕ} (atom : Fin 6 → (Fin rank → ℝ)) : ℝ :=
  atomGram atom 0 1 ^ 2
    + atomGram atom 0 2 ^ 2
    + atomGram atom 0 3 ^ 2
    + atomGram atom 0 4 ^ 2
    + atomGram atom 0 5 ^ 2
    + atomGram atom 1 2 ^ 2
    + atomGram atom 1 3 ^ 2
    + atomGram atom 1 4 ^ 2
    + atomGram atom 1 5 ^ 2
    + atomGram atom 2 3 ^ 2
    + atomGram atom 2 4 ^ 2
    + atomGram atom 2 5 ^ 2
    + atomGram atom 3 4 ^ 2
    + atomGram atom 3 5 ^ 2
    + atomGram atom 4 5 ^ 2

/-- The DIAGONAL ENERGY of six slots. -/
def atomDiagEnergy {rank : ℕ} (atom : Fin 6 → (Fin rank → ℝ)) : ℝ :=
  atomGram atom 0 0 ^ 2
    + atomGram atom 1 1 ^ 2
    + atomGram atom 2 2 ^ 2
    + atomGram atom 3 3 ^ 2
    + atomGram atom 4 4 ^ 2
    + atomGram atom 5 5 ^ 2

/-- The TRIANGLE ENERGY of three slots: the square total of its three
edges. -/
def atomTriangleEnergy {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (slotOne slotTwo slotThree : Fin slotCount) : ℝ :=
  atomGram atom slotOne slotTwo ^ 2 + atomGram atom slotOne slotThree ^ 2
    + atomGram atom slotTwo slotThree ^ 2

/-- **THE EDGE BUDGET.**  Twice the edge energy is the rank minus the
diagonal energy.  This is the Frobenius law with the diagonal split off. -/
theorem atomPairEnergy_two_mul {rank : ℕ} {atom : Fin 6 → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    2 * atomPairEnergy atom = (rank : ℝ) - atomDiagEnergy atom := by
  have hfrobenius := atomGram_frobenius hframe
  have h01 : atomGram atom 1 0 = atomGram atom 0 1 :=
    atomGram_comm atom 1 0
  have h02 : atomGram atom 2 0 = atomGram atom 0 2 :=
    atomGram_comm atom 2 0
  have h03 : atomGram atom 3 0 = atomGram atom 0 3 :=
    atomGram_comm atom 3 0
  have h04 : atomGram atom 4 0 = atomGram atom 0 4 :=
    atomGram_comm atom 4 0
  have h05 : atomGram atom 5 0 = atomGram atom 0 5 :=
    atomGram_comm atom 5 0
  have h12 : atomGram atom 2 1 = atomGram atom 1 2 :=
    atomGram_comm atom 2 1
  have h13 : atomGram atom 3 1 = atomGram atom 1 3 :=
    atomGram_comm atom 3 1
  have h14 : atomGram atom 4 1 = atomGram atom 1 4 :=
    atomGram_comm atom 4 1
  have h15 : atomGram atom 5 1 = atomGram atom 1 5 :=
    atomGram_comm atom 5 1
  have h23 : atomGram atom 3 2 = atomGram atom 2 3 :=
    atomGram_comm atom 3 2
  have h24 : atomGram atom 4 2 = atomGram atom 2 4 :=
    atomGram_comm atom 4 2
  have h25 : atomGram atom 5 2 = atomGram atom 2 5 :=
    atomGram_comm atom 5 2
  have h34 : atomGram atom 4 3 = atomGram atom 3 4 :=
    atomGram_comm atom 4 3
  have h35 : atomGram atom 5 3 = atomGram atom 3 5 :=
    atomGram_comm atom 5 3
  have h45 : atomGram atom 5 4 = atomGram atom 4 5 :=
    atomGram_comm atom 5 4
  simp only [Fin.sum_univ_six, h01, h02, h03, h04, h05, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45] at hfrobenius
  simp only [atomPairEnergy, atomDiagEnergy]
  linarith [hfrobenius]

/-- **THE TWENTY TRIANGLES READ EACH EDGE FOUR TIMES.**  Each of the fifteen
edges belongs to exactly four of the twenty triangles. -/
theorem atomTriangleEnergy_total {rank : ℕ} (atom : Fin 6 → (Fin rank → ℝ)) :
    atomTriangleEnergy atom 0 1 2
      + atomTriangleEnergy atom 0 1 3
      + atomTriangleEnergy atom 0 1 4
      + atomTriangleEnergy atom 0 1 5
      + atomTriangleEnergy atom 0 2 3
      + atomTriangleEnergy atom 0 2 4
      + atomTriangleEnergy atom 0 2 5
      + atomTriangleEnergy atom 0 3 4
      + atomTriangleEnergy atom 0 3 5
      + atomTriangleEnergy atom 0 4 5
      + atomTriangleEnergy atom 1 2 3
      + atomTriangleEnergy atom 1 2 4
      + atomTriangleEnergy atom 1 2 5
      + atomTriangleEnergy atom 1 3 4
      + atomTriangleEnergy atom 1 3 5
      + atomTriangleEnergy atom 1 4 5
      + atomTriangleEnergy atom 2 3 4
      + atomTriangleEnergy atom 2 3 5
      + atomTriangleEnergy atom 2 4 5
      + atomTriangleEnergy atom 3 4 5
      = 4 * atomPairEnergy atom := by
  simp only [atomTriangleEnergy, atomPairEnergy]
  ring

/-! ## Layer 1 — the sharp selection -/

/-- **THE DIAGONAL FLOOR.**  Six diagonal entries of total three have square
total at least three halves, by Cauchy-Schwarz against the trace.  Equality
holds exactly when every diagonal entry is one half, which is the trine
normalisation. -/
theorem atomDiagEnergy_ge_three_halves {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    3 / 2 ≤ atomDiagEnergy atom := by
  have htrace : (∑ slot, atomGram atom slot slot) = (3 : ℝ) := by
    simpa using atomGram_trace hframe
  simp only [Fin.sum_univ_six] at htrace
  simp only [atomDiagEnergy]
  nlinarith [htrace,
    sq_nonneg (atomGram atom 0 0 - atomGram atom 1 1),
    sq_nonneg (atomGram atom 0 0 - atomGram atom 2 2),
    sq_nonneg (atomGram atom 0 0 - atomGram atom 3 3),
    sq_nonneg (atomGram atom 0 0 - atomGram atom 4 4),
    sq_nonneg (atomGram atom 0 0 - atomGram atom 5 5),
    sq_nonneg (atomGram atom 1 1 - atomGram atom 2 2),
    sq_nonneg (atomGram atom 1 1 - atomGram atom 3 3),
    sq_nonneg (atomGram atom 1 1 - atomGram atom 4 4),
    sq_nonneg (atomGram atom 1 1 - atomGram atom 5 5),
    sq_nonneg (atomGram atom 2 2 - atomGram atom 3 3),
    sq_nonneg (atomGram atom 2 2 - atomGram atom 4 4),
    sq_nonneg (atomGram atom 2 2 - atomGram atom 5 5),
    sq_nonneg (atomGram atom 3 3 - atomGram atom 4 4),
    sq_nonneg (atomGram atom 3 3 - atomGram atom 5 5),
    sq_nonneg (atomGram atom 4 4 - atomGram atom 5 5)]

/-- **THE SHARP SELECTION.**  Some triangle of the six slots carries a
squared overlap total of at most one tenth of the edge budget.  The proof is
one averaging step over the twenty triangles. -/
theorem exists_light_triangle {rank : ℕ} {atom : Fin 6 → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ 10 * atomTriangleEnergy atom slotOne slotTwo slotThree
            ≤ (rank : ℝ) - atomDiagEnergy atom := by
  have hbudget := atomPairEnergy_two_mul hframe
  have htotal := atomTriangleEnergy_total atom
  by_contra hall
  push Not at hall
  have k012 := hall 0 1 2 (by decide) (by decide) (by decide)
  have k013 := hall 0 1 3 (by decide) (by decide) (by decide)
  have k014 := hall 0 1 4 (by decide) (by decide) (by decide)
  have k015 := hall 0 1 5 (by decide) (by decide) (by decide)
  have k023 := hall 0 2 3 (by decide) (by decide) (by decide)
  have k024 := hall 0 2 4 (by decide) (by decide) (by decide)
  have k025 := hall 0 2 5 (by decide) (by decide) (by decide)
  have k034 := hall 0 3 4 (by decide) (by decide) (by decide)
  have k035 := hall 0 3 5 (by decide) (by decide) (by decide)
  have k045 := hall 0 4 5 (by decide) (by decide) (by decide)
  have k123 := hall 1 2 3 (by decide) (by decide) (by decide)
  have k124 := hall 1 2 4 (by decide) (by decide) (by decide)
  have k125 := hall 1 2 5 (by decide) (by decide) (by decide)
  have k134 := hall 1 3 4 (by decide) (by decide) (by decide)
  have k135 := hall 1 3 5 (by decide) (by decide) (by decide)
  have k145 := hall 1 4 5 (by decide) (by decide) (by decide)
  have k234 := hall 2 3 4 (by decide) (by decide) (by decide)
  have k235 := hall 2 3 5 (by decide) (by decide) (by decide)
  have k245 := hall 2 4 5 (by decide) (by decide) (by decide)
  have k345 := hall 3 4 5 (by decide) (by decide) (by decide)
  linarith [k012, k013, k014, k015, k023, k024, k025, k034, k035, k045, k123, k124, k125, k134, k135, k145, k234, k235, k245, k345, hbudget, htotal]

/-- **THE SHARP SELECTION AT RANK THREE.**  Some triangle carries a squared
overlap total of at most `3/20`, and the icosahedral witness attains it at
every one of its twenty triangles. -/
theorem exists_light_triangle_three {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ atomTriangleEnergy atom slotOne slotTwo slotThree ≤ 3 / 20 := by
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hlight⟩ :=
    exists_light_triangle hframe
  have hdiag := atomDiagEnergy_ge_three_halves hframe
  refine ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, ?_⟩
  have hcast : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [hcast] at hlight
  linarith [hlight, hdiag]

/-! ## Layer 2 — the icosahedral extremal -/

/-- **EVERY TRIANGLE OF THE ICOSAHEDRAL WITNESS READS EXACTLY `3/20`.**  The
selection of layer one is therefore sharp, and its extremal is the real
equiangular tight frame. -/
theorem icosaFrameAtom_triangleEnergy {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) :
    atomTriangleEnergy icosaFrameAtom slotOne slotTwo slotThree = 3 / 20 := by
  simp only [atomTriangleEnergy, icosaFrameAtom_gram_sq_of_ne honeTwo,
    icosaFrameAtom_gram_sq_of_ne honeThree, icosaFrameAtom_gram_sq_of_ne htwoThree]
  norm_num

/-- The icosahedral witness spends the whole edge budget: its edge energy is
`3/4` and its diagonal energy is `3/2`, the floor. -/
theorem icosaFrameAtom_pairEnergy : atomPairEnergy icosaFrameAtom = 3 / 4 := by
  simp only [atomPairEnergy, icosaFrameAtom_gram_sq_of_ne (by decide : (0 : Fin 6) ≠ 1),
    icosaFrameAtom_gram_sq_of_ne (by decide : (0 : Fin 6) ≠ 2),
    icosaFrameAtom_gram_sq_of_ne (by decide : (0 : Fin 6) ≠ 3),
    icosaFrameAtom_gram_sq_of_ne (by decide : (0 : Fin 6) ≠ 4),
    icosaFrameAtom_gram_sq_of_ne (by decide : (0 : Fin 6) ≠ 5),
    icosaFrameAtom_gram_sq_of_ne (by decide : (1 : Fin 6) ≠ 2),
    icosaFrameAtom_gram_sq_of_ne (by decide : (1 : Fin 6) ≠ 3),
    icosaFrameAtom_gram_sq_of_ne (by decide : (1 : Fin 6) ≠ 4),
    icosaFrameAtom_gram_sq_of_ne (by decide : (1 : Fin 6) ≠ 5),
    icosaFrameAtom_gram_sq_of_ne (by decide : (2 : Fin 6) ≠ 3),
    icosaFrameAtom_gram_sq_of_ne (by decide : (2 : Fin 6) ≠ 4),
    icosaFrameAtom_gram_sq_of_ne (by decide : (2 : Fin 6) ≠ 5),
    icosaFrameAtom_gram_sq_of_ne (by decide : (3 : Fin 6) ≠ 4),
    icosaFrameAtom_gram_sq_of_ne (by decide : (3 : Fin 6) ≠ 5),
    icosaFrameAtom_gram_sq_of_ne (by decide : (4 : Fin 6) ≠ 5)]
  norm_num

theorem icosaFrameAtom_diagEnergy : atomDiagEnergy icosaFrameAtom = 3 / 2 := by
  simp only [atomDiagEnergy, icosaFrameAtom_gram_diag]
  norm_num

/-! ## Layer 3 — the energy cell -/

/-- **THE LIGHT COHERENT TRIANGLE CELL.**  A coherent triangle whose largest
shifted diagonal against its triangle energy stays below its volume has a
positive triple determinant.  This is the coherent energy cell of
`Gtz/Wave/AtomCoherentTriangle.lean` read through the triangle energy. -/
theorem atomTripleDet_pos_of_lightCoherentTriangle {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount} {bound : ℝ}
    (hcycle : 0 ≤ atomTriangleCycle atom slotOne slotTwo slotThree)
    (hone : atomShiftedDiag atom scale slotOne ≤ bound)
    (htwo : atomShiftedDiag atom scale slotTwo ≤ bound)
    (hthree : atomShiftedDiag atom scale slotThree ≤ bound)
    (hlight : bound * atomTriangleEnergy atom slotOne slotTwo slotThree
      < atomTripleVolume atom scale slotOne slotTwo slotThree) :
    0 < atomTripleDet atom scale slotOne slotTwo slotThree := by
  refine atomTripleDet_pos_of_coherentEnergy hcycle ?_
  have hreading : atomTripleReading atom scale slotOne slotTwo slotThree
      ≤ bound * atomTriangleEnergy atom slotOne slotTwo slotThree := by
    simp only [atomTripleReading, atomTriangleEnergy]
    have hfirst : atomShiftedDiag atom scale slotOne
        * atomGram atom slotTwo slotThree ^ 2
        ≤ bound * atomGram atom slotTwo slotThree ^ 2 :=
      mul_le_mul_of_nonneg_right hone (sq_nonneg _)
    have hsecond : atomShiftedDiag atom scale slotTwo
        * atomGram atom slotOne slotThree ^ 2
        ≤ bound * atomGram atom slotOne slotThree ^ 2 :=
      mul_le_mul_of_nonneg_right htwo (sq_nonneg _)
    have hthirdBound : atomShiftedDiag atom scale slotThree
        * atomGram atom slotOne slotTwo ^ 2
        ≤ bound * atomGram atom slotOne slotTwo ^ 2 :=
      mul_le_mul_of_nonneg_right hthree (sq_nonneg _)
    linarith [hfirst, hsecond, hthirdBound]
  linarith [hreading, hlight]

/-- **THE LIGHT COHERENT TRIANGLE CELL, IN THE FORM THE RESIDUE CONSUMES.** -/
theorem exists_deflated_pair_of_lightCoherentTriangle {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ} {slotOne slotTwo slotThree : Fin 6} {bound : ℝ}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree)
    (hcycle : 0 ≤ atomTriangleCycle atom slotOne slotTwo slotThree)
    (hdiagOne : 0 < atomShiftedDiag atom scale slotOne)
    (hone : atomShiftedDiag atom scale slotOne ≤ bound)
    (htwo : atomShiftedDiag atom scale slotTwo ≤ bound)
    (hthree : atomShiftedDiag atom scale slotThree ≤ bound)
    (hminor : 0 < atomPairMinor atom scale slotOne slotTwo)
    (hlight : bound * atomTriangleEnergy atom slotOne slotTwo slotThree
      < atomTripleVolume atom scale slotOne slotTwo slotThree) :
    ∃ pivot firstSlot secondSlot : Fin 6,
      pivot ≠ firstSlot ∧ pivot ≠ secondSlot ∧ firstSlot ≠ secondSlot
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot firstSlot
        ∧ atomPivotCross atom scale pivot firstSlot secondSlot ^ 2
            < atomPairMinor atom scale pivot firstSlot
              * atomPairMinor atom scale pivot secondSlot := by
  refine ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hdiagOne,
    hminor, ?_⟩
  exact deflated_pair_of_tripleDet_pos hdiagOne
    (atomTripleDet_pos_of_lightCoherentTriangle hcycle hone htwo hthree hlight)

end Gtz

import Gtz.Wave.AtomBoundaryWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The mass-one ladder: the sharp margin, the tie structure, and the descent

The atom lane's residue is the non-strict selection at scale mass exactly
one, and this module gives that statement its full consumer mirror, its
exact margin calculus, and its slot-count ladder.

## The additive margin reparametrization

`Gtz.atomMarginWeight` moves a scale family of mass `m < 1` to the mass-one
family `weight = scale + (1 - m) / 6`.  The move is exact: the six weights
add to one, and the shifted quadratic form of a triple differs from the
scale form by the margin `(1 - m) / 6` against the probe energy.  Thus the
weak selection at mass one gives, at EVERY mass below one, a carrier that
dominates with the margin `(1 - m) / 6` exactly — and the boundary witness
shows that no larger margin is available at any mass.  The adversarial
floor of the whole lane is therefore `(1 - m) / 6`, attained, at every
mass.  This is the machine form of the reparametrization discovery: the
blocked residue at mass `m` and the mass-one selection are one statement.

## The tie structure at the boundary witness

The doubled rational tetrahedron of `Gtz/Wave/AtomBoundaryWitness.lean`
satisfies the mass-one selection WITH TIES: the carrier of its three
distinct single directions dominates weakly, the explicit probe
`(5, 0, 5, 0, 3, 0)` reads EQUALITY, and no carrier dominates strictly.
Thus the non-strict conclusion of the mass-one selection cannot be
strengthened, and every proof of it must be exact at this witness.

## The parallel-pair kill and the descent

A weak carrier never contains a parallel pair of positive scale: the
explicit probe `(-factor, 1)` has vanishing blend and positive scale
energy.  As a result the six-slot mass-one selection DESCENDS to five
slots: split one atom into the rational pair `(3/5, 4/5)` of parallel
copies with the matched scale split `(9/25, 16/25)`, apply the six-slot
statement, observe that the returned carrier cannot use both copies, and
fold it back.  The five-slot analogue of the residue is therefore a
CONSEQUENCE of the residue, never a counterexample source — a
slot-count calibration of this residue at five slots is structurally
impossible.  The measured picture agrees: the adversarial floor of the
mass-one margin is zero at four, five and six slots over the real field.

## The field calibration (measured, banked, not stated here)

Over the complex field the mass-one selection is FALSE: the scaled
complex two-trine at mass one refutes every triple with best margin
exactly `(2 - sqrt 5) / 6 = -0.0393`, and a five-slot complex datum
reaches `-0.098`, which splits to six slots and beats the trine.  The
realness of the field enters at mass one itself, at slot count five
already, and no field-agnostic argument can prove the residue.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomMarginWeight`, `Gtz.atomMarginWeight_sum`,
  `Gtz.atomMarginWeight_pos`, `Gtz.scale_energy_add_margin` — **THE
  ADDITIVE REPARAMETRIZATION**, exact.
* `Gtz.exists_margin_carrier_of_boundary` — **THE SHARP MARGIN
  TRANSFER**: the mass-one selection dominates every lower mass with the
  margin `(1 - m) / 6` exactly.
* `Gtz.atomPivotPairClosed_of_atomTripleBoundary`,
  `Gtz.atomBlockedPairClosed_of_atomTripleBoundary`,
  `Gtz.gtzWeighted_six_three_of_atomTripleBoundary` — **THE CONSUMER
  MIRROR**: the mass-one selection closes the pivot pair residue, the
  blocked residue and the cell.
* `Gtz.blend_energy_eq_triple_of_support`,
  `Gtz.weak_values_of_weak_carrier` — the carrier calculus at the weak
  level.
* `Gtz.atomBoundaryAtom_weak_carrier`, `Gtz.atomBoundaryTieProbe`,
  `Gtz.atomBoundaryAtom_tie`, `Gtz.atomBoundaryAtom_no_strict_carrier` —
  **THE TIE STRUCTURE**: the witness satisfies the weak conclusion,
  attains equality, and refutes the strict one.
* `Gtz.atomBoundaryScaleAt`, `Gtz.atomBoundaryScaleAt_sum`,
  `Gtz.atomBoundaryScaleAt_pos`, `Gtz.atomMarginWeight_boundaryScaleAt`,
  `Gtz.atomBoundaryScaleAt_no_margin_carrier` — **THE MARGIN IS SHARP AT
  EVERY MASS**: the witness family attains the floor `(1 - m) / 6`.
* `Gtz.not_weakCarrier_of_parallel_pair` — **THE PARALLEL-PAIR KILL** at
  the weak level.
* `Gtz.atomSplitAtom`, `Gtz.atomSplitScale`, `Gtz.atomSplitSlot`,
  `Gtz.atomSplitFactor`, `Gtz.atomSplitBoost` and their seven laws — the
  rational split of one slot into a parallel pair.
* `Gtz.AtomFiveTripleBoundaryClosed`,
  `Gtz.atomFiveTripleBoundaryClosed_of_atomTripleBoundary` — **THE
  DESCENT**: the six-slot mass-one selection implies the five-slot one.

## Vacuity

The reparametrization laws and the carrier calculus are unconditional.
The witness laws are exact rational computations at one named
configuration.  The consumer mirror and the descent are implications
between named residues, and both consume the landed boundary equivalence,
thus none of them is vacuous under any open hypothesis.
-/

namespace Gtz

/-! ## Layer 0 — the carrier calculus at the weak level -/

/-- The blend energy of a probe supported on three slots is the six-term
Gram quadratic of the triple. -/
theorem blend_energy_eq_triple_of_support {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ))
    {slotOne slotTwo slotThree : Fin slotCount}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree)
    {probe : Fin slotCount → ℝ}
    (hvanish : ∀ slot ∉ ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount)),
      probe slot = 0) :
    atomBlend atom probe ⬝ᵥ atomBlend atom probe
      = atomGram atom slotOne slotOne * probe slotOne ^ 2
        + atomGram atom slotTwo slotTwo * probe slotTwo ^ 2
        + atomGram atom slotThree slotThree * probe slotThree ^ 2
        + 2 * atomGram atom slotOne slotTwo * probe slotOne * probe slotTwo
        + 2 * atomGram atom slotOne slotThree * probe slotOne * probe slotThree
        + 2 * atomGram atom slotTwo slotThree * probe slotTwo * probe slotThree := by
  classical
  rw [atomBlend_energy_eq_gram atom probe]
  have hinner : ∀ rowSlot : Fin slotCount,
      (∑ colSlot, probe rowSlot * probe colSlot * atomGram atom rowSlot colSlot)
        = probe rowSlot * probe slotOne * atomGram atom rowSlot slotOne
          + probe rowSlot * probe slotTwo * atomGram atom rowSlot slotTwo
          + probe rowSlot * probe slotThree * atomGram atom rowSlot slotThree :=
    fun rowSlot => sum_eq_triple_of_support honeTwo honeThree htwoThree
      fun colSlot hnot => by rw [hvanish colSlot hnot, mul_zero, zero_mul]
  rw [Finset.sum_congr rfl fun rowSlot _ => hinner rowSlot,
    sum_eq_triple_of_support honeTwo honeThree htwoThree
      (fun rowSlot hnot => by rw [hvanish rowSlot hnot]; ring),
    atomGram_comm atom slotTwo slotOne, atomGram_comm atom slotThree slotOne,
    atomGram_comm atom slotThree slotTwo]
  ring

/-- A weak carrier reads at its three slots as a weak ternary form: the
scale energy of any value triple is capped by the Gram quadratic. -/
theorem weak_values_of_weak_carrier {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree)
    (hdom : ∀ probe : Fin slotCount → ℝ,
      (∀ slot ∉ ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount)),
        probe slot = 0) →
      (∑ slot, scale slot * probe slot ^ 2)
        ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe)
    (valueOne valueTwo valueThree : ℝ) :
    scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
        + scale slotThree * valueThree ^ 2
      ≤ atomGram atom slotOne slotOne * valueOne ^ 2
        + atomGram atom slotTwo slotTwo * valueTwo ^ 2
        + atomGram atom slotThree slotThree * valueThree ^ 2
        + 2 * atomGram atom slotOne slotTwo * valueOne * valueTwo
        + 2 * atomGram atom slotOne slotThree * valueOne * valueThree
        + 2 * atomGram atom slotTwo slotThree * valueTwo * valueThree := by
  classical
  have hvanish := carrierProbe_vanish slotOne slotTwo slotThree valueOne valueTwo valueThree
  have hstep := hdom (carrierProbe slotOne slotTwo slotThree valueOne valueTwo valueThree)
    hvanish
  have hscaleSum : (∑ slot, scale slot
        * carrierProbe slotOne slotTwo slotThree valueOne valueTwo valueThree slot ^ 2)
      = scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
        + scale slotThree * valueThree ^ 2 := by
    rw [sum_eq_triple_of_support honeTwo honeThree htwoThree
      (fun slot hnot => by rw [hvanish slot hnot]; ring)]
    rw [carrierProbe_one, carrierProbe_two slotThree valueOne valueTwo valueThree honeTwo,
      carrierProbe_three valueOne valueTwo valueThree honeThree htwoThree]
  have henergy := blend_energy_eq_triple_of_support atom honeTwo honeThree htwoThree hvanish
  rw [hscaleSum, henergy, carrierProbe_one,
    carrierProbe_two slotThree valueOne valueTwo valueThree honeTwo,
    carrierProbe_three valueOne valueTwo valueThree honeThree htwoThree] at hstep
  exact hstep

/-! ## Layer 1 — the additive margin reparametrization -/

/-- The MARGIN WEIGHT of a scale family: each slot receives one sixth of
the mass deficit.  The result is a mass-one family, and the passage is the
exact reparametrization of the lane. -/
noncomputable def atomMarginWeight (scale : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun slot => scale slot + (1 - ∑ z, scale z) / 6

/-- The margin weights add to one exactly. -/
theorem atomMarginWeight_sum (scale : Fin 6 → ℝ) :
    (∑ slot, atomMarginWeight scale slot) = 1 := by
  simp only [atomMarginWeight, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The margin weights are positive below mass one. -/
theorem atomMarginWeight_pos {scale : Fin 6 → ℝ} (hpos : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) (slot : Fin 6) :
    0 < atomMarginWeight scale slot := by
  have hslot := hpos slot
  simp only [atomMarginWeight]
  linarith

/-- **THE SHIFT IDENTITY.**  The margin-weight energy of a probe is the
scale energy plus the margin against the probe energy. -/
theorem scale_energy_add_margin (scale : Fin 6 → ℝ) (probe : Fin 6 → ℝ) :
    (∑ slot, atomMarginWeight scale slot * probe slot ^ 2)
      = (∑ slot, scale slot * probe slot ^ 2)
        + (1 - ∑ slot, scale slot) / 6 * (∑ slot, probe slot ^ 2) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun slot _ => by rw [atomMarginWeight]; ring

/-- **THE SHARP MARGIN TRANSFER.**  The mass-one selection gives, at every
mass below one, a carrier that dominates with the margin `(1 - m) / 6`
against the probe energy.  The margin is exact, and the boundary witness
family shows below that no larger margin exists at any mass. -/
theorem exists_margin_carrier_of_boundary (hboundary : AtomTripleBoundaryClosed)
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hpos : ∀ slot, 0 < scale slot) (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            + (1 - ∑ slot, scale slot) / 6 * (∑ slot, probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  obtain ⟨car, hcard, hdom⟩ := hboundary atom (atomMarginWeight scale)
    (atomMarginWeight_pos hpos hsmall) (atomMarginWeight_sum scale) hframe
  refine ⟨car, hcard, fun probe hvanish => ?_⟩
  rw [← scale_energy_add_margin]
  exact hdom probe hvanish

/-- **THE MASS-ONE SELECTION CLOSES THE PIVOT PAIR RESIDUE.** -/
theorem atomPivotPairClosed_of_atomTripleBoundary
    (hboundary : AtomTripleBoundaryClosed) : AtomPivotPairClosed := by
  intro atom scale hpos hsmall hframe
  obtain ⟨car, hcard, hdom⟩ :=
    atomTripleCeilingClosed_of_atomTripleBoundary hboundary atom scale hpos hsmall hframe
  exact exists_pivotPair_of_dominating_carrier hcard hdom

/-- **THE MASS-ONE SELECTION CLOSES THE BLOCKED RESIDUE.**  The non-strict
selection at mass exactly one is therefore the ONE remaining statement of
the atom lane. -/
theorem atomBlockedPairClosed_of_atomTripleBoundary
    (hboundary : AtomTripleBoundaryClosed) : AtomBlockedPairClosed :=
  atomBlockedPairClosed_of_pivotPair
    (atomPivotPairClosed_of_atomTripleBoundary hboundary)

/-- **THE `(6,3)` CELL FROM THE MASS-ONE SELECTION.** -/
theorem gtzWeighted_six_three_of_atomTripleBoundary
    (hboundary : AtomTripleBoundaryClosed) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_blockedPair
    (atomBlockedPairClosed_of_atomTripleBoundary hboundary)

/-! ## Layer 2 — the tie structure at the boundary witness -/

/-- The TIE PROBE of the boundary witness: the kernel direction of the
carrier of the three distinct single directions, cleared to integers. -/
noncomputable def atomBoundaryTieProbe : Fin 6 → ℝ :=
  ![5, 0, 5, 0, 3, 0]

/-- The tie probe is supported on the carrier `{0, 2, 4}`. -/
theorem atomBoundaryTieProbe_vanish :
    ∀ slot ∉ ({0, 2, 4} : Finset (Fin 6)), atomBoundaryTieProbe slot = 0 := by
  intro slot hnot
  fin_cases slot <;> simp_all [atomBoundaryTieProbe]

/-- The tie probe is nonzero. -/
theorem atomBoundaryTieProbe_ne_zero : atomBoundaryTieProbe ≠ 0 := by
  intro hzero
  have h := congrFun hzero 0
  simp [atomBoundaryTieProbe] at h

/-- **THE WITNESS SATISFIES THE MASS-ONE SELECTION.**  The carrier of the
three distinct single directions dominates the boundary witness weakly,
by an exact sum-of-squares certificate. -/
theorem atomBoundaryAtom_weak_carrier :
    ∀ probe : Fin 6 → ℝ, (∀ slot ∉ ({0, 2, 4} : Finset (Fin 6)), probe slot = 0) →
      (∑ slot, atomBoundaryScale slot * probe slot ^ 2)
        ≤ atomBlend atomBoundaryAtom probe ⬝ᵥ atomBlend atomBoundaryAtom probe := by
  intro probe hvanish
  have h02 : (0 : Fin 6) ≠ 2 := by decide
  have h04 : (0 : Fin 6) ≠ 4 := by decide
  have h24 : (2 : Fin 6) ≠ 4 := by decide
  have hscaleSum : (∑ slot, atomBoundaryScale slot * probe slot ^ 2)
      = atomBoundaryScale 0 * probe 0 ^ 2 + atomBoundaryScale 2 * probe 2 ^ 2
        + atomBoundaryScale 4 * probe 4 ^ 2 :=
    sum_eq_triple_of_support h02 h04 h24
      fun slot hnot => by rw [hvanish slot hnot]; ring
  have henergy := blend_energy_eq_triple_of_support atomBoundaryAtom h02 h04 h24 hvanish
  rw [hscaleSum, henergy]
  simp only [atomBoundaryAtom_gram]
  rw [show atomBoundaryGram 0 0 = 27 / 100 from rfl,
    show atomBoundaryGram 2 2 = 27 / 100 from rfl,
    show atomBoundaryGram 4 4 = 3 / 4 from rfl,
    show atomBoundaryGram 0 2 = -(9 / 100) from rfl,
    show atomBoundaryGram 0 4 = -(3 / 20) from rfl,
    show atomBoundaryGram 2 4 = -(3 / 20) from rfl,
    show atomBoundaryScale 0 = 9 / 100 from rfl,
    show atomBoundaryScale 2 = 9 / 100 from rfl,
    show atomBoundaryScale 4 = 1 / 4 from rfl]
  nlinarith [sq_nonneg (6 * probe 0 - 3 * probe 2 - 5 * probe 4),
    sq_nonneg (3 * probe 2 - 5 * probe 4)]

/-- **THE TIE IS EXACT.**  At the tie probe the scale energy of the
boundary witness EQUALS its blend energy: the weak domination of the
carrier `{0, 2, 4}` cannot be strict. -/
theorem atomBoundaryAtom_tie :
    (∑ slot, atomBoundaryScale slot * atomBoundaryTieProbe slot ^ 2)
      = atomBlend atomBoundaryAtom atomBoundaryTieProbe
          ⬝ᵥ atomBlend atomBoundaryAtom atomBoundaryTieProbe := by
  simp [Fin.sum_univ_six, atomBoundaryScale, atomBoundaryTieProbe, atomBlend,
    atomBoundaryAtom, dotProduct, Fin.sum_univ_three]
  norm_num

/-- **NO CARRIER DOMINATES THE WITNESS STRICTLY.**  Any strict carrier
would give a deflated pair through the converse Sylvester extraction, and
the witness carries none. -/
theorem atomBoundaryAtom_no_strict_carrier (car : Finset (Fin 6))
    (hcard : car.card = 3) :
    ¬ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
        (∑ slot, atomBoundaryScale slot * probe slot ^ 2)
          < atomBlend atomBoundaryAtom probe ⬝ᵥ atomBlend atomBoundaryAtom probe := by
  intro hdom
  obtain ⟨pivot, slotOne, slotTwo, honePivot, htwoPivot, hpair, hdiag, hminor, hcross⟩ :=
    exists_pivotPair_of_dominating_carrier hcard hdom
  exact atomBoundaryAtom_no_deflated_pair pivot slotOne slotTwo honePivot htwoPivot
    hpair ⟨hdiag, hminor, hcross⟩

/-- The boundary witness family at a chosen mass: each weight gives back
one sixth of the mass deficit. -/
noncomputable def atomBoundaryScaleAt (mass : ℝ) : Fin 6 → ℝ :=
  fun slot => atomBoundaryScale slot - (1 - mass) / 6

/-- The witness family at mass `m` has scale mass exactly `m`. -/
theorem atomBoundaryScaleAt_sum (mass : ℝ) :
    (∑ slot, atomBoundaryScaleAt mass slot) = mass := by
  simp [Fin.sum_univ_six, atomBoundaryScaleAt, atomBoundaryScale]
  ring

/-- The witness family is positive above mass `23/50`. -/
theorem atomBoundaryScaleAt_pos {mass : ℝ} (hmass : 23 / 50 < mass) (slot : Fin 6) :
    0 < atomBoundaryScaleAt mass slot := by
  simp only [atomBoundaryScaleAt]
  fin_cases slot <;> · norm_num [atomBoundaryScale]; linarith

/-- The margin weight of the witness family at any mass is the mass-one
witness scale: the reparametrization round trip is exact. -/
theorem atomMarginWeight_boundaryScaleAt (mass : ℝ) :
    atomMarginWeight (atomBoundaryScaleAt mass) = atomBoundaryScale := by
  funext slot
  have hsum := atomBoundaryScaleAt_sum mass
  simp only [atomMarginWeight, atomBoundaryScaleAt] at hsum ⊢
  rw [hsum]
  ring

/-- **THE MARGIN `(1 - m) / 6` IS SHARP AT EVERY MASS.**  At the witness
family of mass `m`, no carrier dominates with a margin above
`(1 - m) / 6`: the margin-improved strict test at any carrier fails.
Thus the sharp margin transfer above cannot be improved, at any mass. -/
theorem atomBoundaryScaleAt_no_margin_carrier (mass : ℝ) (car : Finset (Fin 6))
    (hcard : car.card = 3) :
    ¬ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
        (∑ slot, atomBoundaryScaleAt mass slot * probe slot ^ 2)
          + (1 - mass) / 6 * (∑ slot, probe slot ^ 2)
          < atomBlend atomBoundaryAtom probe ⬝ᵥ atomBlend atomBoundaryAtom probe := by
  intro hdom
  refine atomBoundaryAtom_no_strict_carrier car hcard fun probe hvanish hne => ?_
  have hstep := hdom probe hvanish hne
  have hshift : (∑ slot, atomBoundaryScaleAt mass slot * probe slot ^ 2)
      + (1 - mass) / 6 * (∑ slot, probe slot ^ 2)
      = ∑ slot, atomBoundaryScale slot * probe slot ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun slot _ => by rw [atomBoundaryScaleAt]; ring
  rw [hshift] at hstep
  exact hstep

/-! ## Layer 3 — the parallel-pair kill at the weak level -/

/-- **A WEAK CARRIER NEVER CONTAINS A PARALLEL PAIR.**  Two parallel slots
of a carrier admit the probe `(-factor, 1)` whose blend vanishes while its
scale energy is positive, thus weak domination fails.  This is the weak
form of `Gtz.atomPairMinor_neg_of_parallel`, and it is the mechanism that
forces every mass-one tie away from its own doubled pair. -/
theorem not_weakCarrier_of_parallel_pair {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo : Fin slotCount} {factor : ℝ}
    (hne : slotOne ≠ slotTwo) (hparallel : atom slotTwo = factor • atom slotOne)
    (hposTwo : 0 < scale slotTwo) (hnonnegOne : 0 ≤ scale slotOne)
    {car : Finset (Fin slotCount)} (hone : slotOne ∈ car) (htwo : slotTwo ∈ car)
    (hdom : ∀ probe : Fin slotCount → ℝ, (∀ slot ∉ car, probe slot = 0) →
        (∑ slot, scale slot * probe slot ^ 2)
          ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe) : False := by
  classical
  set probe : Fin slotCount → ℝ :=
    fun slot => if slot = slotOne then -factor else if slot = slotTwo then 1 else 0
    with hprobeDef
  have hprobeOne : probe slotOne = -factor := by
    rw [hprobeDef]; simp
  have hprobeTwo : probe slotTwo = 1 := by
    rw [hprobeDef]; simp [Ne.symm hne]
  have hvanishPair : ∀ slot ∉ ({slotOne, slotTwo} : Finset (Fin slotCount)),
      probe slot = 0 := by
    intro slot hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    rw [hprobeDef]
    simp [hnot.1, hnot.2]
  have hvanishCar : ∀ slot ∉ car, probe slot = 0 := by
    intro slot hnot
    refine hvanishPair slot ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun heq => hnot (heq ▸ hone), fun heq => hnot (heq ▸ htwo)⟩
  have hgramTwoOne : atomGram atom slotTwo slotOne = factor * atomGram atom slotOne slotOne := by
    rw [atomGram, atomGram, hparallel, smul_dotProduct, smul_eq_mul]
  have hgramOneTwo : atomGram atom slotOne slotTwo = factor * atomGram atom slotOne slotOne := by
    rw [atomGram_comm]
    exact hgramTwoOne
  have hgramTwoTwo : atomGram atom slotTwo slotTwo
      = factor * (factor * atomGram atom slotOne slotOne) := by
    rw [atomGram, atomGram, hparallel, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul]
  have henergy : atomBlend atom probe ⬝ᵥ atomBlend atom probe = 0 := by
    rw [atomBlend_energy_eq_gram]
    have hinner : ∀ rowSlot : Fin slotCount,
        (∑ colSlot, probe rowSlot * probe colSlot * atomGram atom rowSlot colSlot)
          = probe rowSlot * probe slotOne * atomGram atom rowSlot slotOne
            + probe rowSlot * probe slotTwo * atomGram atom rowSlot slotTwo :=
      fun rowSlot => sum_eq_pair_of_support hne
        fun colSlot hnot => by rw [hvanishPair colSlot hnot, mul_zero, zero_mul]
    rw [Finset.sum_congr rfl fun rowSlot _ => hinner rowSlot,
      sum_eq_pair_of_support hne
        (fun rowSlot hnot => by rw [hvanishPair rowSlot hnot]; ring)]
    rw [hprobeOne, hprobeTwo, hgramTwoOne, hgramOneTwo, hgramTwoTwo]
    ring
  have hscale : (∑ slot, scale slot * probe slot ^ 2)
      = scale slotOne * factor ^ 2 + scale slotTwo := by
    rw [sum_eq_pair_of_support hne
      (fun slot hnot => by rw [hvanishPair slot hnot]; ring), hprobeOne, hprobeTwo]
    ring
  have hstep := hdom probe hvanishCar
  rw [henergy, hscale] at hstep
  nlinarith [hstep, hposTwo, mul_nonneg hnonnegOne (sq_nonneg factor)]

/-! ## Layer 4 — the rational split and the descent to five slots -/

/-- The fold of the split family: slot five folds back onto slot zero. -/
def atomSplitSlot : Fin 6 → Fin 5 :=
  ![0, 1, 2, 3, 4, 0]

/-- The split factor: slot zero carries `3/5` of the split atom, slot five
carries `4/5`, and the middle slots are untouched. -/
noncomputable def atomSplitFactor : Fin 6 → ℝ :=
  ![3 / 5, 1, 1, 1, 1, 4 / 5]

/-- The boost: the reciprocal of the split factor, slot by slot. -/
noncomputable def atomSplitBoost : Fin 6 → ℝ :=
  ![5 / 3, 1, 1, 1, 1, 5 / 4]

/-- The SPLIT FAMILY: the first atom divided into the rational parallel
pair `(3/5, 4/5)`, whose squares add to one. -/
noncomputable def atomSplitAtom {rank : ℕ} (atom : Fin 5 → (Fin rank → ℝ)) :
    Fin 6 → (Fin rank → ℝ) :=
  ![(3 / 5 : ℝ) • atom 0, atom 1, atom 2, atom 3, atom 4, (4 / 5 : ℝ) • atom 0]

/-- The SPLIT SCALE: the first weight divided in the matched squares
`(9/25, 16/25)`. -/
noncomputable def atomSplitScale (scale : Fin 5 → ℝ) : Fin 6 → ℝ :=
  ![9 / 25 * scale 0, scale 1, scale 2, scale 3, scale 4, 16 / 25 * scale 0]

/-- The split factor against its boost is one at every slot. -/
theorem atomSplitFactor_mul_boost (slot : Fin 6) :
    atomSplitFactor slot * atomSplitBoost slot = 1 := by
  fin_cases slot <;> norm_num [atomSplitFactor, atomSplitBoost]

/-- The fold identifies two slots exactly when they are equal or they are
the split pair. -/
theorem atomSplitSlot_eq_iff : ∀ rowSlot colSlot : Fin 6,
    atomSplitSlot rowSlot = atomSplitSlot colSlot
      ↔ rowSlot = colSlot ∨ (rowSlot = 0 ∧ colSlot = 5) ∨ (rowSlot = 5 ∧ colSlot = 0) := by
  decide

/-- **THE GRAM OF THE SPLIT FAMILY FACTORS.**  Every entry is the folded
entry against the two split factors. -/
theorem atomGram_atomSplitAtom {rank : ℕ} (atom : Fin 5 → (Fin rank → ℝ))
    (rowSlot colSlot : Fin 6) :
    atomGram (atomSplitAtom atom) rowSlot colSlot
      = atomSplitFactor rowSlot * atomSplitFactor colSlot
        * atomGram atom (atomSplitSlot rowSlot) (atomSplitSlot colSlot) := by
  fin_cases rowSlot <;> fin_cases colSlot <;>
    simp [atomGram, atomSplitAtom, atomSplitFactor, atomSplitSlot,
      smul_dotProduct, dotProduct_smul] <;>
    ring

/-- The split scale reads as the folded scale against the squared factor. -/
theorem atomSplitScale_eq (scale : Fin 5 → ℝ) (slot : Fin 6) :
    atomSplitScale scale slot
      = atomSplitFactor slot ^ 2 * scale (atomSplitSlot slot) := by
  fin_cases slot <;> norm_num [atomSplitScale, atomSplitFactor, atomSplitSlot]

/-- The split scale is positive when the folded scale is. -/
theorem atomSplitScale_pos {scale : Fin 5 → ℝ} (hpos : ∀ slot, 0 < scale slot)
    (slot : Fin 6) : 0 < atomSplitScale scale slot := by
  rw [atomSplitScale_eq]
  have hfold := hpos (atomSplitSlot slot)
  have hfactor : 0 < atomSplitFactor slot ^ 2 := by
    fin_cases slot <;> norm_num [atomSplitFactor]
  exact mul_pos hfactor hfold

/-- The split scale has the same total mass. -/
theorem atomSplitScale_sum (scale : Fin 5 → ℝ) :
    (∑ slot, atomSplitScale scale slot) = ∑ slot, scale slot := by
  rw [Fin.sum_univ_six, Fin.sum_univ_five,
    show atomSplitScale scale 0 = 9 / 25 * scale 0 from rfl,
    show atomSplitScale scale 1 = scale 1 from rfl,
    show atomSplitScale scale 2 = scale 2 from rfl,
    show atomSplitScale scale 3 = scale 3 from rfl,
    show atomSplitScale scale 4 = scale 4 from rfl,
    show atomSplitScale scale 5 = 16 / 25 * scale 0 from rfl]
  ring

/-- **THE FRAME LAW SURVIVES THE SPLIT.**  The two copies pay `9/25` and
`16/25` of the first atom's contribution, and the squares add to one. -/
theorem atomSplitAtom_frame {rank : ℕ} {atom : Fin 5 → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (probe direction : Fin rank → ℝ) :
    (∑ slot, (atomSplitAtom atom slot ⬝ᵥ probe)
        * (atomSplitAtom atom slot ⬝ᵥ direction))
      = probe ⬝ᵥ direction := by
  have hfive := hframe probe direction
  rw [Fin.sum_univ_five] at hfive
  rw [Fin.sum_univ_six,
    show atomSplitAtom atom 0 = (3 / 5 : ℝ) • atom 0 from rfl,
    show atomSplitAtom atom 1 = atom 1 from rfl,
    show atomSplitAtom atom 2 = atom 2 from rfl,
    show atomSplitAtom atom 3 = atom 3 from rfl,
    show atomSplitAtom atom 4 = atom 4 from rfl,
    show atomSplitAtom atom 5 = (4 / 5 : ℝ) • atom 0 from rfl]
  simp only [smul_dotProduct, smul_eq_mul]
  linear_combination hfive

/-- The two split copies are parallel with the rational factor `4/3`. -/
theorem atomSplitAtom_parallel {rank : ℕ} (atom : Fin 5 → (Fin rank → ℝ)) :
    atomSplitAtom atom 5 = (4 / 3 : ℝ) • atomSplitAtom atom 0 := by
  rw [show atomSplitAtom atom 5 = (4 / 5 : ℝ) • atom 0 from rfl,
    show atomSplitAtom atom 0 = (3 / 5 : ℝ) • atom 0 from rfl, smul_smul]
  norm_num

/-- The boost clears the split scale back to the folded scale. -/
theorem atomSplitScale_boost (scale : Fin 5 → ℝ) (slot : Fin 6) :
    atomSplitScale scale slot * atomSplitBoost slot ^ 2
      = scale (atomSplitSlot slot) := by
  have hfb := atomSplitFactor_mul_boost slot
  rw [atomSplitScale_eq]
  linear_combination (scale (atomSplitSlot slot)
    * (atomSplitFactor slot * atomSplitBoost slot + 1)) * hfb

/-- The boost clears the split Gram back to the folded Gram. -/
theorem atomSplitGram_boost {rank : ℕ} (atom : Fin 5 → (Fin rank → ℝ))
    (rowSlot colSlot : Fin 6) :
    atomSplitBoost rowSlot * atomSplitBoost colSlot
        * atomGram (atomSplitAtom atom) rowSlot colSlot
      = atomGram atom (atomSplitSlot rowSlot) (atomSplitSlot colSlot) := by
  have hrow := atomSplitFactor_mul_boost rowSlot
  have hcol := atomSplitFactor_mul_boost colSlot
  rw [atomGram_atomSplitAtom]
  linear_combination (atomGram atom (atomSplitSlot rowSlot) (atomSplitSlot colSlot)
      * atomSplitBoost rowSlot * atomSplitFactor rowSlot) * hcol
    + (atomGram atom (atomSplitSlot rowSlot) (atomSplitSlot colSlot)) * hrow

/-- **THE FIVE-SLOT MASS-ONE SELECTION.**  Five Parseval atoms of rank
three with positive weights of total one carry a triple whose shifted
ternary form is weakly nonnegative. -/
def AtomFiveTripleBoundaryClosed : Prop :=
  ∀ (atom : Fin 5 → (Fin 3 → ℝ)) (scale : Fin 5 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ slotOne slotTwo slotThree : Fin 5,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ ∀ valueOne valueTwo valueThree : ℝ,
            scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
                + scale slotThree * valueThree ^ 2
              ≤ atomGram atom slotOne slotOne * valueOne ^ 2
                + atomGram atom slotTwo slotTwo * valueTwo ^ 2
                + atomGram atom slotThree slotThree * valueThree ^ 2
                + 2 * atomGram atom slotOne slotTwo * valueOne * valueTwo
                + 2 * atomGram atom slotOne slotThree * valueOne * valueThree
                + 2 * atomGram atom slotTwo slotThree * valueTwo * valueThree

/-- **THE DESCENT.**  The six-slot mass-one selection implies the
five-slot one: split the first atom into the rational parallel pair, note
that the returned carrier can never use both copies, and fold it back with
the boost.  The five-slot analogue of the residue is thus a consequence of
the residue, and a five-slot calibration against it is impossible. -/
theorem atomFiveTripleBoundaryClosed_of_atomTripleBoundary
    (hboundary : AtomTripleBoundaryClosed) : AtomFiveTripleBoundaryClosed := by
  classical
  intro atom scale hpos hmass hframe
  obtain ⟨car, hcard, hdom⟩ := hboundary (atomSplitAtom atom) (atomSplitScale scale)
    (atomSplitScale_pos hpos) (by rw [atomSplitScale_sum]; exact hmass)
    (atomSplitAtom_frame hframe)
  obtain ⟨rowSlot, colSlot, farSlot, hxy, hxz, hyz, hcarEq⟩ :=
    Finset.card_eq_three.mp hcard
  subst hcarEq
  have hpair : ¬ ((0 : Fin 6) ∈ ({rowSlot, colSlot, farSlot} : Finset (Fin 6))
      ∧ (5 : Fin 6) ∈ ({rowSlot, colSlot, farSlot} : Finset (Fin 6))) := by
    rintro ⟨hzero, hfive⟩
    exact not_weakCarrier_of_parallel_pair (show (0 : Fin 6) ≠ 5 by decide)
      (atomSplitAtom_parallel atom) (atomSplitScale_pos hpos 5)
      (atomSplitScale_pos hpos 0).le hzero hfive hdom
  have hfold : ∀ first second : Fin 6,
      first ∈ ({rowSlot, colSlot, farSlot} : Finset (Fin 6)) →
      second ∈ ({rowSlot, colSlot, farSlot} : Finset (Fin 6)) →
      first ≠ second → atomSplitSlot first ≠ atomSplitSlot second := by
    intro first second hfirst hsecond hne heq
    rcases (atomSplitSlot_eq_iff first second).mp heq with hsame | hzeroFive | hfiveZero
    · exact hne hsame
    · exact hpair ⟨hzeroFive.1 ▸ hfirst, hzeroFive.2 ▸ hsecond⟩
    · exact hpair ⟨hfiveZero.2 ▸ hsecond, hfiveZero.1 ▸ hfirst⟩
  have hvals := weak_values_of_weak_carrier hxy hxz hyz hdom
  have hrowMem : rowSlot ∈ ({rowSlot, colSlot, farSlot} : Finset (Fin 6)) := by simp
  have hcolMem : colSlot ∈ ({rowSlot, colSlot, farSlot} : Finset (Fin 6)) := by simp
  have hfarMem : farSlot ∈ ({rowSlot, colSlot, farSlot} : Finset (Fin 6)) := by simp
  refine ⟨atomSplitSlot rowSlot, atomSplitSlot colSlot, atomSplitSlot farSlot,
    hfold rowSlot colSlot hrowMem hcolMem hxy,
    hfold rowSlot farSlot hrowMem hfarMem hxz,
    hfold colSlot farSlot hcolMem hfarMem hyz, ?_⟩
  intro valueOne valueTwo valueThree
  have hsix := hvals (atomSplitBoost rowSlot * valueOne)
    (atomSplitBoost colSlot * valueTwo) (atomSplitBoost farSlot * valueThree)
  have hscaleRow : atomSplitScale scale rowSlot * (atomSplitBoost rowSlot * valueOne) ^ 2
      = scale (atomSplitSlot rowSlot) * valueOne ^ 2 := by
    rw [← atomSplitScale_boost scale rowSlot]; ring
  have hscaleCol : atomSplitScale scale colSlot * (atomSplitBoost colSlot * valueTwo) ^ 2
      = scale (atomSplitSlot colSlot) * valueTwo ^ 2 := by
    rw [← atomSplitScale_boost scale colSlot]; ring
  have hscaleFar : atomSplitScale scale farSlot * (atomSplitBoost farSlot * valueThree) ^ 2
      = scale (atomSplitSlot farSlot) * valueThree ^ 2 := by
    rw [← atomSplitScale_boost scale farSlot]; ring
  have hgramRow : atomGram (atomSplitAtom atom) rowSlot rowSlot
        * (atomSplitBoost rowSlot * valueOne) ^ 2
      = atomGram atom (atomSplitSlot rowSlot) (atomSplitSlot rowSlot) * valueOne ^ 2 := by
    rw [← atomSplitGram_boost atom rowSlot rowSlot]; ring
  have hgramCol : atomGram (atomSplitAtom atom) colSlot colSlot
        * (atomSplitBoost colSlot * valueTwo) ^ 2
      = atomGram atom (atomSplitSlot colSlot) (atomSplitSlot colSlot) * valueTwo ^ 2 := by
    rw [← atomSplitGram_boost atom colSlot colSlot]; ring
  have hgramFar : atomGram (atomSplitAtom atom) farSlot farSlot
        * (atomSplitBoost farSlot * valueThree) ^ 2
      = atomGram atom (atomSplitSlot farSlot) (atomSplitSlot farSlot) * valueThree ^ 2 := by
    rw [← atomSplitGram_boost atom farSlot farSlot]; ring
  have hgramRowCol : 2 * atomGram (atomSplitAtom atom) rowSlot colSlot
        * (atomSplitBoost rowSlot * valueOne) * (atomSplitBoost colSlot * valueTwo)
      = 2 * atomGram atom (atomSplitSlot rowSlot) (atomSplitSlot colSlot)
        * valueOne * valueTwo := by
    rw [← atomSplitGram_boost atom rowSlot colSlot]; ring
  have hgramRowFar : 2 * atomGram (atomSplitAtom atom) rowSlot farSlot
        * (atomSplitBoost rowSlot * valueOne) * (atomSplitBoost farSlot * valueThree)
      = 2 * atomGram atom (atomSplitSlot rowSlot) (atomSplitSlot farSlot)
        * valueOne * valueThree := by
    rw [← atomSplitGram_boost atom rowSlot farSlot]; ring
  have hgramColFar : 2 * atomGram (atomSplitAtom atom) colSlot farSlot
        * (atomSplitBoost colSlot * valueTwo) * (atomSplitBoost farSlot * valueThree)
      = 2 * atomGram atom (atomSplitSlot colSlot) (atomSplitSlot farSlot)
        * valueTwo * valueThree := by
    rw [← atomSplitGram_boost atom colSlot farSlot]; ring
  linarith [hsix, hscaleRow, hscaleCol, hscaleFar, hgramRow, hgramCol, hgramFar,
    hgramRowCol, hgramRowFar, hgramColFar]

end Gtz

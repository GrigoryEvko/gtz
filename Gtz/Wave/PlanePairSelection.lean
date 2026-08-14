import Gtz.Wave.PlaneCapTripleClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The plane pair selection theorem, and its quantitative margin

A PLANE FRAME is a finite family of vectors of the plane whose outer products
total the identity.  A SCALE is a positive number at every slot.  This module
proves that a plane frame of scale total less than one always carries a PAIR of
slots whose scaled outer products dominate the identity, and it prices the
domination by the scale slack.

The proof has three steps and no search.

The MASS LAW is the trace of the frame law.  The masses total two, not one.
The mass-to-scale ratio two is the whole strength of the theorem, and a scale
total of one is exactly the boundary.

The WRAP LAW is the traceless part of the frame law.  The doubled reading of a
plane vector squares its two coordinates, and the doubled readings of a plane
frame TOTAL ZERO.  The pair test is quadratic in the atoms, and the doubled
reading makes it LINEAR in the doubled plane.  Thus the failure of every pair
becomes a family of half planes of the disc, the landed cap residue supplies a
common point of that family, and the wrap law reads the common point against
the mass law.  The reading gives a scale total of at least one, which the
hypothesis refuses.

The PAIR TEST is a two-by-two determinant.  A pair dominates the identity when
the trace of the shifted pair matrix is nonnegative and its determinant is
nonnegative.  Both readings are division free, and the module proves the two
directions, so the pair test is an EQUIVALENCE.

## The sharpness, and the field

The theorem is SHARP.  The trine of `Gtz.planeTrineAtom` (three lines at sixty
degrees, mass two-thirds, scale one-third) has scale total exactly one, every
pair sits at the certificate boundary, and `Gtz.planeTrine_not_dominates` shows
that NO pair dominates at any inflated scale.  Thus the margin of the selection
theorem cannot be positive at scale total one.

The theorem is REAL.  Its Hermitian analogue is FALSE at four atoms: the Bloch
tetrahedron of two-dimensional complex space (four unit vectors of pairwise
squared overlap one third, mass one half, scale one quarter, scale total one)
gives every pair the least eigenvalue `2 - 2/sqrt 3`, which misses one by
`0.1547`.  The reason is a dimension count.  The doubled readings of the real
plane fill a plane, where the cap residue asks for three atoms, and the doubled
readings of the complex plane fill a three-space, where it asks for four.  Four
atoms are exactly the first count at which the two fields separate.  This
paragraph reports a measurement, not a theorem of this module.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.planeDouble`, `Gtz.planeDouble_dot`, `Gtz.planeDouble_dot_self` — **THE
  DOUBLED READING OF THE PLANE.**  The doubled dot of two plane vectors is twice
  the squared dot minus the product of the two masses.
* `Gtz.PlaneParseval`, `Gtz.planeParseval_of_entries`,
  `Gtz.PlaneParseval.sum_first_sq`, `Gtz.PlaneParseval.sum_second_sq`,
  `Gtz.PlaneParseval.sum_cross` — the frame law and its three entry laws, in
  both directions.
* `Gtz.PlaneParseval.sum_mass` — **THE MASS LAW.**  The masses total two.
* `Gtz.PlaneParseval.sum_dot_planeDouble` — **THE WRAP LAW.**  Every reading of
  the doubled atoms totals zero.
* `Gtz.PlaneParseval.rowEnergy`, `Gtz.PlaneParseval.mass_le_one` — the row
  energy law of a slot, and the mass cap that follows from it.
* `Gtz.PlaneParseval.exists_heavy_slot` — **THE MASS PIGEONHOLE.**  Under a
  scale total of at most one, some slot carries twice its scale in mass.
* `Gtz.PlanePairDominates`, `Gtz.PlanePairDominates.symm`,
  `Gtz.PlanePairDominates.le_div` — the pair test, its symmetry, and its
  division form.
* `Gtz.planeForm_nonneg` — the scalar core: a binary quadratic form of
  nonnegative trace and nonnegative discriminant is nonnegative.
* `Gtz.planePairDominates_of_certificate` — **THE PAIR CERTIFICATE.**  Trace and
  determinant give the domination, with no eigenvalue and no square root.
* `Gtz.planePair_trace_of_dominates`, `Gtz.planePair_certificate_of_dominates`,
  `Gtz.planePairDominates_iff` — the converse, and the equivalence.
* `Gtz.exists_dominatingPlanePair` — **THE SELECTION THEOREM.**  Every plane
  frame of at least three slots, with positive scales of total less than one,
  carries a dominating pair.
* `Gtz.exists_dominatingPlanePair_margin` — **THE QUANTITATIVE MARGIN.**  The
  domination holds with the factor `1 + (1 - total)/2`.
* `Gtz.exists_dominatingPlanePair_four`,
  `Gtz.exists_dominatingPlanePair_five` — the two counts the campaign consumes.
* `Gtz.planeTrineAtom`, `Gtz.planeTrineAtom_parseval`,
  `Gtz.planeTrineAtom_mass`, `Gtz.planeTrineAtom_dot`,
  `Gtz.planeTrine_not_dominates` — **THE SHARPNESS CALIBRATION.**
-/

namespace Gtz

open scoped BigOperators Matrix

/-! ## Layer 1 — the doubled reading of the plane -/

/-- **THE DOUBLED READING OF A PLANE VECTOR.**  The first entry is the
difference of the two squared coordinates, the second entry is twice their
product.  The reading doubles the angle and squares the length. -/
def planeDouble (vec : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![vec 0 ^ 2 - vec 1 ^ 2, 2 * (vec 0 * vec 1)]

theorem planeDouble_zero (vec : Fin 2 → ℝ) :
    planeDouble vec 0 = vec 0 ^ 2 - vec 1 ^ 2 := rfl

theorem planeDouble_one (vec : Fin 2 → ℝ) :
    planeDouble vec 1 = 2 * (vec 0 * vec 1) := rfl

/-- The dot product of a plane vector with itself is nonnegative. -/
theorem plane_dot_self_nonneg (vec : Fin 2 → ℝ) : 0 ≤ vec ⬝ᵥ vec := by
  rw [dot_fin_two]
  have hfirst := mul_self_nonneg (vec 0)
  have hsecond := mul_self_nonneg (vec 1)
  linarith

/-- The reading of a plane vector against the first unit vector. -/
theorem dot_firstUnit (vec : Fin 2 → ℝ) : vec ⬝ᵥ ![1, 0] = vec 0 := by
  rw [dot_fin_two]
  norm_num

/-- The reading of a plane vector against the second unit vector. -/
theorem dot_secondUnit (vec : Fin 2 → ℝ) : vec ⬝ᵥ ![0, 1] = vec 1 := by
  rw [dot_fin_two]
  norm_num

/-- **THE DOUBLED DOT LAW.**  The doubled readings of two plane vectors read
twice the squared dot of the vectors, minus the product of the two masses. -/
theorem planeDouble_dot (vecOne vecTwo : Fin 2 → ℝ) :
    planeDouble vecOne ⬝ᵥ planeDouble vecTwo
      = 2 * (vecOne ⬝ᵥ vecTwo) ^ 2 - (vecOne ⬝ᵥ vecOne) * (vecTwo ⬝ᵥ vecTwo) := by
  simp only [dot_fin_two, planeDouble_zero, planeDouble_one]
  ring

/-- **THE DOUBLED ENERGY LAW.**  A doubled reading carries the square of the
mass of its atom. -/
theorem planeDouble_dot_self (vec : Fin 2 → ℝ) :
    planeDouble vec ⬝ᵥ planeDouble vec = (vec ⬝ᵥ vec) ^ 2 := by
  rw [planeDouble_dot]
  ring

/-- A reading of a doubled atom, written on the two entry laws. -/
theorem dot_planeDouble (point vec : Fin 2 → ℝ) :
    point ⬝ᵥ planeDouble vec
      = point 0 * (vec 0 * vec 0) + (-point 0) * (vec 1 * vec 1)
        + 2 * point 1 * (vec 0 * vec 1) := by
  simp only [dot_fin_two, planeDouble_zero, planeDouble_one]
  ring

/-! ## Layer 2 — the plane frame law -/

/-- **THE PLANE FRAME LAW.**  The outer products of the atoms total the identity
of the plane, written as a bilinear reading. -/
def PlaneParseval {slotCount : ℕ} (atom : Fin slotCount → (Fin 2 → ℝ)) : Prop :=
  ∀ probe other : Fin 2 → ℝ,
    (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other

/-- The first entry law of a plane frame. -/
theorem PlaneParseval.sum_first_sq {slotCount : ℕ} {atom : Fin slotCount → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom) : (∑ slot, atom slot 0 * atom slot 0) = 1 := by
  have hunit : ((![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![1, 0]) = 1 := by
    rw [dot_fin_two]; norm_num
  have hread := hframe ![1, 0] ![1, 0]
  rw [hunit] at hread
  simp only [dot_firstUnit] at hread
  exact hread

/-- The second entry law of a plane frame. -/
theorem PlaneParseval.sum_second_sq {slotCount : ℕ} {atom : Fin slotCount → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom) : (∑ slot, atom slot 1 * atom slot 1) = 1 := by
  have hunit : ((![0, 1] : Fin 2 → ℝ) ⬝ᵥ ![0, 1]) = 1 := by
    rw [dot_fin_two]; norm_num
  have hread := hframe ![0, 1] ![0, 1]
  rw [hunit] at hread
  simp only [dot_secondUnit] at hread
  exact hread

/-- The cross entry law of a plane frame. -/
theorem PlaneParseval.sum_cross {slotCount : ℕ} {atom : Fin slotCount → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom) : (∑ slot, atom slot 0 * atom slot 1) = 0 := by
  have hunit : ((![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![0, 1]) = 0 := by
    rw [dot_fin_two]; norm_num
  have hread := hframe ![1, 0] ![0, 1]
  rw [hunit] at hread
  simp only [dot_firstUnit, dot_secondUnit] at hread
  exact hread

/-- **THE FRAME LAW FROM THE THREE ENTRY LAWS.**  A consumer supplies three
scalar sums and gets the bilinear form. -/
theorem planeParseval_of_entries {slotCount : ℕ} {atom : Fin slotCount → (Fin 2 → ℝ)}
    (hfirst : (∑ slot, atom slot 0 * atom slot 0) = 1)
    (hsecond : (∑ slot, atom slot 1 * atom slot 1) = 1)
    (hcross : (∑ slot, atom slot 0 * atom slot 1) = 0) : PlaneParseval atom := by
  intro probe other
  have hexpand : ∀ slot : Fin slotCount, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)
      = (probe 0 * other 0) * (atom slot 0 * atom slot 0)
        + (probe 1 * other 1) * (atom slot 1 * atom slot 1)
        + (probe 0 * other 1 + probe 1 * other 0) * (atom slot 0 * atom slot 1) := by
    intro slot
    simp only [dot_fin_two]
    ring
  simp only [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, hfirst, hsecond, hcross, dot_fin_two]
  ring

/-- **THE MASS LAW.**  The masses of a plane frame total two, the trace of the
identity of the plane.  The mass total is NOT one. -/
theorem PlaneParseval.sum_mass {slotCount : ℕ} {atom : Fin slotCount → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom) : (∑ slot, atom slot ⬝ᵥ atom slot) = 2 := by
  have hexpand : ∀ slot : Fin slotCount, atom slot ⬝ᵥ atom slot
      = atom slot 0 * atom slot 0 + atom slot 1 * atom slot 1 := by
    intro slot
    rw [dot_fin_two]
  simp only [hexpand]
  rw [Finset.sum_add_distrib, hframe.sum_first_sq, hframe.sum_second_sq]
  norm_num

/-- **THE WRAP LAW.**  Every reading of the doubled atoms of a plane frame
totals zero.  The doubled atoms of a frame WRAP around the origin. -/
theorem PlaneParseval.sum_dot_planeDouble {slotCount : ℕ} {atom : Fin slotCount → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom) (point : Fin 2 → ℝ) :
    (∑ slot, point ⬝ᵥ planeDouble (atom slot)) = 0 := by
  simp only [dot_planeDouble]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, hframe.sum_first_sq, hframe.sum_second_sq, hframe.sum_cross]
  ring

/-- **THE ROW ENERGY LAW.**  The squared dots of one atom against the whole
frame total the mass of that atom. -/
theorem PlaneParseval.rowEnergy {slotCount : ℕ} {atom : Fin slotCount → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom) (slot : Fin slotCount) :
    (∑ other, (atom other ⬝ᵥ atom slot) * (atom other ⬝ᵥ atom slot))
      = atom slot ⬝ᵥ atom slot :=
  hframe (atom slot) (atom slot)

/-- **THE MASS CAP.**  No atom of a plane frame carries more than one unit of
mass. -/
theorem PlaneParseval.mass_le_one {slotCount : ℕ} {atom : Fin slotCount → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom) (slot : Fin slotCount) :
    atom slot ⬝ᵥ atom slot ≤ 1 := by
  have hrow := hframe.rowEnergy slot
  have hterm : (atom slot ⬝ᵥ atom slot) * (atom slot ⬝ᵥ atom slot)
      ≤ ∑ other, (atom other ⬝ᵥ atom slot) * (atom other ⬝ᵥ atom slot) :=
    Finset.single_le_sum
      (f := fun other => (atom other ⬝ᵥ atom slot) * (atom other ⬝ᵥ atom slot))
      (fun other _ => mul_self_nonneg _) (Finset.mem_univ slot)
  rw [hrow] at hterm
  nlinarith [plane_dot_self_nonneg (atom slot)]

/-- **THE MASS PIGEONHOLE.**  Under a scale total of at most one, some slot of a
plane frame carries at least twice its scale in mass.  The mass law puts the
scale-weighted average of the mass-to-scale ratio at two. -/
theorem PlaneParseval.exists_heavy_slot {slotCount : ℕ} {atom : Fin slotCount → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom) (scale : Fin slotCount → ℝ) (hcount : 0 < slotCount)
    (hsmall : (∑ slot, scale slot) ≤ 1) :
    ∃ slot, 2 * scale slot ≤ atom slot ⬝ᵥ atom slot := by
  by_contra hnone
  simp only [not_exists, not_le] at hnone
  have hne : (Finset.univ : Finset (Fin slotCount)).Nonempty := by
    have : Nonempty (Fin slotCount) := Fin.pos_iff_nonempty.mp hcount
    exact Finset.univ_nonempty
  have hlt : (∑ slot, atom slot ⬝ᵥ atom slot) < ∑ slot, 2 * scale slot :=
    Finset.sum_lt_sum_of_nonempty hne (fun slot _ => hnone slot)
  rw [hframe.sum_mass, ← Finset.mul_sum] at hlt
  linarith

/-! ## Layer 3 — the wrapping, which is the real-only ingredient

The doubled readings of a plane frame are vectors of a PLANE, and they total
zero.  The traceless part of a real symmetric two-by-two matrix has dimension
two, and the traceless part of a Hermitian two-by-two matrix has dimension
three.  Every law of this layer, and the three-atom count of the cap residue
that the selection theorem calls, rests on the count TWO.  This layer is the
only place where the field enters. -/

/-- **NO OPEN HALF PLANE HOLDS THE DOUBLED ATOMS.**  At every direction of the
doubled plane some slot reads at most zero. -/
theorem PlaneParseval.exists_nonpos_planeDouble_reading {slotCount : ℕ}
    {atom : Fin slotCount → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    (hcount : 0 < slotCount) (point : Fin 2 → ℝ) :
    ∃ slot, point ⬝ᵥ planeDouble (atom slot) ≤ 0 := by
  classical
  haveI : Nonempty (Fin slotCount) := Fin.pos_iff_nonempty.mp hcount
  have hne : (Finset.univ : Finset (Fin slotCount)).Nonempty := Finset.univ_nonempty
  have hsum : (∑ slot, point ⬝ᵥ planeDouble (atom slot)) ≤ ∑ _slot : Fin slotCount, (0 : ℝ) := by
    rw [hframe.sum_dot_planeDouble point, Finset.sum_const_zero]
  obtain ⟨slot, _, hslot⟩ := Finset.exists_le_of_sum_le hne hsum
  exact ⟨slot, hslot⟩

/-- **THE HALF-PLANE LAW.**  If no slot reads negative against a direction of the
doubled plane, then every slot reads exactly zero.  A frame whose doubled atoms
sit in a closed half plane has them all on its boundary line. -/
theorem PlaneParseval.planeDouble_reading_eq_zero {slotCount : ℕ}
    {atom : Fin slotCount → (Fin 2 → ℝ)} (hframe : PlaneParseval atom) {point : Fin 2 → ℝ}
    (hhalf : ∀ slot, 0 ≤ point ⬝ᵥ planeDouble (atom slot)) (slot : Fin slotCount) :
    point ⬝ᵥ planeDouble (atom slot) = 0 := by
  classical
  have hsum := hframe.sum_dot_planeDouble point
  have hother : (0 : ℝ) ≤ ∑ other ∈ Finset.univ.erase slot, point ⬝ᵥ planeDouble (atom other) :=
    Finset.sum_nonneg (fun other _ => hhalf other)
  have hsplit : (∑ other ∈ Finset.univ.erase slot, point ⬝ᵥ planeDouble (atom other))
      = (∑ other, point ⬝ᵥ planeDouble (atom other)) - point ⬝ᵥ planeDouble (atom slot) :=
    Finset.sum_erase_eq_sub (f := fun other => point ⬝ᵥ planeDouble (atom other))
      (Finset.mem_univ slot)
  rw [hsum] at hsplit
  linarith [hhalf slot, hother, hsplit.ge, hsplit.le]

/-- **THE SEPARATED PARTNER.**  Every slot of a plane frame of at least two slots
has a partner whose squared dot against it misses half the product of the two
masses.  The two lines are at least forty-five degrees apart.

This is the wrapping of the doubled atoms, read at one slot: the doubled
readings against one atom total zero, and the atom reads its own square. -/
theorem PlaneParseval.exists_separated_partner {slotCount : ℕ}
    {atom : Fin slotCount → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    (hcount : 2 ≤ slotCount) (slot : Fin slotCount) :
    ∃ other, other ≠ slot
      ∧ 2 * (atom slot ⬝ᵥ atom other) ^ 2
        ≤ (atom slot ⬝ᵥ atom slot) * (atom other ⬝ᵥ atom other) := by
  classical
  have hsum := hframe.sum_dot_planeDouble (planeDouble (atom slot))
  have hsplit : (∑ other ∈ Finset.univ.erase slot,
        planeDouble (atom slot) ⬝ᵥ planeDouble (atom other))
      = (∑ other, planeDouble (atom slot) ⬝ᵥ planeDouble (atom other))
        - planeDouble (atom slot) ⬝ᵥ planeDouble (atom slot) :=
    Finset.sum_erase_eq_sub
      (f := fun other => planeDouble (atom slot) ⬝ᵥ planeDouble (atom other))
      (Finset.mem_univ slot)
  rw [hsum, planeDouble_dot_self] at hsplit
  have hne : (Finset.univ.erase slot).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ slot), Finset.card_univ,
      Fintype.card_fin]
    omega
  have hle : (∑ other ∈ Finset.univ.erase slot,
      planeDouble (atom slot) ⬝ᵥ planeDouble (atom other))
      ≤ ∑ _other ∈ Finset.univ.erase slot, (0 : ℝ) := by
    rw [hsplit, Finset.sum_const_zero]
    nlinarith [sq_nonneg (atom slot ⬝ᵥ atom slot)]
  obtain ⟨other, hmem, hother⟩ := Finset.exists_le_of_sum_le hne hle
  refine ⟨other, Finset.ne_of_mem_erase hmem, ?_⟩
  rw [planeDouble_dot] at hother
  linarith

/-! ## Layer 4 — the pair test and its certificate -/

/-- **THE PAIR TEST.**  The two scaled outer products dominate the identity of
the plane, written division free at every probe. -/
def PlanePairDominates (atomOne atomTwo : Fin 2 → ℝ) (scaleOne scaleTwo : ℝ) : Prop :=
  ∀ probe : Fin 2 → ℝ,
    scaleOne * scaleTwo * (probe ⬝ᵥ probe)
      ≤ scaleTwo * (atomOne ⬝ᵥ probe) ^ 2 + scaleOne * (atomTwo ⬝ᵥ probe) ^ 2

/-- The pair test does not depend on the order of the two slots. -/
theorem PlanePairDominates.symm {atomOne atomTwo : Fin 2 → ℝ} {scaleOne scaleTwo : ℝ}
    (hdom : PlanePairDominates atomOne atomTwo scaleOne scaleTwo) :
    PlanePairDominates atomTwo atomOne scaleTwo scaleOne := by
  intro probe
  have := hdom probe
  linarith [this, mul_comm scaleOne scaleTwo]

/-- **THE DIVISION FORM OF THE PAIR TEST.**  A consumer that carries reciprocals
reads the domination as a sum of two ratios. -/
theorem PlanePairDominates.le_div {atomOne atomTwo : Fin 2 → ℝ} {scaleOne scaleTwo : ℝ}
    (hdom : PlanePairDominates atomOne atomTwo scaleOne scaleTwo)
    (hposOne : 0 < scaleOne) (hposTwo : 0 < scaleTwo) (probe : Fin 2 → ℝ) :
    probe ⬝ᵥ probe
      ≤ (atomOne ⬝ᵥ probe) ^ 2 / scaleOne + (atomTwo ⬝ᵥ probe) ^ 2 / scaleTwo := by
  have hkey := hdom probe
  rw [div_add_div _ _ (ne_of_gt hposOne) (ne_of_gt hposTwo), le_div_iff₀ (by positivity)]
  nlinarith [hkey]

/-- **THE SCALAR CORE.**  A binary quadratic form of nonnegative trace and
nonnegative discriminant is nonnegative at every point.  No eigenvalue, no
square root, no dimension. -/
theorem planeForm_nonneg {formA formB formC first second : ℝ}
    (htrace : 0 ≤ formA + formC) (hdisc : formB ^ 2 ≤ formA * formC) :
    0 ≤ formA * first ^ 2 + 2 * formB * (first * second) + formC * second ^ 2 := by
  have hkey : (formA + formC)
      * (formA * first ^ 2 + 2 * formB * (first * second) + formC * second ^ 2)
      = (formA * first + formB * second) ^ 2 + (formB * first + formC * second) ^ 2
        + (formA * formC - formB ^ 2) * (first ^ 2 + second ^ 2) := by
    ring
  rcases eq_or_lt_of_le htrace with heq | hlt
  · have hzeroA : formA = 0 := by nlinarith [sq_nonneg formA, sq_nonneg formB]
    have hzeroB : formB = 0 := by nlinarith [sq_nonneg formB]
    have hzeroC : formC = 0 := by linarith
    rw [hzeroA, hzeroB, hzeroC]
    norm_num
  · have hrest : 0 ≤ (formA * formC - formB ^ 2) * (first ^ 2 + second ^ 2) :=
      mul_nonneg (by linarith) (by positivity)
    have hprod : 0 ≤ (formA + formC)
        * (formA * first ^ 2 + 2 * formB * (first * second) + formC * second ^ 2) := by
      rw [hkey]
      have hone : (0 : ℝ) ≤ (formA * first + formB * second) ^ 2 := sq_nonneg _
      have htwo : (0 : ℝ) ≤ (formB * first + formC * second) ^ 2 := sq_nonneg _
      linarith
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [hprod, hlt, hneg]

/-- **THE PAIR CERTIFICATE.**  A nonnegative shifted trace and a nonnegative
shifted determinant give the domination.

The two hypotheses are the trace and the determinant of the pair matrix minus
the identity, cleared of every division. -/
theorem planePairDominates_of_certificate {atomOne atomTwo : Fin 2 → ℝ} {scaleOne scaleTwo : ℝ}
    (hposOne : 0 < scaleOne) (hposTwo : 0 < scaleTwo)
    (htrace : 2 * (scaleOne * scaleTwo)
      ≤ scaleTwo * (atomOne ⬝ᵥ atomOne) + scaleOne * (atomTwo ⬝ᵥ atomTwo))
    (hdet : (atomOne ⬝ᵥ atomTwo) ^ 2
      ≤ (atomOne ⬝ᵥ atomOne - scaleOne) * (atomTwo ⬝ᵥ atomTwo - scaleTwo)) :
    PlanePairDominates atomOne atomTwo scaleOne scaleTwo := by
  intro probe
  simp only [dot_fin_two] at htrace hdet ⊢
  have hgap : 0 ≤ (atomOne 0 * atomOne 0 + atomOne 1 * atomOne 1 - scaleOne)
      * (atomTwo 0 * atomTwo 0 + atomTwo 1 * atomTwo 1 - scaleTwo)
      - (atomOne 0 * atomTwo 0 + atomOne 1 * atomTwo 1) ^ 2 := by linarith
  have hscaled : 0 ≤ scaleOne * scaleTwo
      * ((atomOne 0 * atomOne 0 + atomOne 1 * atomOne 1 - scaleOne)
          * (atomTwo 0 * atomTwo 0 + atomTwo 1 * atomTwo 1 - scaleTwo)
        - (atomOne 0 * atomTwo 0 + atomOne 1 * atomTwo 1) ^ 2) :=
    mul_nonneg (le_of_lt (mul_pos hposOne hposTwo)) hgap
  have hdisc : (scaleTwo * (atomOne 0 * atomOne 1) + scaleOne * (atomTwo 0 * atomTwo 1)) ^ 2
      ≤ (scaleTwo * atomOne 0 ^ 2 + scaleOne * atomTwo 0 ^ 2 - scaleOne * scaleTwo)
        * (scaleTwo * atomOne 1 ^ 2 + scaleOne * atomTwo 1 ^ 2 - scaleOne * scaleTwo) := by
    nlinarith [hscaled]
  have hcore := planeForm_nonneg
    (formA := scaleTwo * atomOne 0 ^ 2 + scaleOne * atomTwo 0 ^ 2 - scaleOne * scaleTwo)
    (formB := scaleTwo * (atomOne 0 * atomOne 1) + scaleOne * (atomTwo 0 * atomTwo 1))
    (formC := scaleTwo * atomOne 1 ^ 2 + scaleOne * atomTwo 1 ^ 2 - scaleOne * scaleTwo)
    (first := probe 0) (second := probe 1) (by nlinarith [htrace]) hdisc
  nlinarith [hcore]

/-- **THE TRACE READING OF A DOMINATING PAIR.**  A dominating pair carries the
first half of its own certificate. -/
theorem planePair_trace_of_dominates {atomOne atomTwo : Fin 2 → ℝ} {scaleOne scaleTwo : ℝ}
    (hdom : PlanePairDominates atomOne atomTwo scaleOne scaleTwo) :
    2 * (scaleOne * scaleTwo)
      ≤ scaleTwo * (atomOne ⬝ᵥ atomOne) + scaleOne * (atomTwo ⬝ᵥ atomTwo) := by
  have hfirst := hdom ![1, 0]
  have hsecond := hdom ![0, 1]
  simp only [dot_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hfirst hsecond
  simp only [dot_fin_two]
  nlinarith [hfirst, hsecond]

/-- **THE DETERMINANT READING OF A DOMINATING PAIR.**  A dominating pair carries
the second half of its own certificate.  Four probes read it: the two frame
directions, the adjugate direction, and the two diagonals. -/
theorem planePair_certificate_of_dominates {atomOne atomTwo : Fin 2 → ℝ} {scaleOne scaleTwo : ℝ}
    (hposOne : 0 < scaleOne) (hposTwo : 0 < scaleTwo)
    (hdom : PlanePairDominates atomOne atomTwo scaleOne scaleTwo) :
    (atomOne ⬝ᵥ atomTwo) ^ 2
      ≤ (atomOne ⬝ᵥ atomOne - scaleOne) * (atomTwo ⬝ᵥ atomTwo - scaleTwo) := by
  have hformA : (0 : ℝ) ≤ scaleTwo * atomOne 0 ^ 2 + scaleOne * atomTwo 0 ^ 2
      - scaleOne * scaleTwo := by
    have hprobe := hdom ![1, 0]
    simp only [dot_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hprobe
    nlinarith [hprobe]
  have hformC : (0 : ℝ) ≤ scaleTwo * atomOne 1 ^ 2 + scaleOne * atomTwo 1 ^ 2
      - scaleOne * scaleTwo := by
    have hprobe := hdom ![0, 1]
    simp only [dot_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hprobe
    nlinarith [hprobe]
  set formA := scaleTwo * atomOne 0 ^ 2 + scaleOne * atomTwo 0 ^ 2 - scaleOne * scaleTwo
    with hformAdef
  set formB := scaleTwo * (atomOne 0 * atomOne 1) + scaleOne * (atomTwo 0 * atomTwo 1)
    with hformBdef
  set formC := scaleTwo * atomOne 1 ^ 2 + scaleOne * atomTwo 1 ^ 2 - scaleOne * scaleTwo
    with hformCdef
  have hdisc : formB ^ 2 ≤ formA * formC := by
    rcases eq_or_lt_of_le hformA with hzeroA | hposA
    · rcases eq_or_lt_of_le hformC with hzeroC | hposC
      · have hplus := hdom ![1, 1]
        have hminus := hdom ![1, -1]
        simp only [dot_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          mul_one, mul_neg] at hplus hminus
        have hplusForm : 0 ≤ 2 * formB := by
          rw [hformAdef, hformBdef, hformCdef] at *
          nlinarith [hplus, hzeroA, hzeroC]
        have hminusForm : 0 ≤ -(2 * formB) := by
          rw [hformAdef, hformBdef, hformCdef] at *
          nlinarith [hminus, hzeroA, hzeroC]
        have hzeroB : formB = 0 := by linarith
        rw [hzeroB, ← hzeroA, ← hzeroC]
        norm_num
      · have hprobe := hdom ![formC, -formB]
        simp only [dot_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          mul_neg, neg_mul] at hprobe
        have hkey : 0 ≤ formC * (formA * formC - formB ^ 2) := by
          rw [hformAdef, hformBdef, hformCdef] at *
          nlinarith [hprobe]
        nlinarith [hkey, hposC]
    · have hprobe := hdom ![-formB, formA]
      simp only [dot_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        mul_neg, neg_mul] at hprobe
      have hkey : 0 ≤ formA * (formA * formC - formB ^ 2) := by
        rw [hformAdef, hformBdef, hformCdef] at *
        nlinarith [hprobe]
      nlinarith [hkey, hposA]
  have hexpand : formA * formC - formB ^ 2
      = scaleOne * scaleTwo * ((atomOne ⬝ᵥ atomOne - scaleOne) * (atomTwo ⬝ᵥ atomTwo - scaleTwo)
        - (atomOne ⬝ᵥ atomTwo) ^ 2) := by
    rw [hformAdef, hformBdef, hformCdef]
    simp only [dot_fin_two]
    ring
  have hpos : 0 < scaleOne * scaleTwo := mul_pos hposOne hposTwo
  nlinarith [hdisc, hexpand, hpos]

/-- **THE PAIR TEST IS THE CERTIFICATE.**  At positive scales the domination and
the two division-free readings are the same statement. -/
theorem planePairDominates_iff {atomOne atomTwo : Fin 2 → ℝ} {scaleOne scaleTwo : ℝ}
    (hposOne : 0 < scaleOne) (hposTwo : 0 < scaleTwo) :
    PlanePairDominates atomOne atomTwo scaleOne scaleTwo
      ↔ (2 * (scaleOne * scaleTwo)
            ≤ scaleTwo * (atomOne ⬝ᵥ atomOne) + scaleOne * (atomTwo ⬝ᵥ atomTwo)
          ∧ (atomOne ⬝ᵥ atomTwo) ^ 2
            ≤ (atomOne ⬝ᵥ atomOne - scaleOne) * (atomTwo ⬝ᵥ atomTwo - scaleTwo)) := by
  constructor
  · intro hdom
    exact ⟨planePair_trace_of_dominates hdom,
      planePair_certificate_of_dominates hposOne hposTwo hdom⟩
  · intro hcert
    exact planePairDominates_of_certificate hposOne hposTwo hcert.1 hcert.2

/-! ## Layer 4 — the selection theorem -/

/-- **THE PLANE PAIR SELECTION THEOREM.**  A plane frame of at least three
slots, with positive scales of total less than one, carries a PAIR of slots
whose scaled outer products dominate the identity of the plane.

The proof reads the failure of every pair as a family of half planes of the
disc.  The landed cap residue supplies a common point, the wrap law makes the
reading of that point total zero, and the mass law then puts the scale total at
one or more.  The hypothesis refuses that total. -/
theorem exists_dominatingPlanePair {slotCount : ℕ} (hcount : 3 ≤ slotCount)
    (atom : Fin slotCount → (Fin 2 → ℝ)) (scale : Fin slotCount → ℝ)
    (hframe : PlaneParseval atom) (hpos : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ PlanePairDominates (atom slotOne) (atom slotTwo) (scale slotOne) (scale slotTwo) := by
  classical
  by_contra hnone
  simp only [not_exists, not_and] at hnone
  have hgapLe : ∀ slot, max 0 (atom slot ⬝ᵥ atom slot - scale slot) ≤ atom slot ⬝ᵥ atom slot :=
    fun slot => max_le (plane_dot_self_nonneg _) (by linarith [hpos slot])
  have hgapNonneg : ∀ slot, (0 : ℝ) ≤ max 0 (atom slot ⬝ᵥ atom slot - scale slot) :=
    fun slot => le_max_left _ _
  have hpairGap : ∀ slotOne slotTwo,
      max 0 (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
        * max 0 (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)
          ≤ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 := by
    intro slotOne slotTwo
    by_cases hsame : slotOne = slotTwo
    · subst hsame
      have hle := hgapLe slotOne
      have hnn := hgapNonneg slotOne
      nlinarith [hle, hnn]
    · by_contra hbig
      rw [not_le] at hbig
      have hprodPos : 0 < max 0 (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          * max 0 (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) :=
        lt_of_le_of_lt (sq_nonneg _) hbig
      have hposOne : 0 < max 0 (atom slotOne ⬝ᵥ atom slotOne - scale slotOne) :=
        (hgapNonneg slotOne).lt_of_ne' (by
          intro hzero
          rw [hzero, zero_mul] at hprodPos
          exact lt_irrefl _ hprodPos)
      have hposTwo : 0 < max 0 (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) :=
        (hgapNonneg slotTwo).lt_of_ne' (by
          intro hzero
          rw [hzero, mul_zero] at hprodPos
          exact lt_irrefl _ hprodPos)
      have hlackOne : 0 < atom slotOne ⬝ᵥ atom slotOne - scale slotOne := by
        rcases lt_max_iff.mp hposOne with hzero | hgap
        · exact absurd hzero (lt_irrefl 0)
        · exact hgap
      have hlackTwo : 0 < atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo := by
        rcases lt_max_iff.mp hposTwo with hzero | hgap
        · exact absurd hzero (lt_irrefl 0)
        · exact hgap
      have hgapOne : max 0 (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          = atom slotOne ⬝ᵥ atom slotOne - scale slotOne := max_eq_right (le_of_lt hlackOne)
      have hgapTwo : max 0 (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)
          = atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo := max_eq_right (le_of_lt hlackTwo)
      rw [hgapOne, hgapTwo] at hbig
      refine hnone slotOne slotTwo hsame
        (planePairDominates_of_certificate (hpos slotOne) (hpos slotTwo) ?_ ?_)
      · nlinarith [hlackOne, hlackTwo, hpos slotOne, hpos slotTwo]
      · linarith [hbig]
  obtain ⟨point, _, hlevel⟩ :=
    exists_capPoint_of_triple hcount planeCapTripleClosed_holds
      (fun slot => planeDouble (atom slot))
      (fun slot => atom slot ⬝ᵥ atom slot)
      (fun slot => max 0 (atom slot ⬝ᵥ atom slot - scale slot))
      (fun slot => planeDouble_dot_self _) hgapNonneg hgapLe
      (fun slotOne slotTwo => by
        rw [planeDouble_dot]
        nlinarith [hpairGap slotOne slotTwo])
  have hsumLevel : (∑ slot, (2 * max 0 (atom slot ⬝ᵥ atom slot - scale slot)
      - atom slot ⬝ᵥ atom slot)) ≤ ∑ slot, point ⬝ᵥ planeDouble (atom slot) :=
    Finset.sum_le_sum (fun slot _ => hlevel slot)
  rw [hframe.sum_dot_planeDouble point, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hframe.sum_mass] at hsumLevel
  have hlower : (∑ slot, (atom slot ⬝ᵥ atom slot - scale slot))
      ≤ ∑ slot, max 0 (atom slot ⬝ᵥ atom slot - scale slot) :=
    Finset.sum_le_sum (fun slot _ => le_max_right _ _)
  rw [Finset.sum_sub_distrib, hframe.sum_mass] at hlower
  linarith

/-- **THE QUANTITATIVE MARGIN.**  A plane frame whose scale total misses one by
`slack` carries a pair that dominates the identity with the factor
`1 + slack / 2`.

The margin is what a Schur consumer spends against a rank-one penalty.  The
factor cannot be improved to a positive margin at slack zero: refer to
`Gtz.planeTrine_not_dominates`. -/
theorem exists_dominatingPlanePair_margin {slotCount : ℕ} (hcount : 3 ≤ slotCount)
    (atom : Fin slotCount → (Fin 2 → ℝ)) (scale : Fin slotCount → ℝ)
    (hframe : PlaneParseval atom) (hpos : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo ∧ ∀ probe : Fin 2 → ℝ,
      (1 + (1 - ∑ slot, scale slot) / 2) * (scale slotOne * scale slotTwo) * (probe ⬝ᵥ probe)
        ≤ scale slotTwo * (atom slotOne ⬝ᵥ probe) ^ 2
          + scale slotOne * (atom slotTwo ⬝ᵥ probe) ^ 2 := by
  classical
  set slack := 1 - ∑ slot, scale slot with hslackDef
  have hslack : 0 < slack := by rw [hslackDef]; linarith
  have hfactor : (0 : ℝ) < 1 + slack / 2 := by linarith
  have hinflate : (∑ slot, (1 + slack / 2) * scale slot) < 1 := by
    rw [← Finset.mul_sum]
    have hsum : (∑ slot, scale slot) = 1 - slack := by rw [hslackDef]; ring
    rw [hsum]
    nlinarith [hslack]
  obtain ⟨slotOne, slotTwo, hne, hdom⟩ :=
    exists_dominatingPlanePair hcount atom (fun slot => (1 + slack / 2) * scale slot) hframe
      (fun slot => mul_pos hfactor (hpos slot)) hinflate
  refine ⟨slotOne, slotTwo, hne, fun probe => ?_⟩
  have hkey := hdom probe
  nlinarith [hkey, hfactor, mul_pos (hpos slotOne) (hpos slotTwo),
    plane_dot_self_nonneg probe]

/-- **THE MARGIN IN PAIR-TEST SHAPE.**  The dominating pair of the margin
theorem dominates at the INFLATED scales, so every law of the pair test applies
to it without a rescale at the call site. -/
theorem exists_dominatingPlanePair_inflated {slotCount : ℕ} (hcount : 3 ≤ slotCount)
    (atom : Fin slotCount → (Fin 2 → ℝ)) (scale : Fin slotCount → ℝ)
    (hframe : PlaneParseval atom) (hpos : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ PlanePairDominates (atom slotOne) (atom slotTwo)
          ((1 + (1 - ∑ slot, scale slot) / 2) * scale slotOne)
          ((1 + (1 - ∑ slot, scale slot) / 2) * scale slotTwo) := by
  classical
  have hslack : 0 < 1 - ∑ slot, scale slot := by linarith
  have hfactor : (0 : ℝ) < 1 + (1 - ∑ slot, scale slot) / 2 := by linarith
  have hinflate : (∑ slot, (1 + (1 - ∑ other, scale other) / 2) * scale slot) < 1 := by
    rw [← Finset.mul_sum]
    nlinarith [hslack]
  exact exists_dominatingPlanePair hcount atom
    (fun slot => (1 + (1 - ∑ other, scale other) / 2) * scale slot) hframe
    (fun slot => mul_pos hfactor (hpos slot)) hinflate

/-- **THE FOUR-ATOM SELECTION THEOREM.**  The base case of the campaign's
reduction. -/
theorem exists_dominatingPlanePair_four (atom : Fin 4 → (Fin 2 → ℝ)) (scale : Fin 4 → ℝ)
    (hframe : PlaneParseval atom) (hpos : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ PlanePairDominates (atom slotOne) (atom slotTwo) (scale slotOne) (scale slotTwo) :=
  exists_dominatingPlanePair (by norm_num) atom scale hframe hpos hsmall

/-- **THE FIVE-ATOM SELECTION THEOREM.**  The count of the plane shadows of a
six-atom design at a pivot. -/
theorem exists_dominatingPlanePair_five (atom : Fin 5 → (Fin 2 → ℝ)) (scale : Fin 5 → ℝ)
    (hframe : PlaneParseval atom) (hpos : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ PlanePairDominates (atom slotOne) (atom slotTwo) (scale slotOne) (scale slotTwo) :=
  exists_dominatingPlanePair (by norm_num) atom scale hframe hpos hsmall

/-- **THE DIVISION FORM OF THE SELECTION THEOREM.** -/
theorem exists_dominatingPlanePair_div {slotCount : ℕ} (hcount : 3 ≤ slotCount)
    (atom : Fin slotCount → (Fin 2 → ℝ)) (scale : Fin slotCount → ℝ)
    (hframe : PlaneParseval atom) (hpos : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo ∧ ∀ probe : Fin 2 → ℝ,
      probe ⬝ᵥ probe ≤ (atom slotOne ⬝ᵥ probe) ^ 2 / scale slotOne
        + (atom slotTwo ⬝ᵥ probe) ^ 2 / scale slotTwo := by
  obtain ⟨slotOne, slotTwo, hne, hdom⟩ :=
    exists_dominatingPlanePair hcount atom scale hframe hpos hsmall
  exact ⟨slotOne, slotTwo, hne,
    fun probe => hdom.le_div (hpos slotOne) (hpos slotTwo) probe⟩

/-! ## Layer 5 — the trine, and the sharpness of the margin -/

/-- **THE TRINE.**  Three lines of the plane at sixty degrees, each of mass two
thirds.  The trine is the extremal datum of the selection theorem. -/
noncomputable def planeTrineAtom : Fin 3 → (Fin 2 → ℝ)
  | 0 => ![Real.sqrt (2 / 3), 0]
  | 1 => ![Real.sqrt (1 / 6), Real.sqrt (1 / 2)]
  | 2 => ![-Real.sqrt (1 / 6), Real.sqrt (1 / 2)]

theorem planeTrineAtom_sq_first : Real.sqrt (2 / 3) * Real.sqrt (2 / 3) = 2 / 3 :=
  Real.mul_self_sqrt (by norm_num)

theorem planeTrineAtom_sq_sixth : Real.sqrt (1 / 6) * Real.sqrt (1 / 6) = 1 / 6 :=
  Real.mul_self_sqrt (by norm_num)

theorem planeTrineAtom_sq_half : Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = 1 / 2 :=
  Real.mul_self_sqrt (by norm_num)

theorem planeTrineAtom_mixed : Real.sqrt (2 / 3) * Real.sqrt (1 / 6) = 1 / 3 := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  rw [show (2 / 3 : ℝ) * (1 / 6) = (1 / 3) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- The trine is a plane frame. -/
theorem planeTrineAtom_parseval : PlaneParseval planeTrineAtom := by
  refine planeParseval_of_entries ?_ ?_ ?_ <;>
    simp only [Fin.sum_univ_three, planeTrineAtom, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;>
    nlinarith [planeTrineAtom_sq_first, planeTrineAtom_sq_sixth, planeTrineAtom_sq_half]

/-- Every atom of the trine carries two thirds of a unit of mass. -/
theorem planeTrineAtom_mass (slot : Fin 3) :
    planeTrineAtom slot ⬝ᵥ planeTrineAtom slot = 2 / 3 := by
  fin_cases slot <;>
    simp only [dot_fin_two, planeTrineAtom, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;>
    nlinarith [planeTrineAtom_sq_first, planeTrineAtom_sq_sixth, planeTrineAtom_sq_half]

/-- Every pair of the trine reads a squared dot of one ninth. -/
theorem planeTrineAtom_dot {slotOne slotTwo : Fin 3} (hne : slotOne ≠ slotTwo) :
    (planeTrineAtom slotOne ⬝ᵥ planeTrineAtom slotTwo) ^ 2 = 1 / 9 := by
  fin_cases slotOne <;> fin_cases slotTwo <;>
    simp_all only [ne_eq, not_true_eq_false] <;>
    simp only [dot_fin_two, planeTrineAtom, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;>
    nlinarith [planeTrineAtom_sq_sixth, planeTrineAtom_sq_half, planeTrineAtom_mixed]

/-- **THE SHARPNESS CALIBRATION.**  At the trine no pair dominates the identity
at any inflated scale.  The trine has scale total exactly one, thus the
selection theorem admits NO positive margin at scale total one, and the strict
budget of `Gtz.exists_dominatingPlanePair` is not a convenience. -/
theorem planeTrine_not_dominates {factor : ℝ} (hfactor : 1 < factor)
    (slotOne slotTwo : Fin 3) (hne : slotOne ≠ slotTwo) :
    ¬ PlanePairDominates (planeTrineAtom slotOne) (planeTrineAtom slotTwo)
        (factor / 3) (factor / 3) := by
  intro hdom
  have hposFactor : (0 : ℝ) < factor / 3 := by linarith
  have htrace := planePair_trace_of_dominates hdom
  have hdet := planePair_certificate_of_dominates hposFactor hposFactor hdom
  rw [planeTrineAtom_mass slotOne, planeTrineAtom_mass slotTwo] at htrace hdet
  rw [planeTrineAtom_dot hne] at hdet
  nlinarith [htrace, hdet, hfactor]

/-- The trine sits at scale total exactly one. -/
theorem planeTrine_scale_total : (∑ _slot : Fin 3, (1 : ℝ) / 3) = 1 := by
  norm_num

end Gtz

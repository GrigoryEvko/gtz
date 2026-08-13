import Gtz.Wave.OuterZeroProfileLattice
import Gtz.Wave.SharedPrivateSpectralSplit
import Gtz.Wave.ChartBlockCeiling
import Gtz.Wave.DenseBlockGeometry
import Gtz.Wave.OuterCircuitPinResidue
import Gtz.Reduction.ChartAttainmentWeld

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The atom energy and the ceiling — the design geometry of the third rung

Every kill of the rank-six wall until this module reads the frame and
not the design.  The frame prices the coefficient matrix, the read
values, the Gram core and the commutation, and the numeric sweep of the
outer-zero layer shows that the frame laws do NOT close: the surviving
locus of the frame system is nonempty at every layer the frame can
state.  The reason is structural.  The frame forgets that the chart is
the projection of a six-point design in three dimensions, and it forgets
the CEILING, that is, the fact that the chart value is the MAXIMUM of the
block values and thus caps every triple and not only the active ones.

This module supplies the missing layer.  It is the atom dictionary.

The chart is a symmetric idempotent of trace three, thus the spectral
split writes it as the sum of the rank ones of three orthonormal
vectors.  Read that family by columns: each atom carries a vector in
three dimensions, the ATOM VECTOR, and the chart entry at a pair of
atoms is the dot product of the two atom vectors.  Three laws follow at
once, and they are the whole layer.

The first law is the FRAME LAW.  The orthonormality of the family says
that the six atom vectors form a tight frame of the three-dimensional
probe space: the energy of every probe against the six atom vectors is
the square norm of that probe.  The law needs no design, no chart value,
and no stationarity.

The second law is the BLEND IDENTITY.  The quadratic form of the chart
at an ambient vector is the square norm of the blend of the atom vectors
against that vector.  Thus the shifted gap form splits into a
three-dimensional energy minus a weighted square sum, and the whole
chart geometry moves to three dimensions.

The third law is the ESCAPE LAW.  The shifted weights of a rank-six
frame are positive and sum to less than one, because the chart value is
negative.  Thus at every probe some atom reads more energy than its own
shifted weight, and the ratio form gives the sharp constant: some atom
beats the shifted weight by the reciprocal of the shifted total.

The escape law and the read law together give the CONFINEMENT.  At an
active block the read law prices the atom energy of the blend by the
shifted weight times the blend energy, at every atom OF the block.  The
escape atom therefore never sits in the block: at every basis column of
a rank-six frame some atom OUTSIDE the block reads strongly against the
blend of that column.  This is a new structural law of the rank-six
wall, and it is a law about the design and not about the frame.

The last layer names the residue and discharges the rung.  The residue
is the ATOM TRIPLE CEILING: six vectors in three dimensions that form a
tight frame, together with six positive scales of total less than one,
carry a triple whose shifted form is strictly positive.  The residue
carries no crux, no chart, no frame, no stationarity, and no
combinatorics — it is one sharp inequality about six vectors and six
scales, and the design sweep of this session confirms it with a wide
margin.  From the residue the crux dies at every interior datum, thus
the rank-six frame dies, thus all three named residues of the
outer-zero lattice — circuit, regular, and thin — die together, and the
rank-six support-two closure holds.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomVec` — the atom vector of a spectral family.
* `Gtz.atomBlend` — the blend of the atom vectors against an ambient
  vector.
* `Gtz.atomVec_dot_eq_split_apply` — the chart entry is an atom dot
  product.
* `Gtz.atomBlend_dot` — the blend reads by the atom energies.
* `Gtz.atom_frame_law` — **THE FRAME LAW.**
* `Gtz.atom_frame_energy` — its energy reading.
* `Gtz.atom_frame_split` — the carrier split of the frame law.
* `Gtz.mulVec_eq_atomVec_dot_atomBlend` — the chart action in atom form.
* `Gtz.quadratic_eq_atomBlend_energy` — **THE BLEND IDENTITY.**
* `Gtz.shifted_quadratic_eq` — the shifted gap form in atom terms.
* `Gtz.exists_escape_atom` — **THE ESCAPE LAW.**
* `Gtz.exists_escape_atom_ratio` — its sharp ratio form.
* `Gtz.block_blend_energy_eq` — the blend energy of a read vector.
* `Gtz.block_blend_energy_pos` — the blend of a live read vector is
  alive.
* `Gtz.block_atom_energy_le` — **THE CONFINEMENT.**
* `Gtz.block_carrier_energy_le` — the carrier share of the frame law.
* `Gtz.block_leak_energy_ge` — **THE LEAK FLOOR.**
* `Gtz.exists_escape_outside_block` — **THE OUTSIDE ESCAPE.**
* `Gtz.SixThreeCrux.exists_atom_system` — the atom system of a crux.
* `Gtz.AtomTripleCeilingClosed` — **THE ATOM TRIPLE CEILING RESIDUE.**
* `Gtz.sum_eq_sum_orderEmbOfFin`, `Gtz.carrierLift`,
  `Gtz.carrierLift_vanish`, `Gtz.carrierLift_apply` — the carrier lift.
* `Gtz.SixThreeCrux.exists_ceiling_witness` — **THE CEILING IN ATOM
  FORM**, at every triple and not only at the active ones.
* `Gtz.SixThreeCrux.false_of_atomTripleCeiling` — the crux dies at an
  interior datum.
* `Gtz.RankSixFrame.false_of_atomTripleCeiling` — **THE RANK-SIX KILL.**
* `Gtz.RankSixFrame.exists_escape_outside_block` — the outside escape at
  a rank-six frame.
* `Gtz.rankSixOuterKilled_of_atomTripleCeiling`,
  `Gtz.rankSixSupportTwoClosed_of_atomTripleCeiling` — **THE RANK-SIX
  DISCHARGE FROM ONE DESIGN-SIDE RESIDUE.**
* `Gtz.rankSixOuterCircuitClosed_of_atomTripleCeiling`,
  `Gtz.rankSixOuterRegularClosed_of_atomTripleCeiling`,
  `Gtz.rankSixOuterThinClosed_of_atomTripleCeiling`,
  `Gtz.rankSixOuterLowProfileClosed_of_atomTripleCeiling` — the named
  residues of the outer-zero lattice.
* `Gtz.rankSixOuterOffPairCircuitClosed_of_atomTripleCeiling`,
  `Gtz.rankSixOuterRankOneCircuitClosed_of_atomTripleCeiling` — the two
  halves of the narrowed circuit residue of the pin calculus.
* `Gtz.gtzWeighted_six_three_of_atomTripleCeiling_of_interior` — the
  whole `(6,3)` statement from the residue and interiority.
* `Gtz.AtomTripleCeilingMarginClosed`,
  `Gtz.atomTripleCeilingClosed_of_margin` — the margin form of the
  residue, which is the shape a numeric certificate produces.
* `Gtz.RankFiveFrame.false_of_atomTripleCeiling_of_interior`,
  `Gtz.RankFourFrame.false_of_atomTripleCeiling_of_interior` — the lower
  ranks, at an interior datum.
* `Gtz.rankFiveOuterKilled_of_atomTripleCeiling_of_interior`,
  `Gtz.rankFiveSupportTwoClosed_of_atomTripleCeiling_of_interior`,
  `Gtz.rankFourOuterKilled_of_atomTripleCeiling_of_interior`,
  `Gtz.rankFourSupportTwoClosed_of_atomTripleCeiling_of_interior` — the
  lower rungs.

## Vacuity

The atom laws of layers zero thru three are unconditional matrix
statements.  The crux statements are vacuous if `Gtz.GtzWeighted 6 3`
holds, because no crux exists then.
-/

namespace Gtz

open Matrix

/-! ## Layer 0 — the atom vector and the blend -/

/-- The ATOM VECTOR of a spectral family at a slot: the column of the
family read as a vector of the family index. -/
def atomVec {slotCount rank : ℕ} (family : Fin rank → (Fin slotCount → ℝ))
    (slot : Fin slotCount) : Fin rank → ℝ :=
  fun index => family index slot

/-- The BLEND of the atom vectors against an ambient vector. -/
def atomBlend {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (probe : Fin slotCount → ℝ) : Fin rank → ℝ :=
  fun index => ∑ slot, probe slot * atom slot index

theorem atomVec_apply {slotCount rank : ℕ} (family : Fin rank → (Fin slotCount → ℝ))
    (slot : Fin slotCount) (index : Fin rank) :
    atomVec family slot index = family index slot := rfl

theorem atomBlend_apply {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (probe : Fin slotCount → ℝ) (index : Fin rank) :
    atomBlend atom probe index = ∑ slot, probe slot * atom slot index := rfl

/-- The chart entry at a pair of atoms is the dot product of the two atom
vectors. -/
theorem atomVec_dot_eq_split_apply {slotCount rank : ℕ}
    {chart : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    {family : Fin rank → (Fin slotCount → ℝ)}
    (hsplit : chart = ∑ index, Matrix.vecMulVec (family index) (family index))
    (rowSlot colSlot : Fin slotCount) :
    chart rowSlot colSlot = atomVec family rowSlot ⬝ᵥ atomVec family colSlot := by
  rw [hsplit, Matrix.sum_apply, dotProduct]
  exact Finset.sum_congr rfl fun index _ => by rw [Matrix.vecMulVec_apply]; rfl

/-- The blend reads against a probe by the atom energies. -/
theorem atomBlend_dot {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (probe : Fin slotCount → ℝ) (direction : Fin rank → ℝ) :
    atomBlend atom probe ⬝ᵥ direction
      = ∑ slot, probe slot * (atom slot ⬝ᵥ direction) := by
  classical
  rw [dotProduct]
  have hcell : ∀ index : Fin rank,
      atomBlend atom probe index * direction index
        = ∑ slot, probe slot * (atom slot index * direction index) := by
    intro index
    rw [atomBlend_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun slot _ => by ring
  rw [Finset.sum_congr rfl fun index _ => hcell index, Finset.sum_comm]
  refine Finset.sum_congr rfl fun slot _ => ?_
  rw [dotProduct, Finset.mul_sum]

/-! ## Layer 1 — the frame law -/

variable {slotCount rank : ℕ}

/-- **THE FRAME LAW.**  An orthonormal family reads as a tight frame of
the probe space: the joint energy of two probes against the atom vectors
is their dot product. -/
theorem atom_frame_law {family : Fin rank → (Fin slotCount → ℝ)}
    (hnorm : ∀ index, family index ⬝ᵥ family index = 1)
    (horth : ∀ indexOne indexTwo, indexOne ≠ indexTwo →
      family indexOne ⬝ᵥ family indexTwo = 0)
    (probe direction : Fin rank → ℝ) :
    (∑ slot, (atomVec family slot ⬝ᵥ probe) * (atomVec family slot ⬝ᵥ direction))
      = probe ⬝ᵥ direction := by
  classical
  have hcell : ∀ slot : Fin slotCount,
      (atomVec family slot ⬝ᵥ probe) * (atomVec family slot ⬝ᵥ direction)
        = ∑ indexOne, ∑ indexTwo,
            (probe indexOne * direction indexTwo)
              * (family indexOne slot * family indexTwo slot) := by
    intro slot
    rw [dotProduct, dotProduct, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun indexOne _ => Finset.sum_congr rfl fun indexTwo _ => ?_
    rw [atomVec_apply, atomVec_apply]; ring
  rw [Finset.sum_congr rfl fun slot _ => hcell slot, Finset.sum_comm]
  have hinner : ∀ indexOne : Fin rank,
      (∑ slot, ∑ indexTwo, (probe indexOne * direction indexTwo)
          * (family indexOne slot * family indexTwo slot))
        = probe indexOne * direction indexOne := by
    intro indexOne
    rw [Finset.sum_comm]
    have hgram : ∀ indexTwo : Fin rank,
        (∑ slot, (probe indexOne * direction indexTwo)
            * (family indexOne slot * family indexTwo slot))
          = (probe indexOne * direction indexTwo)
              * (family indexOne ⬝ᵥ family indexTwo) := by
      intro indexTwo
      rw [dotProduct, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun indexTwo _ => hgram indexTwo]
    rw [Finset.sum_eq_single indexOne
      (fun indexTwo _ hne => by rw [horth indexOne indexTwo (Ne.symm hne)]; ring)
      (fun hnot => absurd (Finset.mem_univ _) hnot)]
    rw [hnorm indexOne, mul_one]
  rw [Finset.sum_congr rfl fun indexOne _ => hinner indexOne, dotProduct]

/-- The energy reading of the frame law. -/
theorem atom_frame_energy {family : Fin rank → (Fin slotCount → ℝ)}
    (hnorm : ∀ index, family index ⬝ᵥ family index = 1)
    (horth : ∀ indexOne indexTwo, indexOne ≠ indexTwo →
      family indexOne ⬝ᵥ family indexTwo = 0)
    (probe : Fin rank → ℝ) :
    (∑ slot, (atomVec family slot ⬝ᵥ probe) ^ 2) = probe ⬝ᵥ probe := by
  rw [← atom_frame_law hnorm horth probe probe]
  exact Finset.sum_congr rfl fun slot _ => sq _

/-- The carrier split of the frame law: the energy on a carrier and the
energy off it add to the square norm of the probe. -/
theorem atom_frame_split {family : Fin rank → (Fin slotCount → ℝ)}
    (hnorm : ∀ index, family index ⬝ᵥ family index = 1)
    (horth : ∀ indexOne indexTwo, indexOne ≠ indexTwo →
      family indexOne ⬝ᵥ family indexTwo = 0)
    (car : Finset (Fin slotCount)) (probe : Fin rank → ℝ) :
    (∑ slot ∈ car, (atomVec family slot ⬝ᵥ probe) ^ 2)
        + ∑ slot ∈ carᶜ, (atomVec family slot ⬝ᵥ probe) ^ 2
      = probe ⬝ᵥ probe := by
  classical
  rw [← atom_frame_energy hnorm horth probe]
  exact Finset.sum_add_sum_compl car
    (fun slot => (atomVec family slot ⬝ᵥ probe) ^ 2)

/-! ## Layer 2 — the blend identity -/

/-- The chart action in atom form: the chart applied to an ambient vector
reads at each slot as the atom vector against the blend. -/
theorem mulVec_eq_atomVec_dot_atomBlend {chart : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    {family : Fin rank → (Fin slotCount → ℝ)}
    (hsplit : chart = ∑ index, Matrix.vecMulVec (family index) (family index))
    (probe : Fin slotCount → ℝ) (rowSlot : Fin slotCount) :
    (chart *ᵥ probe) rowSlot
      = atomVec family rowSlot ⬝ᵥ atomBlend (atomVec family) probe := by
  classical
  rw [Matrix.mulVec, dotProduct, dotProduct]
  have hcell : ∀ colSlot : Fin slotCount,
      chart rowSlot colSlot * probe colSlot
        = ∑ index, atomVec family rowSlot index * (probe colSlot * atomVec family colSlot index) := by
    intro colSlot
    rw [atomVec_dot_eq_split_apply hsplit rowSlot colSlot, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun index _ => by ring
  rw [Finset.sum_congr rfl fun colSlot _ => hcell colSlot, Finset.sum_comm]
  refine Finset.sum_congr rfl fun index _ => ?_
  rw [atomBlend_apply, Finset.mul_sum]

/-- **THE BLEND IDENTITY.**  The quadratic form of the chart at an
ambient vector is the square norm of the blend. -/
theorem quadratic_eq_atomBlend_energy {chart : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    {family : Fin rank → (Fin slotCount → ℝ)}
    (hsplit : chart = ∑ index, Matrix.vecMulVec (family index) (family index))
    (probe : Fin slotCount → ℝ) :
    probe ⬝ᵥ (chart *ᵥ probe)
      = atomBlend (atomVec family) probe ⬝ᵥ atomBlend (atomVec family) probe := by
  classical
  rw [dotProduct]
  have hcell : ∀ rowSlot : Fin slotCount,
      probe rowSlot * (chart *ᵥ probe) rowSlot
        = probe rowSlot * (atomVec family rowSlot ⬝ᵥ atomBlend (atomVec family) probe) := by
    intro rowSlot
    rw [mulVec_eq_atomVec_dot_atomBlend hsplit probe rowSlot]
  rw [Finset.sum_congr rfl fun rowSlot _ => hcell rowSlot,
    ← atomBlend_dot (atomVec family) probe (atomBlend (atomVec family) probe)]

/-- The shifted gap form in atom terms: the chart form minus the shifted
square sum. -/
theorem shifted_quadratic_eq {chart : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    {family : Fin rank → (Fin slotCount → ℝ)}
    (hsplit : chart = ∑ index, Matrix.vecMulVec (family index) (family index))
    (shift probe : Fin slotCount → ℝ) :
    probe ⬝ᵥ ((chart - Matrix.diagonal shift) *ᵥ probe)
      = atomBlend (atomVec family) probe ⬝ᵥ atomBlend (atomVec family) probe
        - ∑ slot, shift slot * probe slot ^ 2 := by
  classical
  rw [Matrix.sub_mulVec, dotProduct_sub, quadratic_eq_atomBlend_energy hsplit probe]
  congr 1
  rw [dotProduct]
  refine Finset.sum_congr rfl fun slot _ => ?_
  rw [Matrix.mulVec_diagonal]; ring

/-! ## Layer 3 — the escape law -/

/-- **THE ESCAPE LAW.**  If the scales total less than the square norm of
a probe, then some atom reads more energy than its own scale. -/
theorem exists_escape_atom {family : Fin rank → (Fin slotCount → ℝ)}
    (hnorm : ∀ index, family index ⬝ᵥ family index = 1)
    (horth : ∀ indexOne indexTwo, indexOne ≠ indexTwo →
      family indexOne ⬝ᵥ family indexTwo = 0)
    {scale : Fin slotCount → ℝ} {probe : Fin rank → ℝ}
    (hlt : (∑ slot, scale slot) < probe ⬝ᵥ probe) :
    ∃ slot, scale slot < (atomVec family slot ⬝ᵥ probe) ^ 2 := by
  classical
  by_contra hnone
  have hbound : ∀ slot, (atomVec family slot ⬝ᵥ probe) ^ 2 ≤ scale slot :=
    fun slot => not_lt.mp fun hlt => hnone ⟨slot, hlt⟩
  have hsum : (∑ slot, (atomVec family slot ⬝ᵥ probe) ^ 2) ≤ ∑ slot, scale slot :=
    Finset.sum_le_sum fun slot _ => hbound slot
  rw [atom_frame_energy hnorm horth probe] at hsum
  exact absurd hsum (not_le.mpr hlt)

/-- **THE SHARP ESCAPE RATIO.**  Some atom beats its scale by the
reciprocal of the scale total: the escape is quantitative and its
constant is exact. -/
theorem exists_escape_atom_ratio {family : Fin rank → (Fin slotCount → ℝ)}
    (hnorm : ∀ index, family index ⬝ᵥ family index = 1)
    (horth : ∀ indexOne indexTwo, indexOne ≠ indexTwo →
      family indexOne ⬝ᵥ family indexTwo = 0)
    {scale : Fin slotCount → ℝ} {probe : Fin rank → ℝ} {total : ℝ}
    (htotal : (∑ slot, scale slot) = total) (hpos : 0 < probe ⬝ᵥ probe) :
    ∃ slot, scale slot * (probe ⬝ᵥ probe)
      ≤ total * (atomVec family slot ⬝ᵥ probe) ^ 2 := by
  classical
  by_contra hnone
  have hbound : ∀ slot, total * (atomVec family slot ⬝ᵥ probe) ^ 2
      < scale slot * (probe ⬝ᵥ probe) :=
    fun slot => not_le.mp fun hle => hnone ⟨slot, hle⟩
  have hnonempty : (Finset.univ : Finset (Fin slotCount)).Nonempty := by
    rcases (Finset.univ : Finset (Fin slotCount)).eq_empty_or_nonempty with hempty | hne
    · exfalso
      have hzero : (∑ slot : Fin slotCount, (atomVec family slot ⬝ᵥ probe) ^ 2) = 0 := by
        rw [hempty, Finset.sum_empty]
      rw [atom_frame_energy hnorm horth probe] at hzero
      exact absurd hzero (ne_of_gt hpos)
    · exact hne
  have hsum : (∑ slot, total * (atomVec family slot ⬝ᵥ probe) ^ 2)
      < ∑ slot, scale slot * (probe ⬝ᵥ probe) :=
    Finset.sum_lt_sum_of_nonempty hnonempty fun slot _ => hbound slot
  rw [← Finset.mul_sum, atom_frame_energy hnorm horth probe, ← Finset.sum_mul,
    htotal] at hsum
  exact absurd hsum (lt_irrefl _)

/-! ## Layer 4 — the confinement at a read block -/

variable {chart : Matrix (Fin slotCount) (Fin slotCount) ℝ}
variable {family : Fin rank → (Fin slotCount → ℝ)}

/-- The blend energy of a read vector is its shifted square sum. -/
theorem block_blend_energy_eq
    (hsplit : chart = ∑ index, Matrix.vecMulVec (family index) (family index))
    {car : Finset (Fin slotCount)} {probe shift : Fin slotCount → ℝ}
    (hsupp : ∀ slot ∉ car, probe slot = 0)
    (hread : ∀ slot ∈ car, (chart *ᵥ probe) slot = shift slot * probe slot) :
    atomBlend (atomVec family) probe ⬝ᵥ atomBlend (atomVec family) probe
      = ∑ slot ∈ car, shift slot * probe slot ^ 2 := by
  classical
  rw [← quadratic_eq_atomBlend_energy hsplit probe, dotProduct]
  have hrestrict : (∑ slot, probe slot * (chart *ᵥ probe) slot)
      = ∑ slot ∈ car, probe slot * (chart *ᵥ probe) slot := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun slot _ hnot => ?_
    rw [hsupp slot hnot, zero_mul]
  rw [hrestrict]
  refine Finset.sum_congr rfl fun slot hslot => ?_
  rw [hread slot hslot]; ring

/-- The blend of a live read vector is alive: at strictly positive
shifts the blend energy is strictly positive. -/
theorem block_blend_energy_pos
    (hsplit : chart = ∑ index, Matrix.vecMulVec (family index) (family index))
    {car : Finset (Fin slotCount)} {probe shift : Fin slotCount → ℝ}
    (hsupp : ∀ slot ∉ car, probe slot = 0)
    (hread : ∀ slot ∈ car, (chart *ᵥ probe) slot = shift slot * probe slot)
    (hshift : ∀ slot ∈ car, 0 < shift slot) (hnz : probe ≠ 0) :
    0 < atomBlend (atomVec family) probe ⬝ᵥ atomBlend (atomVec family) probe := by
  classical
  obtain ⟨liveSlot, hlive⟩ : ∃ slot, probe slot ≠ 0 := by
    by_contra hnone
    exact hnz (funext fun slot => not_not.mp fun hne => hnone ⟨slot, hne⟩)
  have hmem : liveSlot ∈ car := by
    by_contra hnot
    exact hlive (hsupp liveSlot hnot)
  rw [block_blend_energy_eq hsplit hsupp hread]
  refine Finset.sum_pos' (fun slot hslot => ?_) ⟨liveSlot, hmem, ?_⟩
  · exact mul_nonneg (hshift slot hslot).le (sq_nonneg _)
  · exact mul_pos (hshift liveSlot hmem) (pow_pos (abs_pos.mpr hlive) 2 |>.trans_le
      (le_of_eq (by rw [sq_abs])))

/-- **THE CONFINEMENT.**  At an atom OF the read block the atom energy of
the blend never exceeds the shifted weight times the blend energy. -/
theorem block_atom_energy_le
    (hsplit : chart = ∑ index, Matrix.vecMulVec (family index) (family index))
    {car : Finset (Fin slotCount)} {probe shift : Fin slotCount → ℝ}
    (hsupp : ∀ slot ∉ car, probe slot = 0)
    (hread : ∀ slot ∈ car, (chart *ᵥ probe) slot = shift slot * probe slot)
    (hshift : ∀ slot ∈ car, 0 ≤ shift slot)
    {blockSlot : Fin slotCount} (hmem : blockSlot ∈ car) :
    (atomVec family blockSlot ⬝ᵥ atomBlend (atomVec family) probe) ^ 2
      ≤ shift blockSlot
        * (atomBlend (atomVec family) probe ⬝ᵥ atomBlend (atomVec family) probe) := by
  classical
  have hentry : atomVec family blockSlot ⬝ᵥ atomBlend (atomVec family) probe
      = shift blockSlot * probe blockSlot := by
    rw [← mulVec_eq_atomVec_dot_atomBlend hsplit probe blockSlot, hread blockSlot hmem]
  have hterm : shift blockSlot * probe blockSlot ^ 2
      ≤ ∑ slot ∈ car, shift slot * probe slot ^ 2 :=
    Finset.single_le_sum (f := fun slot => shift slot * probe slot ^ 2)
      (fun slot hslot => mul_nonneg (hshift slot hslot) (sq_nonneg _)) hmem
  rw [hentry, block_blend_energy_eq hsplit hsupp hread, mul_pow]
  calc shift blockSlot ^ 2 * probe blockSlot ^ 2
      = shift blockSlot * (shift blockSlot * probe blockSlot ^ 2) := by ring
    _ ≤ shift blockSlot * ∑ slot ∈ car, shift slot * probe slot ^ 2 :=
        mul_le_mul_of_nonneg_left hterm (hshift blockSlot hmem)

/-- The carrier share of the frame law at a read block: the atom energy
ON the block is capped by the largest shifted weight of the block. -/
theorem block_carrier_energy_le
    (hsplit : chart = ∑ index, Matrix.vecMulVec (family index) (family index))
    {car : Finset (Fin slotCount)} {probe shift : Fin slotCount → ℝ} {cap : ℝ}
    (hsupp : ∀ slot ∉ car, probe slot = 0)
    (hread : ∀ slot ∈ car, (chart *ᵥ probe) slot = shift slot * probe slot)
    (hshift : ∀ slot ∈ car, 0 ≤ shift slot) (hcap : ∀ slot ∈ car, shift slot ≤ cap) :
    (∑ slot ∈ car, (atomVec family slot ⬝ᵥ atomBlend (atomVec family) probe) ^ 2)
      ≤ cap * (atomBlend (atomVec family) probe ⬝ᵥ atomBlend (atomVec family) probe) := by
  classical
  set blend := atomBlend (atomVec family) probe with hblend
  have hentry : ∀ slot ∈ car, (atomVec family slot ⬝ᵥ blend) ^ 2
      = shift slot * (shift slot * probe slot ^ 2) := by
    intro slot hslot
    rw [hblend, ← mulVec_eq_atomVec_dot_atomBlend hsplit probe slot, hread slot hslot]
    ring
  rw [Finset.sum_congr rfl hentry]
  calc (∑ slot ∈ car, shift slot * (shift slot * probe slot ^ 2))
      ≤ ∑ slot ∈ car, cap * (shift slot * probe slot ^ 2) :=
        Finset.sum_le_sum fun slot hslot =>
          mul_le_mul_of_nonneg_right (hcap slot hslot)
            (mul_nonneg (hshift slot hslot) (sq_nonneg _))
    _ = cap * ∑ slot ∈ car, shift slot * probe slot ^ 2 := by rw [Finset.mul_sum]
    _ = cap * (blend ⬝ᵥ blend) := by
        rw [hblend, block_blend_energy_eq hsplit hsupp hread]

/-- **THE LEAK FLOOR.**  The atom energy of a block blend that sits OFF
the block carries all but the largest shifted weight of the block. -/
theorem block_leak_energy_ge
    (hsplit : chart = ∑ index, Matrix.vecMulVec (family index) (family index))
    (hnorm : ∀ index, family index ⬝ᵥ family index = 1)
    (horth : ∀ indexOne indexTwo, indexOne ≠ indexTwo →
      family indexOne ⬝ᵥ family indexTwo = 0)
    {car : Finset (Fin slotCount)} {probe shift : Fin slotCount → ℝ} {cap : ℝ}
    (hsupp : ∀ slot ∉ car, probe slot = 0)
    (hread : ∀ slot ∈ car, (chart *ᵥ probe) slot = shift slot * probe slot)
    (hshift : ∀ slot ∈ car, 0 ≤ shift slot) (hcap : ∀ slot ∈ car, shift slot ≤ cap) :
    (1 - cap) * (atomBlend (atomVec family) probe ⬝ᵥ atomBlend (atomVec family) probe)
      ≤ ∑ slot ∈ carᶜ,
          (atomVec family slot ⬝ᵥ atomBlend (atomVec family) probe) ^ 2 := by
  have hsplitEnergy := atom_frame_split hnorm horth car
    (atomBlend (atomVec family) probe)
  have hcarrier := block_carrier_energy_le hsplit hsupp hread hshift hcap
  nlinarith [hsplitEnergy, hcarrier]

/-- **THE OUTSIDE ESCAPE.**  At a read block whose shifted weights are
positive and total below one, the escaping atom never sits in the block:
some atom OFF the block reads strongly against the blend. -/
theorem exists_escape_outside_block
    (hsplit : chart = ∑ index, Matrix.vecMulVec (family index) (family index))
    (hnorm : ∀ index, family index ⬝ᵥ family index = 1)
    (horth : ∀ indexOne indexTwo, indexOne ≠ indexTwo →
      family indexOne ⬝ᵥ family indexTwo = 0)
    {car : Finset (Fin slotCount)} {probe shift : Fin slotCount → ℝ} {total : ℝ}
    (hsupp : ∀ slot ∉ car, probe slot = 0)
    (hread : ∀ slot ∈ car, (chart *ᵥ probe) slot = shift slot * probe slot)
    (hshift : ∀ slot, 0 < shift slot) (htotal : (∑ slot, shift slot) = total)
    (hsmall : total < 1) (hnz : probe ≠ 0) :
    ∃ escapeSlot, escapeSlot ∉ car
      ∧ shift escapeSlot
          * (atomBlend (atomVec family) probe ⬝ᵥ atomBlend (atomVec family) probe)
        ≤ total * (atomVec family escapeSlot ⬝ᵥ atomBlend (atomVec family) probe) ^ 2 := by
  classical
  set blend := atomBlend (atomVec family) probe with hblend
  have henergy : 0 < blend ⬝ᵥ blend :=
    block_blend_energy_pos hsplit hsupp hread (fun slot _ => hshift slot) hnz
  obtain ⟨escapeSlot, hescape⟩ :=
    exists_escape_atom_ratio (family := family) hnorm horth htotal henergy
  refine ⟨escapeSlot, ?_, hescape⟩
  intro hmem
  have hconfine := block_atom_energy_le (family := family) hsplit hsupp hread
    (fun slot _ => (hshift slot).le) hmem
  have hshiftPos : 0 < shift escapeSlot * (blend ⬝ᵥ blend) :=
    mul_pos (hshift escapeSlot) henergy
  have hchain : shift escapeSlot * (blend ⬝ᵥ blend)
      ≤ total * (shift escapeSlot * (blend ⬝ᵥ blend)) := by
    refine hescape.trans ?_
    have htotalPos : 0 ≤ total := by
      rw [← htotal]
      exact Finset.sum_nonneg fun slot _ => (hshift slot).le
    exact mul_le_mul_of_nonneg_left hconfine htotalPos
  nlinarith [hchain, hshiftPos, hsmall]

/-! ## Layer 5 — the atom system of a crux -/

/-- **THE ATOM SYSTEM OF A CRUX.**  The chart of a `(6,3)` crux carries
six atom vectors in three dimensions that form a tight frame, whose
blend identity prices the chart form, and whose shifted weights are the
scales. -/
theorem SixThreeCrux.exists_atom_system (crux : SixThreeCrux) :
    ∃ atom : Fin 6 → (Fin 3 → ℝ),
      (∀ probe direction : Fin 3 → ℝ,
        (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
      ∧ (∀ probe : Fin 6 → ℝ,
          probe ⬝ᵥ ((chartPointOfDesign crux.design).chart *ᵥ probe)
            = atomBlend atom probe ⬝ᵥ atomBlend atom probe) := by
  classical
  obtain ⟨family, hnorm, horth, hsplit⟩ :=
    exists_orthonormal_family_of_trace 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).isSymmetric
      (chartPointOfDesign crux.design).isIdempotent
      (chartPointOfDesign crux.design).hasTraceRank
  exact ⟨atomVec family, atom_frame_law hnorm horth,
    fun probe => quadratic_eq_atomBlend_energy hsplit probe⟩

/-! ## Layer 6 — the residue -/

/-- **THE ATOM TRIPLE CEILING.**  Six vectors in three dimensions that
form a tight frame, together with six strictly positive scales of total
less than one, carry a triple of atoms whose shifted form is strictly
positive on every nonzero vector supported there.

The statement carries no crux, no chart, no frame, no stationarity and
no combinatorics.  It is the design-side residue of the whole rank-six
wall, and the design sweep of this session confirms it on the regular
stratum with a wide margin. -/
def AtomTripleCeilingClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
          (∑ slot, scale slot * probe slot ^ 2)
            < atomBlend atom probe ⬝ᵥ atomBlend atom probe

/-! ## Layer 7 — the discharge -/

/-- A vector supported on a carrier sums by its ordered embedding. -/
theorem sum_eq_sum_orderEmbOfFin {car : Finset (Fin 6)} (hcard : car.card = 3)
    (value : Fin 6 → ℝ) (hvanish : ∀ slot ∉ car, value slot = 0) :
    (∑ slot, value slot) = ∑ index : Fin 3, value (car.orderEmbOfFin hcard index) := by
  classical
  have hrestrict : (∑ slot, value slot) = ∑ slot ∈ car, value slot :=
    (Finset.sum_subset (Finset.subset_univ _) fun slot _ hnot => hvanish slot hnot).symm
  have hmap : (∑ slot ∈ car, value slot)
      = ∑ index : Fin 3, value (car.orderEmbOfFin hcard index) := by
    have hsum := Finset.sum_map (Finset.univ : Finset (Fin 3))
      (car.orderEmbOfFin hcard).toEmbedding value
    rw [Finset.map_orderEmbOfFin_univ car hcard] at hsum
    exact hsum
  rw [hrestrict, hmap]

/-- The lift of a three-dimensional direction to the ambient vector
supported on a carrier. -/
noncomputable def carrierLift {car : Finset (Fin 6)} (hcard : car.card = 3)
    (direction : Fin 3 → ℝ) : Fin 6 → ℝ :=
  fun slot => ∑ index : Fin 3,
    if car.orderEmbOfFin hcard index = slot then direction index else 0

theorem carrierLift_vanish {car : Finset (Fin 6)} (hcard : car.card = 3)
    (direction : Fin 3 → ℝ) {slot : Fin 6} (hnot : slot ∉ car) :
    carrierLift hcard direction slot = 0 := by
  classical
  refine Finset.sum_eq_zero fun index _ => ?_
  rw [if_neg]
  intro heq
  exact hnot (heq ▸ car.orderEmbOfFin_mem hcard index)

theorem carrierLift_apply {car : Finset (Fin 6)} (hcard : car.card = 3)
    (direction : Fin 3 → ℝ) (index : Fin 3) :
    carrierLift hcard direction (car.orderEmbOfFin hcard index) = direction index := by
  classical
  rw [carrierLift, Finset.sum_eq_single index
    (fun other _ hne => if_neg fun heq => hne ((car.orderEmbOfFin hcard).injective heq))
    (fun hnot => absurd (Finset.mem_univ _) hnot), if_pos rfl]

/-- **THE CEILING IN ATOM FORM.**  At EVERY triple of atoms the chart
ceiling supplies a nonzero test vector supported there whose blend energy
is at most its shifted square sum.  The chart value is the maximum of the
block values, thus no triple escapes, and the witness is the least
eigenvector of the compressed gap block.  This is the design-side reading
of `Gtz.hasNoDominatingTriple` sharpened to the chart value, and it is the
law that every frame layer of the campaign discards. -/
theorem SixThreeCrux.exists_ceiling_witness (crux : SixThreeCrux)
    {family : Fin 3 → (Fin 6 → ℝ)}
    (hsplit : (chartPointOfDesign crux.design).chart
      = ∑ index, Matrix.vecMulVec (family index) (family index))
    {car : Finset (Fin 6)} (hcard : car.card = 3) :
    ∃ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) ∧ probe ≠ 0
      ∧ atomBlend (atomVec family) probe ⬝ᵥ atomBlend (atomVec family) probe
        ≤ ∑ slot, (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight slot) * probe slot ^ 2 := by
  classical
  set point := chartPointOfDesign crux.design with hpoint
  set value := chartObjective point with hvalue
  set gapBlock := (chartPointGap point).submatrix (car.orderEmbOfFin hcard)
    (car.orderEmbOfFin hcard) with hgapBlock
  have hgapSymm : (chartPointGap point)ᵀ = chartPointGap point := chartPointGap_transpose point
  have hblockHermitian : gapBlock.IsHermitian := by
    rw [hgapBlock, Matrix.IsHermitian, Matrix.conjTranspose]
    ext rowIndex colIndex
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      RCLike.star_def, starRingEnd_apply, star_trivial]
    exact congrFun (congrFun hgapSymm _) _
  obtain ⟨eigenVec, hunit, heigen⟩ :=
    exists_unit_eigenvector_lambdaMinMat gapBlock hblockHermitian
  have hceiling : lambdaMinMat gapBlock ≤ value := by
    rw [hgapBlock, hvalue, ← chartGapRaw_chartConfig point]
    exact lambdaMinMat_gap_submatrix_le_chartObjective point hcard
  set lift := carrierLift hcard eigenVec with hlift
  have hliftVanish : ∀ slot ∉ car, lift slot = 0 :=
    fun slot hnot => carrierLift_vanish hcard eigenVec hnot
  have hliftNe : lift ≠ 0 := by
    intro hzero
    have hone : (1 : ℝ) = 0 := by
      rw [← hunit, dotProduct]
      refine Finset.sum_eq_zero fun index _ => ?_
      have hentry : eigenVec index = lift (car.orderEmbOfFin hcard index) := by
        rw [hlift, carrierLift_apply hcard eigenVec index]
      rw [hentry, hzero, Pi.zero_apply, mul_zero]
    exact absurd hone one_ne_zero
  have hliftNorm : lift ⬝ᵥ lift = 1 := by
    rw [dotProduct, sum_eq_sum_orderEmbOfFin hcard (fun slot => lift slot * lift slot)
      (fun slot hnot => by rw [hliftVanish slot hnot, mul_zero])]
    rw [← hunit, dotProduct]
    exact Finset.sum_congr rfl fun index _ => by
      rw [hlift, carrierLift_apply hcard eigenVec index]
  have hliftGap : lift ⬝ᵥ (chartPointGap point *ᵥ lift)
      = eigenVec ⬝ᵥ (gapBlock *ᵥ eigenVec) := by
    rw [dotProduct, sum_eq_sum_orderEmbOfFin hcard
      (fun slot => lift slot * (chartPointGap point *ᵥ lift) slot)
      (fun slot hnot => by rw [hliftVanish slot hnot, zero_mul])]
    rw [dotProduct]
    refine Finset.sum_congr rfl fun rowIndex _ => ?_
    rw [hlift, carrierLift_apply hcard eigenVec rowIndex]
    congr 1
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
      sum_eq_sum_orderEmbOfFin hcard
        (fun slot => chartPointGap point (car.orderEmbOfFin hcard rowIndex) slot * lift slot)
        (fun slot hnot => by rw [hliftVanish slot hnot, mul_zero])]
    refine Finset.sum_congr rfl fun colIndex _ => ?_
    rw [hgapBlock, Matrix.submatrix_apply, hlift,
      carrierLift_apply hcard eigenVec colIndex]
  have hrayleigh : eigenVec ⬝ᵥ (gapBlock *ᵥ eigenVec) = lambdaMinMat gapBlock := by
    rw [dotProduct]
    have hcell : ∀ index : Fin 3,
        eigenVec index * (gapBlock *ᵥ eigenVec) index
          = lambdaMinMat gapBlock * (eigenVec index * eigenVec index) := by
      intro index
      rw [heigen index]; ring
    rw [Finset.sum_congr rfl (fun index _ => hcell index), ← Finset.mul_sum, ← dotProduct,
      hunit, mul_one]
  have hgapForm : lift ⬝ᵥ (chartPointGap point *ᵥ lift)
      = atomBlend (atomVec family) lift ⬝ᵥ atomBlend (atomVec family) lift
        - ∑ slot, point.weight slot * lift slot ^ 2 := by
    rw [chartPointGap]
    exact shifted_quadratic_eq hsplit point.weight lift
  have hshiftForm : (∑ slot, (value + point.weight slot) * lift slot ^ 2)
      = value * (lift ⬝ᵥ lift) + ∑ slot, point.weight slot * lift slot ^ 2 := by
    rw [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun slot _ => by ring
  refine ⟨lift, hliftVanish, hliftNe, ?_⟩
  rw [hshiftForm, hliftNorm, mul_one]
  rw [hliftGap, hrayleigh] at hgapForm
  linarith [hceiling, hgapForm]

/-- **THE CRUX KILL FROM THE RESIDUE.**  At an interior datum the atom
triple ceiling refutes the crux: the residue supplies a strictly
dominating triple, and the ceiling witness of that triple forbids it. -/
theorem SixThreeCrux.false_of_atomTripleCeiling (crux : SixThreeCrux)
    (hresidue : AtomTripleCeilingClosed)
    (hinterior : ∀ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    False := by
  classical
  set point := chartPointOfDesign crux.design with hpoint
  set value := chartObjective point with hvalue
  obtain ⟨family, hnorm, horth, hsplit⟩ :=
    exists_orthonormal_family_of_trace 3 point.chart point.isSymmetric
      point.isIdempotent point.hasTraceRank
  have hshiftSum : (∑ atomIndex : Fin 6, (value + point.weight atomIndex))
      = 6 * value + 1 := by
    rw [Finset.sum_add_distrib, point.weight_sum_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hnegValue : value < 0 := crux.hasNegativeChartValue
  have hshiftSmall : (∑ atomIndex : Fin 6, (value + point.weight atomIndex)) < 1 := by
    rw [hshiftSum]; linarith
  obtain ⟨car, hcard, hdominates⟩ :=
    hresidue (atomVec family) (fun atomIndex => value + point.weight atomIndex)
      hinterior hshiftSmall (atom_frame_law hnorm horth)
  obtain ⟨probe, hvanish, hne, hwitness⟩ := crux.exists_ceiling_witness hsplit hcard
  exact absurd (hdominates probe hvanish hne) (not_lt.mpr hwitness)

/-- **THE RANK-SIX KILL.**  A rank-six frame carries interiority as a
theorem, thus the atom triple ceiling refutes it outright. -/
theorem RankSixFrame.false_of_atomTripleCeiling {crux : SixThreeCrux}
    (frame : RankSixFrame crux) (hresidue : AtomTripleCeilingClosed) : False :=
  crux.false_of_atomTripleCeiling hresidue frame.shifted_weight_pos

/-- **THE OUTSIDE ESCAPE AT A RANK-SIX FRAME.**  Every basis column of a
rank-six frame reads strongly at an atom OUTSIDE its own block: the
escaping atom of the blend is never a block atom. -/
theorem RankSixFrame.exists_escape_outside_block {crux : SixThreeCrux}
    (frame : RankSixFrame crux) (columnIndex : Fin 6)
    (family : Fin 3 → (Fin 6 → ℝ))
    (hnorm : ∀ index, family index ⬝ᵥ family index = 1)
    (horth : ∀ indexOne indexTwo, indexOne ≠ indexTwo →
      family indexOne ⬝ᵥ family indexTwo = 0)
    (hsplit : (chartPointOfDesign crux.design).chart
      = ∑ index, Matrix.vecMulVec (family index) (family index)) :
    ∃ escapeSlot : Fin 6,
      escapeSlot ∉ frame.activeSubset (frame.basisLabel columnIndex)
      ∧ (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight escapeSlot)
          * (atomBlend (atomVec family) (frame.tightDir (frame.basisLabel columnIndex))
              ⬝ᵥ atomBlend (atomVec family) (frame.tightDir (frame.basisLabel columnIndex)))
        ≤ (6 * chartObjective (chartPointOfDesign crux.design) + 1)
          * (atomVec family escapeSlot
              ⬝ᵥ atomBlend (atomVec family)
                  (frame.tightDir (frame.basisLabel columnIndex))) ^ 2 := by
  classical
  set point := chartPointOfDesign crux.design with hpoint
  set value := chartObjective point with hvalue
  set direction := frame.tightDir (frame.basisLabel columnIndex) with hdirection
  have hmemAll := frame.hmemAll columnIndex
  have hsupp : ∀ slot ∉ frame.activeSubset (frame.basisLabel columnIndex),
      direction slot = 0 :=
    fun slot hnot => frame.hdata.tightDir_support _ hmemAll slot hnot
  have hread : ∀ slot ∈ frame.activeSubset (frame.basisLabel columnIndex),
      (point.chart *ᵥ direction) slot = (value + point.weight slot) * direction slot := by
    intro slot hslot
    have htight := frame.hdata.tightDir_isTight _ hmemAll slot hslot
    rw [chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply,
      Matrix.mulVec_diagonal] at htight
    linarith [htight]
  have hnz : direction ≠ 0 := by
    intro hzero
    have hunit := frame.hdata.tightDir_unit _ hmemAll
    rw [← hdirection, hzero] at hunit
    simp only [dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hunit
    exact absurd hunit.symm one_ne_zero
  exact _root_.Gtz.exists_escape_outside_block hsplit hnorm horth hsupp hread
    frame.shifted_weight_pos frame.shifted_weight_sum
    (by have := crux.hasNegativeChartValue; rw [← hvalue] at this; linarith) hnz

/-! ## Layer 8 — the rung -/

/-- **THE RANK-SIX DIRECT KILL FROM THE RESIDUE.** -/
theorem rankSixOuterKilled_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankSixOuterKilled :=
  fun _ data => data.frame.false_of_atomTripleCeiling hresidue

/-- **THE RANK-SIX DISCHARGE FROM ONE DESIGN-SIDE RESIDUE.**  The
support-two closure of the third rung follows from the atom triple
ceiling alone: the circuit residue, the regular residue and the thin
residue are all consumed. -/
theorem rankSixSupportTwoClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankSixSupportTwoClosed :=
  rankSixSupportTwoClosed_of_outer_killed
    (rankSixOuterKilled_of_atomTripleCeiling hresidue)

/-- The circuit residue of the outer-zero lattice. -/
theorem rankSixOuterCircuitClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankSixOuterCircuitClosed := by
  intro _ data
  intros
  exact data.frame.false_of_atomTripleCeiling hresidue

/-- The off-pair half of the narrowed circuit residue. -/
theorem rankSixOuterOffPairCircuitClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankSixOuterOffPairCircuitClosed := by
  intro _ data
  intros
  exact data.frame.false_of_atomTripleCeiling hresidue

/-- The rank-one half of the narrowed circuit residue: the rank-one gap
block of the pin calculus is consumed together with the rest. -/
theorem rankSixOuterRankOneCircuitClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankSixOuterRankOneCircuitClosed := by
  intro _ data
  intros
  exact data.frame.false_of_atomTripleCeiling hresidue

/-- The regular residue of the outer-zero lattice: the whole
all-degree-three stratum. -/
theorem rankSixOuterRegularClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankSixOuterRegularClosed := by
  intro _ data
  intros
  exact data.frame.false_of_atomTripleCeiling hresidue

/-- The thin residue of the outer-zero lattice. -/
theorem rankSixOuterThinClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankSixOuterThinClosed := by
  intro _ data
  intros
  exact data.frame.false_of_atomTripleCeiling hresidue

/-- The low-profile residue of the column-Gram fold. -/
theorem rankSixOuterLowProfileClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankSixOuterLowProfileClosed := by
  intro _ data
  intros
  exact data.frame.false_of_atomTripleCeiling hresidue

/-- **THE WHOLE `(6,3)` STATEMENT FROM THE RESIDUE AND INTERIORITY.**
The atom triple ceiling together with interiority at every crux gives
weighted GTZ at `(6,3)`. -/
theorem gtzWeighted_six_three_of_atomTripleCeiling_of_interior
    (hresidue : AtomTripleCeilingClosed)
    (hinterior : ∀ crux : SixThreeCrux, ∀ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_isEmpty_sixThreeCrux
    ⟨fun crux => crux.false_of_atomTripleCeiling hresidue (hinterior crux)⟩

/-! ## Layer 9 — the margin form and the lower ranks -/

/-- **THE MARGIN FORM OF THE RESIDUE.**  The same statement with a
UNIFORM margin instead of a pointwise strict inequality.  The design
sweep measures exactly this number, thus the margin form is the residue
a numeric certificate produces. -/
def AtomTripleCeilingMarginClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ (car : Finset (Fin 6)) (margin : ℝ), car.card = 3 ∧ 0 < margin
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2) + margin * (probe ⬝ᵥ probe)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe

/-- The margin form implies the pointwise form: a nonzero vector has
positive square norm. -/
theorem atomTripleCeilingClosed_of_margin
    (hmargin : AtomTripleCeilingMarginClosed) : AtomTripleCeilingClosed := by
  classical
  intro atom scale hpos hsmall hframe
  obtain ⟨car, margin, hcard, hmarginPos, hbound⟩ := hmargin atom scale hpos hsmall hframe
  refine ⟨car, hcard, fun probe hvanish hne => ?_⟩
  have hnormPos : 0 < probe ⬝ᵥ probe := by
    obtain ⟨liveSlot, hlive⟩ : ∃ slot, probe slot ≠ 0 := by
      by_contra hnone
      exact hne (funext fun slot => not_not.mp fun hlt => hnone ⟨slot, hlt⟩)
    rw [dotProduct]
    exact Finset.sum_pos' (fun slot _ => mul_self_nonneg _)
      ⟨liveSlot, Finset.mem_univ _, mul_self_pos.mpr hlive⟩
  have := hbound probe hvanish
  nlinarith [this, mul_pos hmarginPos hnormPos]

/-- **THE RANK-FIVE KILL.**  The atom triple ceiling refutes a rank-five
frame whenever the shifted weights of that frame are interior. -/
theorem RankFiveFrame.false_of_atomTripleCeiling_of_interior {crux : SixThreeCrux}
    (_frame : RankFiveFrame crux) (hresidue : AtomTripleCeilingClosed)
    (hinterior : ∀ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    False :=
  crux.false_of_atomTripleCeiling hresidue hinterior

/-- **THE RANK-FOUR KILL.**  The same at rank four. -/
theorem RankFourFrame.false_of_atomTripleCeiling_of_interior {crux : SixThreeCrux}
    (_frame : RankFourFrame crux) (hresidue : AtomTripleCeilingClosed)
    (hinterior : ∀ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    False :=
  crux.false_of_atomTripleCeiling hresidue hinterior

/-- The rank-five direct kill from the residue and interiority. -/
theorem rankFiveOuterKilled_of_atomTripleCeiling_of_interior
    (hresidue : AtomTripleCeilingClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (atomIndex : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFiveOuterKilled :=
  fun crux _ => crux.false_of_atomTripleCeiling hresidue (hinterior crux)

/-- The rank-five support-two closure from the residue and interiority. -/
theorem rankFiveSupportTwoClosed_of_atomTripleCeiling_of_interior
    (hresidue : AtomTripleCeilingClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (atomIndex : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFiveSupportTwoClosed :=
  rankFiveSupportTwoClosed_of_outer_killed
    (rankFiveOuterKilled_of_atomTripleCeiling_of_interior hresidue hinterior)

/-- The rank-four direct kill from the residue and interiority. -/
theorem rankFourOuterKilled_of_atomTripleCeiling_of_interior
    (hresidue : AtomTripleCeilingClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (atomIndex : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFourOuterKilled :=
  fun crux _ => crux.false_of_atomTripleCeiling hresidue (hinterior crux)

/-- The rank-four support-two closure from the residue and interiority. -/
theorem rankFourSupportTwoClosed_of_atomTripleCeiling_of_interior
    (hresidue : AtomTripleCeilingClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (atomIndex : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFourSupportTwoClosed :=
  rankFourSupportTwoClosed_of_outer_killed
    (rankFourOuterKilled_of_atomTripleCeiling_of_interior hresidue hinterior)

end Gtz

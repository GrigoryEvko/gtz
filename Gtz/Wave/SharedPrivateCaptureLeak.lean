import Gtz.Wave.SharedPrivateReadIntertwiner
import Gtz.Wave.SharedPrivateCircuitGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The capture leak — the commutation, read atom by atom

The chart commutes with the multiplier assembly.  Every kill so far
consumed that commutation through a trace, and a trace of the whole
assembly hides the support.  This module reads the commutation at one
atom at a time, and the support enters.

The sandwich.  A symmetric idempotent that commutes with a form
sandwiches it: `P Xi P = P Xi`.  The left side splits over the active
family, because the assembly is a weighted sum of rank-one atoms, and
the diagonal of a sandwiched rank-one atom is the square of the
projected direction at that atom.  The right side is the forced
diagonal, one sixth of the shifted weight.

The leak law.  Split the active family at one atom into the labels
whose block holds the atom and the labels whose block misses it.  The
first family reads the shifted weight twice, thus it contributes the
square of the shifted weight over the size.  Thus the second family
carries the rest:

    (value + weight y) * (1 - value - weight y) / size
      = sum over the labels whose block misses y of
        the multiplier times the square of the projected direction at y.

Both sides are nonnegative.  The left side is strictly positive at an
interior window, because the shifted weight sum is less than one.  Thus
**some active label has a block that misses the atom, and its projected
direction does not vanish there**.  No frame, no basis, no Gram core:
the law holds at every chart stationary datum.

The slot form.  A shared-private datum with a diagonal Gram core writes
its assembly over the basis slots alone.  The leak law then runs over
the slots whose support misses the atom, and the missing-slot law
follows: **no atom sits in every basis support**.  At basis count six
this removes the whole multiplicity-six profile class from the deficit
residue.

The circuits.  A pair circuit writes a positive label as a combination
of two basis columns.  The two supports then differ inside one block of
three atoms, thus **the two supports share at least two atoms** — the
landed pair law shares only one.  And at every atom of the difference
the chart kills the other basis column.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomMatrix_sandwich_apply`,
  `Gtz.atomMatrix_sandwich_diagonal`,
  `Gtz.sum_atomMatrix_sandwich_apply`,
  `Gtz.sum_atomMatrix_sandwich_diagonal`,
  `Gtz.capture_apply_eq_sum` — the sandwiched rank-one calculus.
* `Gtz.projector_sandwich_eq_capture`,
  `Gtz.projector_capture_complement_eq_zero` — the commuting sandwich.
* `Gtz.capture_diagonal_sum_eq`,
  `Gtz.capture_diagonal_lt_one_of_negative_value` — **THE CAPTURE
  WINDOW.**
* `Gtz.capture_leak_identity` — **THE LEAK LAW**, at every chart
  stationary datum.
* `Gtz.capture_leak_pos_of_interior`,
  `Gtz.exists_offBlock_capture_of_interior` — **THE OFF-BLOCK
  WITNESS.**
* `Gtz.capture_cross_leak_identity` — **THE CROSS LEAK LAW**, the whole
  sandwich at one atom pair.
* `Gtz.capture_energy_eq`, `Gtz.offBlock_capture_energy` — the per-label
  capture energy and its leak form, with no commutation.
* `Gtz.gram_diagonal_conjugate_eq_sum_atomMatrix`,
  `Gtz.SharedPrivateData.assembly_eq_slot_sum` — the slot form of the
  assembly.
* `Gtz.SharedPrivateData.gramDiag_pos`,
  `Gtz.SharedPrivateData.slot_leak_identity`,
  `Gtz.SharedPrivateData.slot_leak_term_le`,
  `Gtz.SharedPrivateData.exists_offSupport_slot`,
  `Gtz.SharedPrivateData.exists_offSupport_capture_slot`,
  `Gtz.SharedPrivateData.multiplicity_lt_basisCount` — **THE
  MISSING-SLOT LAW.**
* `Gtz.SharedPrivateData.slot_mass_le_half`,
  `Gtz.SharedPrivateData.private_mass_eq`,
  `Gtz.SharedPrivateData.private_mass_ge` — the slot mass lattice.
* `Gtz.SharedPrivateData.pair_reconstruction`,
  `Gtz.SharedPrivateData.pairCircuit_mem_support_of_sdiff`,
  `Gtz.SharedPrivateData.pairCircuit_two_le_inter_card` — **THE PAIR
  CIRCUITS SHARE TWO ATOMS.**
* `Gtz.SharedPrivateData.pairCircuit_capture_eq_zero` — **THE PAIR
  CAPTURE KILL.**
* `Gtz.SharedPrivateDeficitSixLowMultiplicityClosed`,
  `Gtz.sharedPrivateDeficitSixInteriorClosed_of_lowMultiplicity` — the
  narrowed six residue.
* `Gtz.SharedPrivateCircuitPairSharedClosed`,
  `Gtz.sharedPrivateCircuitPairClosed_of_shared` — the narrowed pair
  residue.
* `Gtz.sharedPrivateKilled_of_leak_strata`,
  `Gtz.rankFourSharedPrivateClosed_of_leak_strata`,
  `Gtz.rankFiveSharedPrivateClosed_of_leak_strata`,
  `Gtz.rankSixSharedPrivateClosed_of_leak_strata` — the dispatch.

## Vacuity

The matrix statements are unconditional.  The datum statements
quantify over chart stationary data and over shared-private data, and
no shared-private datum exists if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the sandwiched rank-one diagonal -/

/-- **THE SANDWICHED RANK-ONE ATOM.**  A sandwiched rank-one atom is the
rank-one atom of the projected direction.  The left factor reads the
direction, the right factor reads it again through the symmetry. -/
theorem atomMatrix_sandwich_apply {size : ℕ}
    {proj : Matrix (Fin size) (Fin size) ℝ} (hsymm : projᵀ = proj)
    (vec : Fin size → ℝ) (rowAtom colAtom : Fin size) :
    (proj * atomMatrix vec * proj) rowAtom colAtom
      = (proj *ᵥ vec) rowAtom * (proj *ᵥ vec) colAtom := by
  have hleft : ∀ midAtom : Fin size,
      (proj * atomMatrix vec) rowAtom midAtom
        = (proj *ᵥ vec) rowAtom * vec midAtom := by
    intro midAtom
    rw [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun probeAtom _ => ?_
    rw [atomMatrix, Matrix.vecMulVec_apply]
    ring
  rw [Matrix.mul_apply]
  have hterm : ∀ midAtom : Fin size,
      (proj * atomMatrix vec) rowAtom midAtom * proj midAtom colAtom
        = (proj *ᵥ vec) rowAtom * (proj colAtom midAtom * vec midAtom) := by
    intro midAtom
    have hsym := congrFun (congrFun hsymm midAtom) colAtom
    rw [Matrix.transpose_apply] at hsym
    rw [hleft midAtom, hsym]
    ring
  rw [Finset.sum_congr rfl fun midAtom _ => hterm midAtom, ← Finset.mul_sum]
  rfl

/-- The diagonal of a sandwiched rank-one atom is the square of the
projected direction. -/
theorem atomMatrix_sandwich_diagonal {size : ℕ}
    {proj : Matrix (Fin size) (Fin size) ℝ} (hsymm : projᵀ = proj)
    (vec : Fin size → ℝ) (atomIndex : Fin size) :
    (proj * atomMatrix vec * proj) atomIndex atomIndex
      = ((proj *ᵥ vec) atomIndex) ^ 2 := by
  rw [atomMatrix_sandwich_apply hsymm, sq]

/-- **THE SANDWICHED ASSEMBLY.**  A sandwiched weighted sum of rank-one
atoms is the weighted sum of the rank-one atoms of the projected
directions. -/
theorem sum_atomMatrix_sandwich_apply {size : ℕ} {labelType : Type}
    {proj : Matrix (Fin size) (Fin size) ℝ} (hsymm : projᵀ = proj)
    (labelSet : Finset labelType) (coef : labelType → ℝ)
    (vec : labelType → (Fin size → ℝ)) (rowAtom colAtom : Fin size) :
    (proj * (∑ label ∈ labelSet, coef label • atomMatrix (vec label)) * proj)
        rowAtom colAtom
      = ∑ label ∈ labelSet,
          coef label * ((proj *ᵥ vec label) rowAtom
            * (proj *ᵥ vec label) colAtom) := by
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
    atomMatrix_sandwich_apply hsymm]

/-- The diagonal of a sandwiched weighted sum of rank-one atoms is the
weighted sum of the squares of the projected directions. -/
theorem sum_atomMatrix_sandwich_diagonal {size : ℕ} {labelType : Type}
    {proj : Matrix (Fin size) (Fin size) ℝ} (hsymm : projᵀ = proj)
    (labelSet : Finset labelType) (coef : labelType → ℝ)
    (vec : labelType → (Fin size → ℝ)) (atomIndex : Fin size) :
    (proj * (∑ label ∈ labelSet, coef label • atomMatrix (vec label)) * proj)
        atomIndex atomIndex
      = ∑ label ∈ labelSet,
          coef label * ((proj *ᵥ vec label) atomIndex) ^ 2 := by
  rw [sum_atomMatrix_sandwich_apply hsymm]
  exact Finset.sum_congr rfl fun label _ => by rw [sq]

/-- **THE CAPTURE ENTRY.**  The capture entry is the weighted sum of the
projected direction against the direction. -/
theorem capture_apply_eq_sum {size : ℕ} {labelType : Type}
    (proj : Matrix (Fin size) (Fin size) ℝ) (labelSet : Finset labelType)
    (coef : labelType → ℝ) (vec : labelType → (Fin size → ℝ))
    (rowAtom colAtom : Fin size) :
    (proj * ∑ label ∈ labelSet, coef label • atomMatrix (vec label))
        rowAtom colAtom
      = ∑ label ∈ labelSet,
          coef label * ((proj *ᵥ vec label) rowAtom * vec label colAtom) := by
  rw [Matrix.mul_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun midAtom _ => ?_)
  rw [atomMatrix, Matrix.vecMulVec_apply]
  ring

/-! ## Layer 2 — the commuting sandwich -/

/-- **THE SANDWICH.**  A symmetric idempotent that commutes with a form
sandwiches it. -/
theorem projector_sandwich_eq_capture {size : ℕ}
    {proj form : Matrix (Fin size) (Fin size) ℝ}
    (hidem : proj * proj = proj) (hcomm : proj * form = form * proj) :
    proj * form * proj = proj * form := by
  rw [hcomm, Matrix.mul_assoc, hidem]

/-- The capture annihilates the complement. -/
theorem projector_capture_complement_eq_zero {size : ℕ}
    {proj form : Matrix (Fin size) (Fin size) ℝ}
    (hidem : proj * proj = proj) (hcomm : proj * form = form * proj) :
    proj * form * (1 - proj) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, projector_sandwich_eq_capture hidem hcomm,
    sub_self]

/-! ## Layer 3 — the capture window -/

variable {size rank : ℕ} {activeIndex : Type}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}

/-- The shifted weights sum to the size times the value plus one. -/
theorem capture_diagonal_sum_eq
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir) :
    ∑ atomIndex : Fin size, (value + weight atomIndex)
      = (size : ℝ) * value + 1 := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hdata.weight_sum_one]

/-- **THE CAPTURE WINDOW.**  At a negative chart value every shifted
weight is strictly less than one: the shifted weights are nonnegative
and their total is less than one. -/
theorem capture_diagonal_lt_one_of_negative_value
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir) (hvalue : value < 0)
    (atomIndex : Fin size) : value + weight atomIndex < 1 := by
  classical
  have hnonneg : ∀ probe : Fin size, 0 ≤ value + weight probe := fun probe =>
    capture_diagonal_nonneg_of_isChartStationaryData hdata probe
  have hle : value + weight atomIndex
      ≤ ∑ probe : Fin size, (value + weight probe) :=
    Finset.single_le_sum (f := fun probe => value + weight probe)
      (fun probe _ => hnonneg probe) (Finset.mem_univ atomIndex)
  rw [capture_diagonal_sum_eq hdata] at hle
  have hsizePos : (0 : ℝ) < (size : ℝ) :=
    size_cast_pos_of_isChartStationaryData hdata
  have hneg : (size : ℝ) * value < 0 := mul_neg_of_pos_of_neg hsizePos hvalue
  linarith

/-! ## Layer 4 — the leak law -/

/-- The block family of an atom: the labels whose block holds it. -/
noncomputable def blockHolders (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin size)) (atomIndex : Fin size) :
    Finset activeIndex :=
  activeSet.filter fun label => atomIndex ∈ activeSubset label

/-- The off-block family of an atom: the labels whose block misses it. -/
noncomputable def blockMissers (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin size)) (atomIndex : Fin size) :
    Finset activeIndex :=
  activeSet.filter fun label => atomIndex ∉ activeSubset label

/-- The block family carries the whole assembly diagonal: the labels
that miss the atom vanish there. -/
theorem blockHolders_assembly_diagonal
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir) (atomIndex : Fin size) :
    ∑ label ∈ blockHolders activeSet activeSubset atomIndex,
        activeWeight label * tightDir label atomIndex ^ 2 = ((size : ℝ))⁻¹ := by
  have hfull := hdata.assembly_diagonal atomIndex
  rw [chartMultiplierAssembly_diagonal] at hfull
  rw [← hfull, blockHolders]
  refine Finset.sum_filter_of_ne fun label hmem hne => ?_
  by_contra hnot
  exact hne (by rw [hdata.tightDir_support label hmem atomIndex hnot,
    pow_two, mul_zero, mul_zero])

/-- **THE LEAK LAW.**  At every atom the labels whose block misses the
atom carry exactly the shifted-weight leak.  The proof reads the
commuting sandwich twice: once through the rank-one split, once
through the forced diagonal. -/
theorem capture_leak_identity
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir) (atomIndex : Fin size) :
    ∑ label ∈ blockMissers activeSet activeSubset atomIndex,
        activeWeight label
          * ((projection *ᵥ tightDir label) atomIndex) ^ 2
      = (value + weight atomIndex) * (1 - (value + weight atomIndex))
        * ((size : ℝ))⁻¹ := by
  set shifted : ℝ := value + weight atomIndex with hshiftedDef
  set assembly := chartMultiplierAssembly activeSet activeWeight tightDir
    with hassemblyDef
  -- the sandwich equals the capture, and the capture diagonal is forced
  have hsandwich : projection * assembly * projection = projection * assembly :=
    projector_sandwich_eq_capture hdata.isIdempotent hdata.assembly_commutes
  have hcapture : (projection * assembly) atomIndex atomIndex
      = shifted * ((size : ℝ))⁻¹ :=
    diagonal_projection_mul_multiplier_of_isChartStationaryData hdata atomIndex
  -- the sandwich diagonal splits over the active family
  have hsplit : (projection * assembly * projection) atomIndex atomIndex
      = ∑ label ∈ activeSet, activeWeight label
          * ((projection *ᵥ tightDir label) atomIndex) ^ 2 := by
    rw [hassemblyDef, chartMultiplierAssembly,
      sum_atomMatrix_sandwich_diagonal hdata.isSymmetric]
  -- the block family reads the shifted weight twice
  have hholders : ∑ label ∈ blockHolders activeSet activeSubset atomIndex,
      activeWeight label * ((projection *ᵥ tightDir label) atomIndex) ^ 2
      = shifted ^ 2 * ((size : ℝ))⁻¹ := by
    have hterm : ∀ label ∈ blockHolders activeSet activeSubset atomIndex,
        activeWeight label * ((projection *ᵥ tightDir label) atomIndex) ^ 2
          = shifted ^ 2 * (activeWeight label * tightDir label atomIndex ^ 2) := by
      intro label hmem
      rw [blockHolders, Finset.mem_filter] at hmem
      rw [projection_mulVec_tightDir_of_mem hdata hmem.1 hmem.2, ← hshiftedDef]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      blockHolders_assembly_diagonal hdata atomIndex]
  -- the two families partition the active family
  have hpartition : ∑ label ∈ activeSet, activeWeight label
        * ((projection *ᵥ tightDir label) atomIndex) ^ 2
      = (∑ label ∈ blockHolders activeSet activeSubset atomIndex,
          activeWeight label * ((projection *ᵥ tightDir label) atomIndex) ^ 2)
        + ∑ label ∈ blockMissers activeSet activeSubset atomIndex,
            activeWeight label
              * ((projection *ᵥ tightDir label) atomIndex) ^ 2 := by
    rw [blockHolders, blockMissers]
    exact (Finset.sum_filter_add_sum_filter_not activeSet
      (fun label => atomIndex ∈ activeSubset label) _).symm
  rw [hsandwich, hcapture] at hsplit
  rw [hpartition, hholders] at hsplit
  have hfinal : ∑ label ∈ blockMissers activeSet activeSubset atomIndex,
      activeWeight label * ((projection *ᵥ tightDir label) atomIndex) ^ 2
      = shifted * ((size : ℝ))⁻¹ - shifted ^ 2 * ((size : ℝ))⁻¹ := by
    linarith
  rw [hfinal]
  ring

/-- **THE LEAK FLOOR.**  At an interior window with a negative value the
leak is strictly positive. -/
theorem capture_leak_pos_of_interior
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir) (hvalue : value < 0)
    {atomIndex : Fin size} (hinterior : 0 < value + weight atomIndex) :
    0 < ∑ label ∈ blockMissers activeSet activeSubset atomIndex,
        activeWeight label
          * ((projection *ᵥ tightDir label) atomIndex) ^ 2 := by
  have hsizePos : (0 : ℝ) < (size : ℝ) :=
    size_cast_pos_of_isChartStationaryData hdata
  have hcap := capture_diagonal_lt_one_of_negative_value hdata hvalue atomIndex
  rw [capture_leak_identity hdata atomIndex]
  have hinvPos : (0 : ℝ) < ((size : ℝ))⁻¹ := inv_pos.mpr hsizePos
  exact mul_pos (mul_pos hinterior (by linarith)) hinvPos

/-- **THE OFF-BLOCK WITNESS.**  At an interior atom some active label
has a block that misses the atom and a chart image that does not vanish
there.  This is the support content of the commutation: no atom sits
in every active block. -/
theorem exists_offBlock_capture_of_interior
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir) (hvalue : value < 0)
    {atomIndex : Fin size} (hinterior : 0 < value + weight atomIndex) :
    ∃ label ∈ activeSet, atomIndex ∉ activeSubset label
      ∧ (projection *ᵥ tightDir label) atomIndex ≠ 0 := by
  by_contra hnot
  push Not at hnot
  have hzero : ∑ label ∈ blockMissers activeSet activeSubset atomIndex,
      activeWeight label * ((projection *ᵥ tightDir label) atomIndex) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun label hmem => ?_
    rw [blockMissers, Finset.mem_filter] at hmem
    rw [hnot label hmem.1 hmem.2, pow_two, mul_zero, mul_zero]
  exact absurd hzero (capture_leak_pos_of_interior hdata hvalue hinterior).ne'

/-- **THE CROSS LEAK LAW.**  The whole sandwich, read at one atom pair.
The labels whose block misses the column atom carry the capture entry,
scaled by the complementary shifted weight.  The diagonal case is the
leak law, and the numeric extraction of this campaign shows that the
full pair form, not the diagonal shadow, is the layer that closes the
deficit residues. -/
theorem capture_cross_leak_identity
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir) (rowAtom colAtom : Fin size) :
    ∑ label ∈ blockMissers activeSet activeSubset colAtom,
        activeWeight label * ((projection *ᵥ tightDir label) rowAtom
          * (projection *ᵥ tightDir label) colAtom)
      = (1 - (value + weight colAtom))
        * (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
            rowAtom colAtom := by
  set assembly := chartMultiplierAssembly activeSet activeWeight tightDir
    with hassemblyDef
  have hsandwich : projection * assembly * projection = projection * assembly :=
    projector_sandwich_eq_capture hdata.isIdempotent hdata.assembly_commutes
  have hsplitAll : (projection * assembly * projection) rowAtom colAtom
      = ∑ label ∈ activeSet, activeWeight label
          * ((projection *ᵥ tightDir label) rowAtom
            * (projection *ᵥ tightDir label) colAtom) := by
    rw [hassemblyDef, chartMultiplierAssembly,
      sum_atomMatrix_sandwich_apply hdata.isSymmetric]
  have hcaptureSum : (projection * assembly) rowAtom colAtom
      = ∑ label ∈ activeSet, activeWeight label
          * ((projection *ᵥ tightDir label) rowAtom * tightDir label colAtom) := by
    rw [hassemblyDef, chartMultiplierAssembly, capture_apply_eq_sum]
  -- the holders read the shifted weight at the column atom
  have hholders : ∑ label ∈ blockHolders activeSet activeSubset colAtom,
      activeWeight label * ((projection *ᵥ tightDir label) rowAtom
        * (projection *ᵥ tightDir label) colAtom)
      = (value + weight colAtom) * (projection * assembly) rowAtom colAtom := by
    have hterm : ∀ label ∈ blockHolders activeSet activeSubset colAtom,
        activeWeight label * ((projection *ᵥ tightDir label) rowAtom
            * (projection *ᵥ tightDir label) colAtom)
          = (value + weight colAtom) * (activeWeight label
              * ((projection *ᵥ tightDir label) rowAtom
                * tightDir label colAtom)) := by
      intro label hmem
      rw [blockHolders, Finset.mem_filter] at hmem
      rw [projection_mulVec_tightDir_of_mem hdata hmem.1 hmem.2]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hcaptureSum]
    rw [blockHolders]
    refine congrArg _ (Finset.sum_filter_of_ne fun label hmem hne => ?_)
    by_contra hnot
    exact hne (by rw [hdata.tightDir_support label hmem colAtom hnot, mul_zero,
      mul_zero])
  have hpartition : ∑ label ∈ activeSet, activeWeight label
        * ((projection *ᵥ tightDir label) rowAtom
          * (projection *ᵥ tightDir label) colAtom)
      = (∑ label ∈ blockHolders activeSet activeSubset colAtom,
          activeWeight label * ((projection *ᵥ tightDir label) rowAtom
            * (projection *ᵥ tightDir label) colAtom))
        + ∑ label ∈ blockMissers activeSet activeSubset colAtom,
            activeWeight label * ((projection *ᵥ tightDir label) rowAtom
              * (projection *ᵥ tightDir label) colAtom) := by
    rw [blockHolders, blockMissers]
    exact (Finset.sum_filter_add_sum_filter_not activeSet
      (fun label => colAtom ∈ activeSubset label) _).symm
  rw [hsandwich] at hsplitAll
  rw [hpartition, hholders] at hsplitAll
  linarith

/-- **THE CAPTURE ENERGY.**  The chart image of a tight direction has the
shifted-weight energy of the direction: the chart is a symmetric
idempotent, thus the squared image reads the direction against its own
image. -/
theorem capture_energy_eq
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir) {label : activeIndex}
    (hmem : label ∈ activeSet) :
    ∑ atomIndex : Fin size, ((projection *ᵥ tightDir label) atomIndex) ^ 2
      = ∑ atomIndex : Fin size,
          (value + weight atomIndex) * tightDir label atomIndex ^ 2 := by
  have hgram : projectionᵀ * projection = projection := by
    rw [hdata.isSymmetric, hdata.isIdempotent]
  have hquad := gram_quadForm projection (tightDir label)
  rw [hgram] at hquad
  have hleft : (projection *ᵥ tightDir label) ⬝ᵥ (projection *ᵥ tightDir label)
      = ∑ atomIndex : Fin size,
          ((projection *ᵥ tightDir label) atomIndex) ^ 2 := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun _ _ => (sq _).symm
  have hright : tightDir label ⬝ᵥ (projection *ᵥ tightDir label)
      = ∑ atomIndex : Fin size,
          (value + weight atomIndex) * tightDir label atomIndex ^ 2 := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    by_cases hblock : atomIndex ∈ activeSubset label
    · rw [projection_mulVec_tightDir_of_mem hdata hmem hblock]
      ring
    · rw [hdata.tightDir_support label hmem atomIndex hblock]
      ring
  rw [← hleft, ← hquad, hright]

/-- **THE OFF-BLOCK ENERGY.**  Outside its own block the chart image of a
tight direction carries exactly the shifted-weight leak of the
direction.  This is the per-label form of the leak law, and it needs no
commutation at all. -/
theorem offBlock_capture_energy
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir) {label : activeIndex}
    (hmem : label ∈ activeSet) :
    ∑ atomIndex ∈ Finset.univ.filter (fun probe => probe ∉ activeSubset label),
        ((projection *ᵥ tightDir label) atomIndex) ^ 2
      = ∑ atomIndex : Fin size,
          (value + weight atomIndex) * (1 - (value + weight atomIndex))
            * tightDir label atomIndex ^ 2 := by
  have hpartition : ∑ atomIndex : Fin size,
        ((projection *ᵥ tightDir label) atomIndex) ^ 2
      = (∑ atomIndex ∈ Finset.univ.filter
            (fun probe => probe ∈ activeSubset label),
          ((projection *ᵥ tightDir label) atomIndex) ^ 2)
        + ∑ atomIndex ∈ Finset.univ.filter
            (fun probe => probe ∉ activeSubset label),
            ((projection *ᵥ tightDir label) atomIndex) ^ 2 :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun probe => probe ∈ activeSubset label) _).symm
  have hblockPart : ∑ atomIndex ∈ Finset.univ.filter
        (fun probe => probe ∈ activeSubset label),
        ((projection *ᵥ tightDir label) atomIndex) ^ 2
      = ∑ atomIndex : Fin size,
          (value + weight atomIndex) ^ 2 * tightDir label atomIndex ^ 2 := by
    have hterm : ∀ atomIndex ∈ Finset.univ.filter
          (fun probe => probe ∈ activeSubset label),
        ((projection *ᵥ tightDir label) atomIndex) ^ 2
          = (value + weight atomIndex) ^ 2 * tightDir label atomIndex ^ 2 := by
      intro atomIndex hatom
      rw [Finset.mem_filter] at hatom
      rw [projection_mulVec_tightDir_of_mem hdata hmem hatom.2]
      ring
    rw [Finset.sum_congr rfl hterm]
    refine Finset.sum_filter_of_ne fun atomIndex _ hne => ?_
    by_contra hnot
    exact hne (by rw [hdata.tightDir_support label hmem atomIndex hnot]; ring)
  rw [capture_energy_eq hdata hmem, hblockPart] at hpartition
  have hfinal : ∑ atomIndex ∈ Finset.univ.filter
        (fun probe => probe ∉ activeSubset label),
        ((projection *ᵥ tightDir label) atomIndex) ^ 2
      = (∑ atomIndex : Fin size,
            (value + weight atomIndex) * tightDir label atomIndex ^ 2)
        - ∑ atomIndex : Fin size,
            (value + weight atomIndex) ^ 2 * tightDir label atomIndex ^ 2 := by
    linarith
  rw [hfinal, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun atomIndex _ => by ring

/-! ## Layer 5 — the slot form at a diagonal Gram core -/

/-- A diagonally conjugated Gram is the weighted sum of the rank-one
atoms of its columns. -/
theorem gram_diagonal_conjugate_eq_sum_atomMatrix {basisCount : ℕ}
    (columns : Matrix (Fin size) (Fin basisCount) ℝ)
    (coreDiag : Fin basisCount → ℝ) :
    columns * Matrix.diagonal coreDiag * columnsᵀ
      = ∑ slot : Fin basisCount,
          coreDiag slot • atomMatrix (fun atomIndex => columns atomIndex slot) := by
  classical
  ext rowIndex colIndex
  rw [Matrix.mul_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun slot _ => ?_
  rw [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.smul_apply,
    atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

namespace SharedPrivateData

variable {crux : SixThreeCrux}

/-- **THE SLOT FORM.**  A shared-private datum with a diagonal Gram core
writes its assembly as the weighted sum of the rank-one atoms of the
basis directions. -/
theorem assembly_eq_slot_sum (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) :
    chartMultiplierAssembly data.activeSet data.reducedWeight data.tightDir
      = ∑ slot : Fin data.basisCount,
          gramDiag slot • atomMatrix (data.tightDir (data.basisLabel slot)) := by
  classical
  have hH := data.hHform
  rw [hdiag, gram_diagonal_conjugate_eq_sum_atomMatrix] at hH
  rw [← hH]
  refine Finset.sum_congr rfl fun slot _ => ?_
  rfl

/-- The slot form reads the assembly diagonal: the Gram core diagonal
carries the constant one sixth against the squared basis entries. -/
theorem slot_assembly_diagonal (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) (atomIndex : Fin 6) :
    ∑ slot : Fin data.basisCount,
        gramDiag slot * data.tightDir (data.basisLabel slot) atomIndex ^ 2
      = ((6 : ℕ) : ℝ)⁻¹ := by
  classical
  have hfull := data.hdata.assembly_diagonal atomIndex
  rw [data.assembly_eq_slot_sum hdiag] at hfull
  rw [← hfull, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun slot _ => ?_
  rw [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul, pow_two]

/-- Every Gram core diagonal entry is strictly positive: the core is
positive semidefinite and kernel-free. -/
theorem gramDiag_pos (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) (slot : Fin data.basisCount) :
    0 < gramDiag slot := by
  have hpsd := data.hpsd
  have hker := data.hker
  rw [hdiag] at hpsd hker
  have hpos := posSemidef_diagonal_pos_of_kernel_free hpsd hker slot
  rwa [Matrix.diagonal_apply_eq] at hpos

/-- The slot family that misses an atom: the basis slots whose support
does not hold it. -/
noncomputable def offSupportSlots (data : SharedPrivateData crux)
    (atomIndex : Fin 6) : Finset (Fin data.basisCount) :=
  Finset.univ.filter fun slot =>
    atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot)

/-- **THE SLOT LEAK LAW.**  At a diagonal Gram core the leak runs over
the basis slots whose support misses the atom. -/
theorem slot_leak_identity (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) (atomIndex : Fin 6) :
    ∑ slot ∈ data.offSupportSlots atomIndex,
        gramDiag slot
          * (((chartPointOfDesign crux.design).chart
              *ᵥ data.tightDir (data.basisLabel slot)) atomIndex) ^ 2
      = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
        * (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex))
        * ((6 : ℕ) : ℝ)⁻¹ := by
  set chart := (chartPointOfDesign crux.design).chart with hchartDef
  set assembly := chartMultiplierAssembly data.activeSet data.reducedWeight
    data.tightDir with hassemblyDef
  set shifted : ℝ := chartObjective (chartPointOfDesign crux.design)
    + (chartPointOfDesign crux.design).weight atomIndex with hshiftedDef
  have hsandwich : chart * assembly * chart = chart * assembly :=
    projector_sandwich_eq_capture data.hdata.isIdempotent
      data.hdata.assembly_commutes
  have hcapture : (chart * assembly) atomIndex atomIndex
      = shifted * ((6 : ℕ) : ℝ)⁻¹ :=
    diagonal_projection_mul_multiplier_of_isChartStationaryData data.hdata atomIndex
  have hsplit : (chart * assembly * chart) atomIndex atomIndex
      = ∑ slot : Fin data.basisCount, gramDiag slot
          * ((chart *ᵥ data.tightDir (data.basisLabel slot)) atomIndex) ^ 2 := by
    rw [hassemblyDef, data.assembly_eq_slot_sum hdiag,
      sum_atomMatrix_sandwich_diagonal data.hdata.isSymmetric]
  -- the supporting slots read the shifted weight twice
  have hsupport : ∑ slot ∈ Finset.univ.filter (fun slot =>
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)),
      gramDiag slot
        * ((chart *ᵥ data.tightDir (data.basisLabel slot)) atomIndex) ^ 2
      = shifted ^ 2 * ((6 : ℕ) : ℝ)⁻¹ := by
    have hterm : ∀ slot ∈ Finset.univ.filter (fun slot =>
          atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)),
        gramDiag slot
            * ((chart *ᵥ data.tightDir (data.basisLabel slot)) atomIndex) ^ 2
          = shifted ^ 2 * (gramDiag slot
              * data.tightDir (data.basisLabel slot) atomIndex ^ 2) := by
      intro slot hmem
      rw [Finset.mem_filter] at hmem
      have hmemActive : data.basisLabel slot ∈ data.activeSet := by
        have hpos := data.hmem slot
        simp only [positiveActiveSet, Finset.mem_filter] at hpos
        exact hpos.1
      have hblock := datumTightSupport_subset data.hdata hmemActive hmem.2
      rw [hchartDef, projection_mulVec_tightDir_of_mem data.hdata hmemActive hblock,
        ← hshiftedDef]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hrestrict : ∑ slot ∈ Finset.univ.filter (fun slot =>
          atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)),
        gramDiag slot * data.tightDir (data.basisLabel slot) atomIndex ^ 2
        = ∑ slot : Fin data.basisCount,
            gramDiag slot * data.tightDir (data.basisLabel slot) atomIndex ^ 2 := by
      refine Finset.sum_filter_of_ne fun slot _ hne => ?_
      by_contra hnot
      rw [mem_datumTightSupport, not_not] at hnot
      exact hne (by rw [hnot, pow_two, mul_zero, mul_zero])
    rw [hrestrict, data.slot_assembly_diagonal hdiag atomIndex]
  have hpartition : ∑ slot : Fin data.basisCount, gramDiag slot
        * ((chart *ᵥ data.tightDir (data.basisLabel slot)) atomIndex) ^ 2
      = (∑ slot ∈ Finset.univ.filter (fun slot =>
            atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)),
          gramDiag slot
            * ((chart *ᵥ data.tightDir (data.basisLabel slot)) atomIndex) ^ 2)
        + ∑ slot ∈ data.offSupportSlots atomIndex, gramDiag slot
            * ((chart *ᵥ data.tightDir (data.basisLabel slot)) atomIndex) ^ 2 := by
    rw [offSupportSlots]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun slot => atomIndex ∈ datumTightSupport data.tightDir
        (data.basisLabel slot)) _).symm
  rw [hsandwich, hcapture] at hsplit
  rw [hpartition, hsupport] at hsplit
  have hfinal : ∑ slot ∈ data.offSupportSlots atomIndex, gramDiag slot
      * ((chart *ᵥ data.tightDir (data.basisLabel slot)) atomIndex) ^ 2
      = shifted * ((6 : ℕ) : ℝ)⁻¹ - shifted ^ 2 * ((6 : ℕ) : ℝ)⁻¹ := by
    linarith
  rw [hfinal]
  ring

/-- **THE OFF-SUPPORT SLOT.**  At an interior atom some basis support
misses the atom.  A diagonal Gram core and the leak law force it. -/
theorem exists_offSupport_slot (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) {atomIndex : Fin 6}
    (hinterior : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex) :
    ∃ slot : Fin data.basisCount,
      atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot) := by
  by_contra hnot
  push Not at hnot
  have hempty : data.offSupportSlots atomIndex = ∅ := by
    rw [offSupportSlots, Finset.filter_eq_empty_iff]
    intro slot _
    rw [not_not]
    exact hnot slot
  have hleak := data.slot_leak_identity hdiag atomIndex
  rw [hempty, Finset.sum_empty] at hleak
  have hcap := capture_diagonal_lt_one_of_negative_value data.hdata data.hvalueNeg
    atomIndex
  have hinvPos : (0 : ℝ) < ((6 : ℕ) : ℝ)⁻¹ := by norm_num
  nlinarith

/-- **THE SLOT TERM CAP.**  One off-support slot carries at most the
whole leak: the leak is a sum of nonnegative terms. -/
theorem slot_leak_term_le (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) {atomIndex : Fin 6}
    {slot : Fin data.basisCount}
    (hout : atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot)) :
    gramDiag slot
        * (((chartPointOfDesign crux.design).chart
            *ᵥ data.tightDir (data.basisLabel slot)) atomIndex) ^ 2
      ≤ (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
        * (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex))
        * ((6 : ℕ) : ℝ)⁻¹ := by
  have hmemSlot : slot ∈ data.offSupportSlots atomIndex := by
    rw [offSupportSlots, Finset.mem_filter]
    exact ⟨Finset.mem_univ slot, hout⟩
  have hterms : ∀ otherSlot ∈ data.offSupportSlots atomIndex,
      0 ≤ gramDiag otherSlot
        * (((chartPointOfDesign crux.design).chart
            *ᵥ data.tightDir (data.basisLabel otherSlot)) atomIndex) ^ 2 :=
    fun otherSlot _ => mul_nonneg (data.gramDiag_pos hdiag otherSlot).le
      (sq_nonneg _)
  have hsingle := Finset.single_le_sum (f := fun otherSlot =>
      gramDiag otherSlot
        * (((chartPointOfDesign crux.design).chart
            *ᵥ data.tightDir (data.basisLabel otherSlot)) atomIndex) ^ 2)
    hterms hmemSlot
  rwa [data.slot_leak_identity hdiag atomIndex] at hsingle

/-- **THE OFF-SUPPORT CAPTURE WITNESS.**  At an interior atom some basis
support misses the atom AND the chart image of that basis direction does
not vanish there.  This is the sharp support content of the
commutation. -/
theorem exists_offSupport_capture_slot (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) {atomIndex : Fin 6}
    (hinterior : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex) :
    ∃ slot : Fin data.basisCount,
      atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot)
        ∧ ((chartPointOfDesign crux.design).chart
            *ᵥ data.tightDir (data.basisLabel slot)) atomIndex ≠ 0 := by
  by_contra hnot
  push Not at hnot
  have hzero : ∑ slot ∈ data.offSupportSlots atomIndex, gramDiag slot
      * (((chartPointOfDesign crux.design).chart
          *ᵥ data.tightDir (data.basisLabel slot)) atomIndex) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun slot hmem => ?_
    rw [offSupportSlots, Finset.mem_filter] at hmem
    rw [hnot slot hmem.2, pow_two, mul_zero, mul_zero]
  rw [data.slot_leak_identity hdiag atomIndex] at hzero
  have hcap := capture_diagonal_lt_one_of_negative_value data.hdata data.hvalueNeg
    atomIndex
  have hinvPos : (0 : ℝ) < ((6 : ℕ) : ℝ)⁻¹ := by norm_num
  nlinarith

/-- **THE MISSING-SLOT LAW.**  At an interior atom the basis support
multiplicity is strictly below the basis count.  No atom sits in every
basis support. -/
theorem multiplicity_lt_basisCount (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) {atomIndex : Fin 6}
    (hinterior : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex) :
    basisSupportMultiplicity data.tightDir data.basisLabel atomIndex
      < data.basisCount := by
  classical
  obtain ⟨witness, hwitness⟩ := data.exists_offSupport_slot hdiag hinterior
  have hsubset : (Finset.univ.filter fun slot =>
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot))
      ⊂ (Finset.univ : Finset (Fin data.basisCount)) := by
    refine Finset.ssubset_univ_iff.mpr fun heq => ?_
    have hmemAll : witness ∈ Finset.univ.filter fun slot =>
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
      rw [heq]; exact Finset.mem_univ witness
    rw [Finset.mem_filter] at hmemAll
    exact hwitness hmemAll.2
  have hcard := Finset.card_lt_card hsubset
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  rw [basisSupportMultiplicity]
  exact hcard

/-! ### The slot mass lattice -/

/-- **THE SLOT MASS CAP.**  Every Gram core diagonal entry is at most one
half: its support carries three atoms and each atom caps the entry at
one sixth. -/
theorem slot_mass_le_half (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) (slot : Fin data.basisCount) :
    gramDiag slot ≤ 1 / 2 := by
  -- the direction mass sits on the support
  have hmemActive : data.basisLabel slot ∈ data.activeSet := by
    have hpos := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at hpos
    exact hpos.1
  have hunit := data.hdata.tightDir_unit (data.basisLabel slot) hmemActive
  rw [dotProduct] at hunit
  have hmass : ∑ atomIndex ∈ datumTightSupport data.tightDir
        (data.basisLabel slot),
      data.tightDir (data.basisLabel slot) atomIndex ^ 2 = 1 := by
    have hfilter : ∑ atomIndex ∈ datumTightSupport data.tightDir
          (data.basisLabel slot),
        data.tightDir (data.basisLabel slot) atomIndex ^ 2
        = ∑ atomIndex : Fin 6,
            data.tightDir (data.basisLabel slot) atomIndex ^ 2 := by
      rw [datumTightSupport]
      refine Finset.sum_filter_of_ne fun atomIndex _ hne => ?_
      intro habs
      exact hne (by rw [habs, pow_two, mul_zero])
    rw [hfilter, ← hunit]
    exact Finset.sum_congr rfl fun atomIndex _ => sq _
  -- each atom caps the scaled square by one sixth
  have hcap : ∀ atomIndex : Fin 6,
      gramDiag slot * data.tightDir (data.basisLabel slot) atomIndex ^ 2
        ≤ ((6 : ℕ) : ℝ)⁻¹ := by
    intro atomIndex
    have htotal := data.slot_assembly_diagonal hdiag atomIndex
    have hterms : ∀ otherSlot ∈ (Finset.univ : Finset (Fin data.basisCount)),
        0 ≤ gramDiag otherSlot
          * data.tightDir (data.basisLabel otherSlot) atomIndex ^ 2 :=
      fun otherSlot _ => mul_nonneg (data.gramDiag_pos hdiag otherSlot).le
        (sq_nonneg _)
    have hsingle := Finset.single_le_sum (f := fun otherSlot =>
        gramDiag otherSlot
          * data.tightDir (data.basisLabel otherSlot) atomIndex ^ 2)
      hterms (Finset.mem_univ slot)
    rwa [htotal] at hsingle
  have hsum : gramDiag slot
      = ∑ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
          gramDiag slot * data.tightDir (data.basisLabel slot) atomIndex ^ 2 := by
    rw [← Finset.mul_sum, hmass, mul_one]
  have hbound : ∑ atomIndex ∈ datumTightSupport data.tightDir
        (data.basisLabel slot),
        gramDiag slot * data.tightDir (data.basisLabel slot) atomIndex ^ 2
      ≤ ∑ _atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
          ((6 : ℕ) : ℝ)⁻¹ :=
    Finset.sum_le_sum fun atomIndex _ => hcap atomIndex
  rw [Finset.sum_const, data.hthree slot, nsmul_eq_mul] at hbound
  rw [hsum]
  refine hbound.trans ?_
  norm_num

/-- **THE PRIVATE MASS.**  The pin atom sits in one basis support only,
thus its Gram core entry reads the whole constant one sixth. -/
theorem private_mass_eq (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) :
    gramDiag data.privateSlot
        * data.tightDir (data.basisLabel data.privateSlot) data.pinAtom ^ 2
      = ((6 : ℕ) : ℝ)⁻¹ := by
  have htotal := data.slot_assembly_diagonal hdiag data.pinAtom
  rw [← htotal]
  symm
  refine Finset.sum_eq_single data.privateSlot (fun slot _ hne => ?_)
    (fun habs => absurd (Finset.mem_univ _) habs)
  rw [data.hprivate slot hne, pow_two, mul_zero, mul_zero]

/-- The private slot carries at least one sixth of the Gram core mass:
the pin entry is a unit-vector coordinate. -/
theorem private_mass_ge (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) :
    ((6 : ℕ) : ℝ)⁻¹ ≤ gramDiag data.privateSlot := by
  have hmemActive : data.basisLabel data.privateSlot ∈ data.activeSet := by
    have hpos := data.hmem data.privateSlot
    simp only [positiveActiveSet, Finset.mem_filter] at hpos
    exact hpos.1
  have hunit := data.hdata.tightDir_unit (data.basisLabel data.privateSlot) hmemActive
  rw [dotProduct] at hunit
  have hsq : data.tightDir (data.basisLabel data.privateSlot) data.pinAtom ^ 2 ≤ 1 := by
    have hle := Finset.single_le_sum
      (f := fun atomIndex : Fin 6 =>
        data.tightDir (data.basisLabel data.privateSlot) atomIndex
          * data.tightDir (data.basisLabel data.privateSlot) atomIndex)
      (fun atomIndex _ => mul_self_nonneg _) (Finset.mem_univ data.pinAtom)
    rw [hunit] at hle
    rw [pow_two]
    exact hle
  have hnn := (data.gramDiag_pos hdiag data.privateSlot).le
  rw [← data.private_mass_eq hdiag]
  nlinarith [sq_nonneg (data.tightDir (data.basisLabel data.privateSlot)
    data.pinAtom)]

/-! ## Layer 6 — the pair circuit geometry -/

/-- The reconstruction of a pair circuit: the label is the combination of
the two live basis columns. -/
theorem pair_reconstruction (data : SharedPrivateData crux)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet)
    (hpos : 0 < data.reducedWeight label)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hpair : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      data.labelCoeff label slot = 0) (atomIndex : Fin 6) :
    data.tightDir label atomIndex
      = data.labelCoeff label slotOne
          * data.tightDir (data.basisLabel slotOne) atomIndex
        + data.labelCoeff label slotTwo
          * data.tightDir (data.basisLabel slotTwo) atomIndex := by
  classical
  rw [data.reconstruction_apply hmem hpos atomIndex]
  have hrestrict : ∑ slot, data.labelCoeff label slot
      * data.tightDir (data.basisLabel slot) atomIndex
      = ∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin data.basisCount)),
          data.labelCoeff label slot
            * data.tightDir (data.basisLabel slot) atomIndex := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro slot _ hnot
    have honeNe : slot ≠ slotOne := fun heq =>
      hnot (heq ▸ Finset.mem_insert_self _ _)
    have htwoNe : slot ≠ slotTwo := fun heq =>
      hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [hpair slot honeNe htwoNe, zero_mul]
  rw [hrestrict, Finset.sum_pair hne]

/-- **THE DIFFERENCE ATOM.**  An atom in one support and not the other
sits in the circuit label's own support. -/
theorem pairCircuit_mem_support_of_sdiff (data : SharedPrivateData crux)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet)
    (hpos : 0 < data.reducedWeight label)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hcoeffOne : data.labelCoeff label slotOne ≠ 0)
    (hpair : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      data.labelCoeff label slot = 0)
    {atomIndex : Fin 6}
    (hin : atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hout : atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slotTwo)) :
    atomIndex ∈ datumTightSupport data.tightDir label := by
  classical
  rw [mem_datumTightSupport] at hin ⊢
  rw [mem_datumTightSupport, not_not] at hout
  rw [data.pair_reconstruction hmem hpos hne hpair atomIndex, hout, mul_zero,
    add_zero]
  exact mul_ne_zero hcoeffOne hin

/-- **THE PAIR CIRCUITS SHARE TWO ATOMS.**  The two supports of a pair
circuit differ inside the label's block of three atoms.  Each support
has three atoms, thus the two differences have the same cardinality and
together fit in three atoms.  Thus the intersection has at least two
atoms — one more than the landed pair law gives. -/
theorem pairCircuit_two_le_inter_card (data : SharedPrivateData crux)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet)
    (hpos : 0 < data.reducedWeight label)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hcoeffOne : data.labelCoeff label slotOne ≠ 0)
    (hcoeffTwo : data.labelCoeff label slotTwo ≠ 0)
    (hpair : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      data.labelCoeff label slot = 0) :
    2 ≤ (datumTightSupport data.tightDir (data.basisLabel slotOne)
      ∩ datumTightSupport data.tightDir (data.basisLabel slotTwo)).card := by
  classical
  set supportOne := datumTightSupport data.tightDir (data.basisLabel slotOne)
    with hsupportOneDef
  set supportTwo := datumTightSupport data.tightDir (data.basisLabel slotTwo)
    with hsupportTwoDef
  -- the two differences sit in the label's support
  have hdiffOne : supportOne \ supportTwo ⊆ datumTightSupport data.tightDir label := by
    intro atomIndex hatom
    rw [Finset.mem_sdiff] at hatom
    exact data.pairCircuit_mem_support_of_sdiff hmem hpos hne hcoeffOne hpair
      hatom.1 hatom.2
  have hdiffTwo : supportTwo \ supportOne ⊆ datumTightSupport data.tightDir label := by
    intro atomIndex hatom
    rw [Finset.mem_sdiff] at hatom
    refine data.pairCircuit_mem_support_of_sdiff hmem hpos (Ne.symm hne) hcoeffTwo
      (fun slot htwoNe honeNe => hpair slot honeNe htwoNe) hatom.1 hatom.2
  have hunion : (supportOne \ supportTwo) ∪ (supportTwo \ supportOne)
      ⊆ datumTightSupport data.tightDir label :=
    Finset.union_subset hdiffOne hdiffTwo
  have hdisjoint : Disjoint (supportOne \ supportTwo) (supportTwo \ supportOne) :=
    Finset.disjoint_left.mpr fun atomIndex hone htwo =>
      (Finset.mem_sdiff.mp htwo).2 (Finset.mem_sdiff.mp hone).1
  have hcardUnion : (supportOne \ supportTwo).card + (supportTwo \ supportOne).card
      ≤ (datumTightSupport data.tightDir label).card := by
    rw [← Finset.card_union_of_disjoint hdisjoint]
    exact Finset.card_le_card hunion
  -- the label's support fits in its block of three atoms
  have hlabelCard : (datumTightSupport data.tightDir label).card ≤ 3 := by
    have hsub := datumTightSupport_subset data.hdata hmem
    have hcard := Finset.card_le_card hsub
    rwa [data.hdata.activeSubset_card label hmem] at hcard
  -- each difference complements the intersection inside a support of three
  have hsplitOne : (supportOne \ supportTwo).card + (supportOne ∩ supportTwo).card
      = 3 := by
    rw [Finset.card_sdiff_add_card_inter, hsupportOneDef, data.hthree slotOne]
  have hsplitTwo : (supportTwo \ supportOne).card + (supportTwo ∩ supportOne).card
      = 3 := by
    rw [Finset.card_sdiff_add_card_inter, hsupportTwoDef, data.hthree slotTwo]
  have hcomm : (supportTwo ∩ supportOne).card = (supportOne ∩ supportTwo).card := by
    rw [Finset.inter_comm]
  rw [hcomm] at hsplitTwo
  omega

/-- **THE PAIR CAPTURE KILL.**  At an atom of one support that the other
misses, the chart annihilates the other basis direction.  The label's
own tight read prices the combination, and the missing column drops
out. -/
theorem pairCircuit_capture_eq_zero (data : SharedPrivateData crux)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet)
    (hpos : 0 < data.reducedWeight label)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hcoeffOne : data.labelCoeff label slotOne ≠ 0)
    (hcoeffTwo : data.labelCoeff label slotTwo ≠ 0)
    (hpair : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      data.labelCoeff label slot = 0)
    {atomIndex : Fin 6}
    (hin : atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hout : atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slotTwo)) :
    ((chartPointOfDesign crux.design).chart
      *ᵥ data.tightDir (data.basisLabel slotTwo)) atomIndex = 0 := by
  classical
  set chart := (chartPointOfDesign crux.design).chart with hchartDef
  set shifted : ℝ := chartObjective (chartPointOfDesign crux.design)
    + (chartPointOfDesign crux.design).weight atomIndex with hshiftedDef
  have hlabelSupport := data.pairCircuit_mem_support_of_sdiff hmem hpos hne
    hcoeffOne hpair hin hout
  have hlabelBlock := datumTightSupport_subset data.hdata hmem hlabelSupport
  have hmemOne : data.basisLabel slotOne ∈ data.activeSet := by
    have hposOne := data.hmem slotOne
    simp only [positiveActiveSet, Finset.mem_filter] at hposOne
    exact hposOne.1
  have hblockOne := datumTightSupport_subset data.hdata hmemOne hin
  -- the label reads the shifted weight on its own block
  have hlabelRead := projection_mulVec_tightDir_of_mem data.hdata hmem hlabelBlock
  have hcolumnRead := projection_mulVec_tightDir_of_mem data.hdata hmemOne hblockOne
  -- the chart image of the label splits over the pair
  have hsplit : (chart *ᵥ data.tightDir label) atomIndex
      = data.labelCoeff label slotOne
          * (chart *ᵥ data.tightDir (data.basisLabel slotOne)) atomIndex
        + data.labelCoeff label slotTwo
          * (chart *ᵥ data.tightDir (data.basisLabel slotTwo)) atomIndex := by
    rw [Matrix.mulVec, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
      dotProduct, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun otherAtom _ => ?_
    rw [data.pair_reconstruction hmem hpos hne hpair otherAtom]
    ring
  have hvalue : data.tightDir label atomIndex
      = data.labelCoeff label slotOne
        * data.tightDir (data.basisLabel slotOne) atomIndex := by
    rw [data.pair_reconstruction hmem hpos hne hpair atomIndex]
    rw [mem_datumTightSupport, not_not] at hout
    rw [hout, mul_zero, add_zero]
  rw [hchartDef] at hsplit
  rw [hlabelRead, hcolumnRead, hvalue, ← hshiftedDef] at hsplit
  have hzero : data.labelCoeff label slotTwo
      * (chart *ᵥ data.tightDir (data.basisLabel slotTwo)) atomIndex = 0 := by
    rw [hchartDef]; linarith
  exact (mul_eq_zero.mp hzero).resolve_left hcoeffTwo

end SharedPrivateData

/-! ## Layer 7 — the narrowed residues and the dispatch -/

/-- **THE LOW-MULTIPLICITY SIX RESIDUE.**  The interior six residue with
the multiplicity cap added.  The cap is free: the missing-slot law
gives it at every interior atom. -/
def SharedPrivateDeficitSixLowMultiplicityClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (gramDiag : Fin data.basisCount → ℝ),
    data.gram = Matrix.diagonal gramDiag →
    Matrix.trace data.coeff = 3 →
    data.basisCount = 6 →
    (Finset.univ.filter fun atomIndex =>
        basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 1).card = 1 →
    (Finset.univ.filter fun atomIndex =>
        basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 2).card ≤ 1 →
    (∀ atomIndex : Fin 6, 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex) →
    ∑ atomIndex : Fin 6,
      basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 18 →
    (∀ atomIndex : Fin 6,
      basisSupportMultiplicity data.tightDir data.basisLabel atomIndex ≤ 5) →
    False

/-- **THE SIX NARROWING BY THE LEAK.**  The multiplicity cap costs
nothing: at basis count six the missing-slot law caps every interior
atom at five.  This removes the whole multiplicity-six profile class
from the deficit residue. -/
theorem sharedPrivateDeficitSixInteriorClosed_of_lowMultiplicity
    (hnarrow : SharedPrivateDeficitSixLowMultiplicityClosed) :
    SharedPrivateDeficitSixInteriorClosed := by
  classical
  intro crux data gramDiag hdiag htraceThree hsix hcardOne hcardTwo hinterior hmass
  refine hnarrow crux data gramDiag hdiag htraceThree hsix hcardOne hcardTwo
    hinterior hmass fun atomIndex => ?_
  have hlt := data.multiplicity_lt_basisCount hdiag (hinterior atomIndex)
  omega

/-- **THE SHARED PAIR RESIDUE.**  The pair circuit residue with the two
geometric conclusions added: the two supports share at least two atoms,
and at every atom of the difference the chart kills the other basis
direction. -/
def SharedPrivateCircuitPairSharedClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      (∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
        data.labelCoeff label slot = 0) →
      2 ≤ (datumTightSupport data.tightDir (data.basisLabel slotOne)
        ∩ datumTightSupport data.tightDir (data.basisLabel slotTwo)).card →
      (∀ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) →
        atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slotTwo) →
        ((chartPointOfDesign crux.design).chart
          *ᵥ data.tightDir (data.basisLabel slotTwo)) atomIndex = 0) →
      (∀ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) →
        atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slotOne) →
        ((chartPointOfDesign crux.design).chart
          *ᵥ data.tightDir (data.basisLabel slotOne)) atomIndex = 0) →
      False

/-- **THE PAIR NARROWING.**  The two geometric conclusions are free. -/
theorem sharedPrivateCircuitPairClosed_of_shared
    (hnarrow : SharedPrivateCircuitPairSharedClosed) :
    SharedPrivateCircuitPairClosed := by
  classical
  intro crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
  refine hnarrow crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo
    hpair (data.pairCircuit_two_le_inter_card hmem hpos hne hcoeffOne hcoeffTwo
      hpair) (fun atomIndex hin hout =>
        data.pairCircuit_capture_eq_zero hmem hpos hne hcoeffOne hcoeffTwo hpair
          hin hout) (fun atomIndex hin hout => ?_)
  exact data.pairCircuit_capture_eq_zero hmem hpos (Ne.symm hne) hcoeffTwo
    hcoeffOne (fun slot htwoNe honeNe => hpair slot honeNe htwoNe) hin hout

/-- **THE LEAK STRATA DISPATCH.**  The narrowed pair residue, the wide
circuit residue, the boundary residue, the narrowed six residue and the
interior complement residue close the generic shared-private kill. -/
theorem sharedPrivateKilled_of_leak_strata
    (hpair : SharedPrivateCircuitPairSharedClosed)
    (hwide : SharedPrivateCircuitWideClosed)
    (hboundary : SharedPrivateBoundaryClosed)
    (hsix : SharedPrivateDeficitSixLowMultiplicityClosed)
    (hcomplement : SharedPrivateDeficitComplementInteriorClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_interior_strata
    (sharedPrivateExtrasClosed_of_width
      (sharedPrivateCircuitPairClosed_of_shared hpair) hwide)
    hboundary
    (sharedPrivateDeficitSixInteriorClosed_of_lowMultiplicity hsix)
    hcomplement

/-- The rank-four bridge through the leak strata. -/
theorem rankFourSharedPrivateClosed_of_leak_strata
    (hpair : SharedPrivateCircuitPairSharedClosed)
    (hwide : SharedPrivateCircuitWideClosed)
    (hboundary : SharedPrivateBoundaryClosed)
    (hsix : SharedPrivateDeficitSixLowMultiplicityClosed)
    (hcomplement : SharedPrivateDeficitComplementInteriorClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_leak_strata hpair hwide hboundary hsix hcomplement)

/-- The rank-five bridge through the leak strata. -/
theorem rankFiveSharedPrivateClosed_of_leak_strata
    (hpair : SharedPrivateCircuitPairSharedClosed)
    (hwide : SharedPrivateCircuitWideClosed)
    (hboundary : SharedPrivateBoundaryClosed)
    (hsix : SharedPrivateDeficitSixLowMultiplicityClosed)
    (hcomplement : SharedPrivateDeficitComplementInteriorClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_leak_strata hpair hwide hboundary hsix hcomplement)

/-- The rank-six bridge through the leak strata. -/
theorem rankSixSharedPrivateClosed_of_leak_strata
    (hpair : SharedPrivateCircuitPairSharedClosed)
    (hwide : SharedPrivateCircuitWideClosed)
    (hboundary : SharedPrivateBoundaryClosed)
    (hsix : SharedPrivateDeficitSixLowMultiplicityClosed)
    (hcomplement : SharedPrivateDeficitComplementInteriorClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_leak_strata hpair hwide hboundary hsix hcomplement)

end Gtz

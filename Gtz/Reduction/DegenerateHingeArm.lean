/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.ThresholdCellHingeMap
import Gtz.Design.TieCensusCompletion
import Gtz.Design.CompanionConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The degenerate hinge arm at general rank

`Gtz.DegenerateArmAt` is the third arm of `Gtz.design_stress_trichotomy`: a
nonzero stress whose supported atoms all meet one hyperplane. This module closes
the two mechanical halves of that arm at every rank and states the one half that
survives.

## What this module lands

The orthonormal frame of a hyperplane is a THEOREM at every rank
(`Gtz.hyperplaneFrameExists`), thus `Gtz.HyperplaneFrameExists` leaves the
residual list. The construction is a Householder reflection with the stable sign
choice, so it needs no case analysis and no Gram-Schmidt recursion.

The SURPLUS half of the Schur producer is a THEOREM at every rank
(`Gtz.exists_pole_surplus`). On the degenerate branch the poles carry the whole
Parseval mass of the probe direction (`Gtz.poleMass_eq_one`) while their weights
miss at least one supported label, thus some single pole overshoots.

What survives is the COVER half alone, at a subset that holds a surplus pole.

## The defect in the producer route, and its repair

`Gtz.DegenerateHyperplaneProducer` and `Gtz.DegeneratePoleAugmentation` drop the
tie and the primitivity of the design. That makes them STRICTLY STRONGER than
the arm they serve: `Gtz.hyperplaneProducer_forbids_parallelPair_tie` proves that
the producer forbids every tie with a parallel pair, and a tie with a parallel
pair is exactly what the arm permits. `Gtz.DegenerateHyperplaneCover` is the
repair. It carries the primitivity, the tie, the stress and the hyperplane, and
its rank-three instance is a THEOREM off the closed two-pole capstone
(`Gtz.degenerateHyperplaneCover_three_of_selection`).

The refutation is UNCONDITIONAL. `Gtz.sixSplitDiamondDesign` is a `(6,3)` tie
that carries a parallel pair, thus
`Gtz.not_degenerateHyperplaneProducer_six_three` and
`Gtz.not_degeneratePoleAugmentation_six_three` are theorems, while
`Gtz.degenerateHyperplaneCover_six_three` proves the repaired residual at the
SAME cell. `Gtz.degenerate_residual_verdict_six_three` records the four
verdicts together.
-/

namespace Gtz

open Matrix Finset

variable {n k size rank : ℕ}

/-! ## Part 1: Householder reflections at general rank

A reflection in the hyperplane orthogonal to one axis. Everything below is one
identity about the reflection: it preserves the dot product, and it is its own
adjoint. Neither reads the dimension. -/

/-- The reflection of a probe in the hyperplane orthogonal to an axis. At a zero
axis the scaling term vanishes, thus the reflection is the identity and every
law below holds with no hypothesis on the axis. -/
noncomputable def reflect (axis probe : Fin rank → ℝ) : Fin rank → ℝ :=
  probe - (2 * (axis ⬝ᵥ probe) / (axis ⬝ᵥ axis)) • axis

/-- A vector of zero length is the zero vector. -/
theorem eq_zero_of_selfDotProduct_eq_zero {vec : Fin rank → ℝ} (hzero : vec ⬝ᵥ vec = 0) :
    vec = 0 := by
  by_contra hne
  exact absurd hzero (ne_of_gt (selfDotProduct_pos hne))

/-- A reflection about the zero axis is the identity. -/
theorem reflect_zero_axis (probe : Fin rank → ℝ) : reflect (0 : Fin rank → ℝ) probe = probe := by
  rw [reflect, smul_zero, sub_zero]

/-- **THE REFLECTION IS SELF-ADJOINT.**  No hypothesis on the axis: the two
sides carry the same scalar factor, and `Gtz.dotProduct_comm` matches them. -/
theorem dotProduct_reflect_left (axis leftProbe rightProbe : Fin rank → ℝ) :
    reflect axis leftProbe ⬝ᵥ rightProbe = leftProbe ⬝ᵥ reflect axis rightProbe := by
  simp only [reflect, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  rw [dotProduct_comm leftProbe axis]
  ring

/-- **THE REFLECTION IS AN ISOMETRY.**  Again with no hypothesis: at a zero axis
it is the identity, and otherwise the cross terms cancel against the square
term. -/
theorem dotProduct_reflect_reflect (axis leftProbe rightProbe : Fin rank → ℝ) :
    reflect axis leftProbe ⬝ᵥ reflect axis rightProbe = leftProbe ⬝ᵥ rightProbe := by
  by_cases haxis : axis ⬝ᵥ axis = 0
  · rw [eq_zero_of_selfDotProduct_eq_zero haxis, reflect_zero_axis, reflect_zero_axis]
  · simp only [reflect, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]
    rw [dotProduct_comm leftProbe axis]
    field_simp
    ring

/-! ### The standard basis vectors, read against the dot product -/

/-- The standard basis vector at a coordinate. -/
def basisVec (coord : Fin rank) : Fin rank → ℝ := fun index => if index = coord then 1 else 0

/-- A basis vector reads off one coordinate. -/
theorem basisVec_dotProduct (coord : Fin rank) (probe : Fin rank → ℝ) :
    basisVec coord ⬝ᵥ probe = probe coord := by
  classical
  rw [dotProduct]
  simp only [basisVec, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ coord probe, if_pos (Finset.mem_univ coord)]

/-- The basis vectors are orthonormal. -/
theorem basisVec_dotProduct_basisVec (leftCoord rightCoord : Fin rank) :
    basisVec leftCoord ⬝ᵥ basisVec rightCoord = if leftCoord = rightCoord then 1 else 0 := by
  rw [basisVec_dotProduct, basisVec]

/-! ### The stable Householder axis

The axis `unitNormal + sign(unitNormal pivot) * basisVec pivot` never vanishes,
thus the reflection is honest at every unit normal and the construction needs no
case analysis on degeneracy and no recursion. -/

/-- The stable sign choice at a pivot coordinate: the sign of that coordinate of
the unit normal, with zero counted positive. -/
noncomputable def stableSign (pivot : Fin rank) (unitNormal : Fin rank → ℝ) : ℝ :=
  if unitNormal pivot < 0 then -1 else 1

theorem stableSign_sq (pivot : Fin rank) (unitNormal : Fin rank → ℝ) :
    stableSign pivot unitNormal ^ 2 = 1 := by
  rw [stableSign]
  split_ifs <;> norm_num

/-- The stable sign makes the pivot coordinate nonnegative. -/
theorem stableSign_mul_nonneg (pivot : Fin rank) (unitNormal : Fin rank → ℝ) :
    0 ≤ stableSign pivot unitNormal * unitNormal pivot := by
  rw [stableSign]
  split_ifs with hsign
  · nlinarith
  · nlinarith [not_lt.mp hsign]

/-- The Householder axis that carries a unit normal onto the pivot basis
vector. -/
noncomputable def householderAxis (pivot : Fin rank) (unitNormal : Fin rank → ℝ) :
    Fin rank → ℝ :=
  unitNormal + stableSign pivot unitNormal • basisVec pivot

/-- The axis length, with the sign choice made explicit. -/
theorem householderAxis_selfDotProduct (pivot : Fin rank) {unitNormal : Fin rank → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) :
    householderAxis pivot unitNormal ⬝ᵥ householderAxis pivot unitNormal
      = 2 + 2 * (stableSign pivot unitNormal * unitNormal pivot) := by
  rw [householderAxis, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct,
    dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, hunit, basisVec_dotProduct_basisVec,
    basisVec_dotProduct, dotProduct_comm unitNormal (basisVec pivot), basisVec_dotProduct,
    if_pos rfl]
  nlinarith [stableSign_sq pivot unitNormal]

/-- **THE AXIS HAS LENGTH AT LEAST TWO.**  This is the whole point of the sign
choice: no unit normal makes the axis short, thus none makes it vanish. -/
theorem two_le_householderAxis_selfDotProduct (pivot : Fin rank) {unitNormal : Fin rank → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) :
    2 ≤ householderAxis pivot unitNormal ⬝ᵥ householderAxis pivot unitNormal := by
  have hsplit := householderAxis_selfDotProduct pivot hunit
  nlinarith [stableSign_mul_nonneg pivot unitNormal, hsplit]

/-- **THE AXIS PAIRS WITH THE NORMAL AT HALF ITS OWN LENGTH.**  Thus the
reflection scale factor at the unit normal is exactly one. -/
theorem householderAxis_dotProduct_unitNormal (pivot : Fin rank) {unitNormal : Fin rank → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) :
    2 * (householderAxis pivot unitNormal ⬝ᵥ unitNormal)
      = householderAxis pivot unitNormal ⬝ᵥ householderAxis pivot unitNormal := by
  have hleft : householderAxis pivot unitNormal ⬝ᵥ unitNormal
      = 1 + stableSign pivot unitNormal * unitNormal pivot := by
    rw [householderAxis, add_dotProduct, smul_dotProduct, smul_eq_mul, hunit,
      basisVec_dotProduct]
  rw [hleft, householderAxis_selfDotProduct pivot hunit]
  ring

/-- **THE REFLECTION CARRIES THE UNIT NORMAL ONTO THE PIVOT AXIS.**  Every other
basis vector then reflects into the normal's hyperplane. -/
theorem reflect_householderAxis_unitNormal (pivot : Fin rank) {unitNormal : Fin rank → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) :
    reflect (householderAxis pivot unitNormal) unitNormal
      = (-stableSign pivot unitNormal) • basisVec pivot := by
  have hlength : 0 < householderAxis pivot unitNormal ⬝ᵥ householderAxis pivot unitNormal := by
    have := two_le_householderAxis_selfDotProduct pivot hunit
    linarith
  have hscale : 2 * (householderAxis pivot unitNormal ⬝ᵥ unitNormal)
      / (householderAxis pivot unitNormal ⬝ᵥ householderAxis pivot unitNormal) = 1 := by
    rw [householderAxis_dotProduct_unitNormal pivot hunit]
    exact div_self (ne_of_gt hlength)
  rw [reflect, hscale, one_smul, householderAxis, neg_smul]
  abel

/-! ### The frame

The frame indices are the coordinates that miss the pivot, transported along the
shift `index -> index + 1`. That shift is injective and never hits the pivot,
which is all the frame laws read. -/

/-- The pivot coordinate of a nonempty coordinate set. -/
def pivotIndex (hpos : 0 < rank) : Fin rank := ⟨0, hpos⟩

/-- The shift that transports a frame index to a coordinate above the pivot. -/
def shiftIndex (index : Fin (rank - 1)) : Fin rank :=
  ⟨index.val + 1, by have hlt := index.isLt; omega⟩

theorem shiftIndex_ne_pivotIndex (hpos : 0 < rank) (index : Fin (rank - 1)) :
    shiftIndex index ≠ pivotIndex hpos := by
  intro hequal
  have hval : (shiftIndex index).val = (pivotIndex hpos).val := by rw [hequal]
  simp only [shiftIndex, pivotIndex] at hval
  omega

theorem shiftIndex_injective (leftIndex rightIndex : Fin (rank - 1))
    (hequal : shiftIndex leftIndex = shiftIndex rightIndex) : leftIndex = rightIndex := by
  have hval : (shiftIndex leftIndex).val = (shiftIndex rightIndex).val := by rw [hequal]
  simp only [shiftIndex] at hval
  exact Fin.ext (by omega)

/-- **THE ORTHONORMAL FRAME OF A HYPERPLANE, AT EVERY RANK.**  This discharges
`Gtz.HyperplaneFrameExists`, the Gram-Schmidt residual of the general-rank
degenerate arm, with no hypothesis and no appeal to an inner product space
structure.

The frame is the Householder image of the basis vectors that miss the pivot. It
is orthonormal because the reflection is an isometry
(`Gtz.dotProduct_reflect_reflect`), and it meets the normal because the
reflection is self-adjoint (`Gtz.dotProduct_reflect_left`) and carries the
normal onto the pivot axis. -/
theorem hyperplaneFrameExists (rank : ℕ) : HyperplaneFrameExists rank := by
  intro unitNormal hunit
  rcases Nat.eq_zero_or_pos rank with hzero | hpos
  · exfalso
    subst hzero
    rw [dotProduct, Finset.univ_eq_empty, Finset.sum_empty] at hunit
    exact absurd hunit (by norm_num)
  refine ⟨fun index => reflect (householderAxis (pivotIndex hpos) unitNormal)
    (basisVec (shiftIndex index)), ?_, ?_⟩
  · intro leftIndex rightIndex
    rw [dotProduct_reflect_reflect, basisVec_dotProduct_basisVec]
    by_cases hindex : leftIndex = rightIndex
    · rw [if_pos hindex, if_pos (by rw [hindex])]
    · rw [if_neg hindex,
        if_neg fun hshift => hindex (shiftIndex_injective leftIndex rightIndex hshift)]
  · intro index
    rw [dotProduct_reflect_left, reflect_householderAxis_unitNormal (pivotIndex hpos) hunit,
      dotProduct_smul, smul_eq_mul, basisVec_dotProduct_basisVec,
      if_neg (shiftIndex_ne_pivotIndex hpos index), mul_zero]

/-- The hyperplane frame at every rank at once, in the shape the general-rank
composition consumes. -/
theorem hyperplaneFrameExists_forall : ∀ rank : ℕ, HyperplaneFrameExists rank :=
  hyperplaneFrameExists

/-! ## Part 2: the poles carry the whole probe mass, thus one of them overshoots

The SURPLUS half of the Schur producer needs a subset whose readings against the
unit normal add up to more than one. On the degenerate branch a SINGLE label
already does it, and the proof is Parseval and nothing else. -/

/-- The Parseval identity read against one direction. -/
theorem parseval_along (design : WeightedDesign size rank) (probe : Fin rank → ℝ) :
    ∑ c, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2 = probe ⬝ᵥ probe := by
  have hform : probe ⬝ᵥ ((1 : Matrix (Fin rank) (Fin rank) ℝ) *ᵥ probe)
      = ∑ c, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2 := by
    rw [← design.isParseval]
    exact weighted_atomForm_eq design.weight design.atom probe
  rw [Matrix.one_mulVec] at hform
  exact hform.symm

/-- **THE POLES CARRY THE WHOLE PROBE MASS.**  Every label off the pole set meets
the hyperplane, thus contributes nothing. This sharpens
`Gtz.probe_mass_on_unsupported`, which spreads the same mass over all the
unsupported labels: the poles are the unsupported labels that actually carry
it. -/
theorem poleMass_eq_one (design : WeightedDesign size rank) (probe : Fin rank → ℝ) :
    ∑ c ∈ offHyperplane design probe, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
      = probe ⬝ᵥ probe := by
  classical
  rw [← parseval_along design probe]
  refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_
  have hflat : design.atom c ⬝ᵥ probe = 0 := by
    by_contra hne
    exact hc (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hne⟩)
  rw [hflat]
  ring

/-- **THE SURPLUS IS FREE ON THE DEGENERATE BRANCH.**  One label that meets the
hyperplane is enough: the weights of the remaining labels miss that one, thus
they cannot carry the whole unit of Parseval mass without some reading
overshooting one.

This discharges the surplus half of `Gtz.posDef_of_normalSurplus_hyperplaneCover`
at every size and every rank, with no predecessor rank, no primitivity and no
tie. What the degenerate arm still needs is the COVER half alone. -/
theorem exists_pole_surplus (design : WeightedDesign size rank) {unitNormal : Fin rank → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) {flatLabel : Fin size}
    (hflat : design.atom flatLabel ⬝ᵥ unitNormal = 0) :
    ∃ pole : Fin size, 1 < (design.atom pole ⬝ᵥ unitNormal) ^ 2 := by
  classical
  by_contra hnone
  push Not at hnone
  have hparseval : ∑ c, design.weight c * (design.atom c ⬝ᵥ unitNormal) ^ 2 = 1 := by
    rw [parseval_along design unitNormal, hunit]
  have hzeroTerm : design.weight flatLabel * (design.atom flatLabel ⬝ᵥ unitNormal) ^ 2 = 0 := by
    rw [hflat]
    ring
  have herase : ∑ c ∈ Finset.univ.erase flatLabel,
      design.weight c * (design.atom c ⬝ᵥ unitNormal) ^ 2 = 1 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ flatLabel), hparseval, hzeroTerm, sub_zero]
  have hbound : ∑ c ∈ Finset.univ.erase flatLabel,
      design.weight c * (design.atom c ⬝ᵥ unitNormal) ^ 2
      ≤ ∑ c ∈ Finset.univ.erase flatLabel, design.weight c := by
    refine Finset.sum_le_sum fun c _ => ?_
    nlinarith [design.weight_pos c, hnone c]
  have hweights : ∑ c ∈ Finset.univ.erase flatLabel, design.weight c
      = 1 - design.weight flatLabel := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ flatLabel), design.weight_sum_one]
  have hpos := design.weight_pos flatLabel
  rw [hweights] at hbound
  linarith [herase, hbound, hpos]

/-- **THE SURPLUS AT THE DEGENERATE BRANCH ITSELF.**  A nonzero stress supplies
the flat label, thus the pole comes for free from the branch data. -/
theorem exists_pole_surplus_of_degenerate (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ} {unitNormal : Fin rank → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) (hstressNe : stressCoeff ≠ 0)
    (hsupport : ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ unitNormal = 0) :
    ∃ pole : Fin size, 1 < (design.atom pole ⬝ᵥ unitNormal) ^ 2 := by
  obtain ⟨flatLabel, hflatLabel⟩ := Function.ne_iff.mp hstressNe
  exact exists_pole_surplus design hunit (hsupport flatLabel (by simpa using hflatLabel))

/-- A subset that holds one overshooting label overshoots. -/
theorem surplus_of_mem (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (unitNormal : Fin rank → ℝ) {pole : Fin size} (hmem : pole ∈ selected)
    (hpole : 1 < (design.atom pole ⬝ᵥ unitNormal) ^ 2) :
    1 < ∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2 := by
  have hsingle : (design.atom pole ⬝ᵥ unitNormal) ^ 2
      ≤ ∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2 :=
    Finset.single_le_sum (f := fun c => (design.atom c ⬝ᵥ unitNormal) ^ 2)
      (fun c _ => sq_nonneg _) hmem
  linarith

/-! ## Part 3: the producer route is strictly stronger than the arm

`Gtz.DegenerateHyperplaneProducer` and `Gtz.DegeneratePoleAugmentation` drop the
tie and the primitivity of the design, thus they demand a STRICTLY dominating
subset at every design of the branch. The arm demands only a parallel pair, and
a design that HAS a parallel pair satisfies the arm outright. This part measures
the difference and repairs it. -/

/-- The parallel-pair stress: one at the duplicate, the squared ratio at the
original. This is the stress `Gtz.isPrimitiveDesign_of_stressFree_general`
builds, named here because the degenerate branch consumes it. -/
noncomputable def parallelPairStress (keptLabel dropLabel : Fin size) (ratio : ℝ) :
    Fin size → ℝ :=
  fun c => (if c = dropLabel then (1 : ℝ) else 0) - (if c = keptLabel then ratio ^ 2 else 0)

theorem parallelPairStress_isStress (design : WeightedDesign size rank)
    {keptLabel dropLabel : Fin size} {ratio : ℝ}
    (hparallel : design.atom dropLabel = ratio • design.atom keptLabel) :
    (∑ c, parallelPairStress keptLabel dropLabel ratio c • atomMatrix (design.atom c)) = 0 := by
  classical
  have hdrop : atomMatrix (design.atom dropLabel)
      = ratio ^ 2 • atomMatrix (design.atom keptLabel) := by
    rw [hparallel, atomMatrix_smul]
  have hpointwise : ∀ c, parallelPairStress keptLabel dropLabel ratio c
      • atomMatrix (design.atom c)
      = (if c = dropLabel then (1 : ℝ) else 0) • atomMatrix (design.atom c)
        - (if c = keptLabel then ratio ^ 2 else 0) • atomMatrix (design.atom c) := by
    intro c
    rw [parallelPairStress, sub_smul]
  rw [Finset.sum_congr rfl fun c _ => hpointwise c, Finset.sum_sub_distrib]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_pos]
  rw [hdrop, one_smul, sub_self]

theorem parallelPairStress_ne_zero {keptLabel dropLabel : Fin size} {ratio : ℝ}
    (hdistinct : keptLabel ≠ dropLabel) :
    parallelPairStress keptLabel dropLabel ratio ≠ 0 := by
  intro hzero
  have hentry := congrFun hzero dropLabel
  rw [parallelPairStress] at hentry
  simp only [if_neg (Ne.symm hdistinct), Pi.zero_apply] at hentry
  norm_num at hentry

theorem parallelPairStress_support {keptLabel dropLabel : Fin size} {ratio : ℝ}
    {probe : Fin rank → ℝ} (design : WeightedDesign size rank)
    (hparallel : design.atom dropLabel = ratio • design.atom keptLabel)
    (hkept : design.atom keptLabel ⬝ᵥ probe = 0) :
    ∀ c, parallelPairStress keptLabel dropLabel ratio c ≠ 0 →
      design.atom c ⬝ᵥ probe = 0 := by
  intro c hc
  by_cases hdrop : c = dropLabel
  · rw [hdrop, hparallel, smul_dotProduct, smul_eq_mul, hkept, mul_zero]
  by_cases hkeptLabel : c = keptLabel
  · rw [hkeptLabel, hkept]
  · exfalso
    rw [parallelPairStress, if_neg hdrop, if_neg hkeptLabel] at hc
    norm_num at hc

/-- **EVERY PARALLEL PAIR PUTS THE DESIGN ON THE DEGENERATE BRANCH.**  At rank
two and above the duplicated direction admits a nonzero orthogonal probe, and
the parallel-pair stress is supported inside that probe's hyperplane. -/
theorem exists_coplanarStress_of_hasParallelPair (hrank : 2 ≤ rank)
    (design : WeightedDesign size rank) (hpair : HasParallelPair design) :
    ∃ (stressCoeff : Fin size → ℝ) (probe : Fin rank → ℝ),
      stressCoeff ≠ 0 ∧ probe ≠ 0
        ∧ (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0
        ∧ ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0 := by
  classical
  obtain ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩ := hpair
  obtain ⟨probe, hprobeNe, hprobeOrth⟩ := exists_ne_zero_orthogonal_of_card_lt
    (fun _ : Fin 1 => design.atom keptLabel) (Finset.univ : Finset (Fin 1))
    (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  refine ⟨parallelPairStress keptLabel dropLabel ratio, probe,
    parallelPairStress_ne_zero hdistinct, hprobeNe,
    parallelPairStress_isStress design hparallel,
    parallelPairStress_support design hparallel (hprobeOrth 0 (Finset.mem_univ 0))⟩

/-- The producer route, unpacked: on the branch data it contradicts a tie
outright. This is the body of `Gtz.degenerateArmAt_of_hyperplaneProducer`, named
so that the measurement below can read it. -/
theorem false_of_hyperplaneProducer_of_branch
    (hproducer : DegenerateHyperplaneProducer size rank) (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ} {probe : Fin rank → ℝ} (hstressNe : stressCoeff ≠ 0)
    (hprobeNe : probe ≠ 0)
    (hstress : (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0)
    (hsupport : ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0)
    (htie : IsTie design) : False := by
  have hscaled : ∀ c, stressCoeff c ≠ 0 →
      design.atom c ⬝ᵥ ((Real.sqrt (probe ⬝ᵥ probe))⁻¹ • probe) = 0 := by
    intro c hc
    rw [dotProduct_smul, smul_eq_mul, hsupport c hc, mul_zero]
  obtain ⟨selected, hcard, hsurplus, hcover⟩ := hproducer design stressCoeff _ hstressNe
    (unit_of_ne_zero probe hprobeNe) hstress hscaled
  exact htie.2 selected hcard
    (posDef_of_normalSurplus_hyperplaneCover design selected _
      (unit_of_ne_zero probe hprobeNe) hsurplus hcover)

/-- **THE DEFECT, AS A KERNEL FACT.**  The producer route forbids every tie that
carries a parallel pair, and such a tie is exactly what the arm PERMITS: the
arm's conclusion is `Gtz.HasParallelPair`, which such a design satisfies
outright. Thus `Gtz.DegenerateHyperplaneProducer` is strictly stronger than
`Gtz.DegenerateArmAt`, and any cell that carries a parallel-pair tie REFUTES it.
The same reading applies to `Gtz.DegeneratePoleAugmentation`, which produces
it. -/
theorem hyperplaneProducer_forbids_parallelPair_tie (hrank : 2 ≤ rank)
    (hproducer : DegenerateHyperplaneProducer size rank)
    (design : WeightedDesign size rank) (hpair : HasParallelPair design) : ¬ IsTie design := by
  intro htie
  obtain ⟨stressCoeff, probe, hstressNe, hprobeNe, hstress, hsupport⟩ :=
    exists_coplanarStress_of_hasParallelPair hrank design hpair
  exact false_of_hyperplaneProducer_of_branch hproducer design hstressNe hprobeNe hstress
    hsupport htie

/-- The same measurement one step earlier: the pole augmentation forbids the
parallel-pair tie too, because it produces the producer. -/
theorem poleAugmentation_forbids_parallelPair_tie (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (haugment : DegeneratePoleAugmentation size rank)
    (design : WeightedDesign size rank) (hpair : HasParallelPair design) : ¬ IsTie design :=
  hyperplaneProducer_forbids_parallelPair_tie hrank
    (degenerateHyperplaneProducer_of_augmentation hpredecessor
      (hyperplaneFrameExists rank) haugment) design hpair

/-! ### The repaired residual

Everything the branch supplies is carried: the primitivity that the arm's own
conclusion buys by contraposition, the tie, the stress, the hyperplane, and the
surplus pole that `Gtz.exists_pole_surplus_of_degenerate` produces. What is
demanded is the COVER inequality alone. -/

/-- **THE COVER RESIDUAL OF THE DEGENERATE ARM.**  A primitive tie whose stress
lies inside a hyperplane admits a card-`rank` subset that holds a given
overshooting pole and covers the hyperplane strictly.

The surplus half is not demanded, because `Gtz.surplus_of_mem` reads it off the
membership of the pole. -/
def DegenerateHyperplaneCover (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ)
      (unitNormal : Fin rank → ℝ) (pole : Fin size),
    IsPrimitiveDesign design → IsTie design → stressCoeff ≠ 0 →
    unitNormal ⬝ᵥ unitNormal = 1 →
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ unitNormal = 0) →
    1 < (design.atom pole ⬝ᵥ unitNormal) ^ 2 →
    ∃ selected : Finset (Fin size), selected.card = rank ∧ pole ∈ selected
      ∧ ∀ probe : Fin rank → ℝ, probe ⬝ᵥ unitNormal = 0 → probe ≠ 0 →
        (∑ c ∈ selected, (design.atom c ⬝ᵥ probe) * (design.atom c ⬝ᵥ unitNormal)) ^ 2
          < ((∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2) - 1)
            * ((∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)

/-- **THE DEGENERATE ARM FROM THE COVER ALONE.**  No predecessor rank, no
Gram-Schmidt residual and no surplus demand: the frame is the theorem
`Gtz.hyperplaneFrameExists`, the surplus is the theorem
`Gtz.exists_pole_surplus_of_degenerate`, and the primitivity comes free by
contraposition on the arm's own conclusion. -/
theorem degenerateArmAt_of_hyperplaneCover (hcover : DegenerateHyperplaneCover size rank) :
    DegenerateArmAt size rank := by
  intro design stressCoeff probe hstressNe hprobeNe hstress hsupport htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  have hunit := unit_of_ne_zero probe hprobeNe
  have hscaled : ∀ c, stressCoeff c ≠ 0 →
      design.atom c ⬝ᵥ ((Real.sqrt (probe ⬝ᵥ probe))⁻¹ • probe) = 0 := by
    intro c hc
    rw [dotProduct_smul, smul_eq_mul, hsupport c hc, mul_zero]
  obtain ⟨pole, hpole⟩ :=
    exists_pole_surplus_of_degenerate design hunit hstressNe hscaled
  obtain ⟨selected, hcard, hmem, hcoverFires⟩ := hcover design stressCoeff _ pole hprimitive
    htie hstressNe hunit hstress hscaled hpole
  exact htie.2 selected hcard
    (posDef_of_normalSurplus_hyperplaneCover design selected _ hunit
      (surplus_of_mem design selected _ hmem hpole) hcoverFires)

/-- **THE REPAIR IS FAITHFUL AT RANK THREE.**  The closed two-pole capstone
proves the repaired residual at the rank-three deciding cell, because a
primitive `(6,3)` design with a coplanar stress is never a tie. The refuted
producer has no such rank-three proof: it demands a strict dominator at
parallel-pair ties as well. -/
theorem degenerateHyperplaneCover_three_of_selection (hselection : TwoPoleStratumSelection 6) :
    DegenerateHyperplaneCover 6 3 := by
  intro design stressCoeff unitNormal _pole hprimitive htie hstressNe hunit hstress hsupport
    _hpole
  exfalso
  have hunitNe : unitNormal ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    exact absurd hunit (by norm_num)
  exact (isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive
    (sixThree_hasParallelPair_of_isTie_of_coplanarStress hselection design htie hstressNe
      hunitNe hstress hsupport)

/-- The arm at the rank-three deciding cell, through the repaired residual. A
third route to the closed rank-three degenerate arm, after the direct
`Gtz.thresholdDegenerateArm_three_of_selection` and the pole split
`Gtz.thresholdDegenerateArm_three_of_poleSplit`. -/
theorem thresholdDegenerateArm_three_of_cover (hselection : TwoPoleStratumSelection 6) :
    ThresholdDegenerateArm 3 :=
  degenerateArmAt_of_hyperplaneCover (degenerateHyperplaneCover_three_of_selection hselection)

/-! ## Part 4: the degenerate arm at the deciding cell, and the re-assembly

The degenerate arm now costs ONE residual and no predecessor rank. The list the
inherited map reached was `Gtz.HyperplaneFrameExists` plus
`Gtz.DegeneratePoleAugmentation` under `Gtz.GtzWeightedAll (rank - 1)`, and the
second of those is refuted at any cell that carries a parallel-pair tie
(`Gtz.poleAugmentation_forbids_parallelPair_tie`). -/

/-- Arm (iii) at the deciding cell of a rank, from the cover alone. -/
theorem thresholdDegenerateArm_of_cover (rank : ℕ)
    (hcover : DegenerateHyperplaneCover (thresholdSize rank) rank) :
    ThresholdDegenerateArm rank :=
  degenerateArmAt_of_hyperplaneCover hcover

/-- **THE THRESHOLD CELL OBLIGATION, ON FIVE RESIDUALS AND NO PREDECESSOR.**
This is the statement of `Skeleton.obligationThresholdCellHingeRankFourAndUp`
verbatim. Against
`Gtz.thresholdCellHingeRankFourAndUp_of_residuals_withPredecessorRank` it drops
one residual and the whole predecessor-rank hypothesis, because the frame is a
theorem (`Gtz.hyperplaneFrameExists`) and the surplus is a theorem
(`Gtz.exists_pole_surplus_of_degenerate`). -/
theorem thresholdCellHingeRankFourAndUp_of_repairedResiduals
    (hfreeArm : ∀ rank : ℕ, 4 ≤ rank → ThresholdStressFreeArm rank)
    (hmassGap : ∀ rank : ℕ, 4 ≤ rank → MassGapSideIsRankSized (thresholdSize rank) rank)
    (hselection : ∀ rank : ℕ, 4 ≤ rank →
      BalancedStratumSelectionAtRank (thresholdSize rank) rank)
    (hpartialArm : ∀ rank : ℕ, 4 ≤ rank →
      BalancedPartialSupportArmAt (thresholdSize rank) rank)
    (hcover : ∀ rank : ℕ, 4 ≤ rank → DegenerateHyperplaneCover (thresholdSize rank) rank) :
    ∀ rank : ℕ, 4 ≤ rank →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  refine thresholdCellHingeRankFourAndUp_of_arms hfreeArm (fun rank hrank => ?_)
    (fun rank hrank => thresholdDegenerateArm_of_cover rank (hcover rank hrank))
  exact balancedArmAt_of_residuals (hmassGap rank hrank) (hselection rank hrank)
    (hpartialArm rank hrank)

/-- **THE SUB-THRESHOLD BAND OBLIGATION, BY THE SAME REPAIR.**  The statement of
`Skeleton.obligationSubThresholdBandHinge` verbatim. -/
theorem subThresholdBandHinge_of_repairedResiduals
    (hfreeArm : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size < thresholdSize rank → StressFreeArmAt size rank)
    (hbalancedArm : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size < thresholdSize rank → BalancedArmAt size rank)
    (hcover : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size < thresholdSize rank → DegenerateHyperplaneCover size rank) :
    ∀ rank : ℕ, 3 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design :=
  subThresholdBandHinge_of_arms hfreeArm hbalancedArm
    fun rank size hrank hlow hhigh =>
      degenerateArmAt_of_hyperplaneCover (hcover rank size hrank hlow hhigh)

/-- **THE WHOLE SHARP WINDOW, WITH THE DEGENERATE ARM ON ONE RESIDUAL.**  Both
registry hinge obligations are the two ends of this window. -/
theorem sharpWindowHinge_of_repairedResiduals
    (hfreeArm : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size ≤ thresholdSize rank → StressFreeArmAt size rank)
    (hbalancedArm : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size ≤ thresholdSize rank → BalancedArmAt size rank)
    (hcover : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size ≤ thresholdSize rank → DegenerateHyperplaneCover size rank) :
    ∀ rank : ℕ, 3 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        HingeHoldsAtSize size rank :=
  sharpWindowHinge_of_arms hfreeArm hbalancedArm
    fun rank size hrank hlow hhigh =>
      degenerateArmAt_of_hyperplaneCover (hcover rank size hrank hlow hhigh)

/-! ## Part 5: the partial-support arm

`Gtz.BalancedPartialSupportArmAt` is the arm with no rank-three analogue: two
spanning sign sides and at least one label the stress misses. This part bounds
the missed labels, lifts the mass-gap law over them, and reduces the arm to two
residuals that are the exact analogues of the full-support ones. -/

/-- The three sign classes of a stress split every sum. -/
theorem sum_split_by_sign (stressCoeff : Fin n → ℝ) (summand : Fin n → ℝ) :
    ∑ c, summand c
      = (∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c), summand c)
        + (∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0), summand c)
        + ∑ c ∈ Finset.univ.filter (fun c => stressCoeff c = 0), summand c := by
  classical
  have hnot : (Finset.univ.filter fun c => ¬ (0 < stressCoeff c))
      = (Finset.univ.filter fun c => stressCoeff c < 0)
        ∪ Finset.univ.filter (fun c => stressCoeff c = 0) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, not_lt]
    constructor
    · intro hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr heq
    · rintro (hlt | heq)
      · linarith
      · linarith [heq.le, heq.ge]
  have hdisjoint : Disjoint (Finset.univ.filter fun c => stressCoeff c < 0)
      (Finset.univ.filter fun c => stressCoeff c = 0) := by
    rw [Finset.disjoint_left]
    intro c hneg hzero
    have hlt := (Finset.mem_filter.mp hneg).2
    have heq := (Finset.mem_filter.mp hzero).2
    linarith
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c => 0 < stressCoeff c) summand,
    hnot, Finset.sum_union hdisjoint, add_assoc]

/-- The three sign classes count out the whole cell. -/
theorem card_split_by_sign (stressCoeff : Fin n → ℝ) :
    (Finset.univ.filter fun c => 0 < stressCoeff c).card
        + (Finset.univ.filter fun c => stressCoeff c < 0).card
        + (Finset.univ.filter fun c => stressCoeff c = 0).card = n := by
  classical
  have hcast := sum_split_by_sign stressCoeff (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at hcast
  exact_mod_cast hcast.symm

/-- **THE MISSED LABELS ARE BOUNDED BY THE BAND WIDTH.**  Two spanning sides
carry at least `rank` labels each, thus the labels the stress misses number at
most `size - 2 * rank`. At the deciding cell that is `rank * (rank - 3) / 2`,
which is zero at rank three and positive above it. -/
theorem card_unsupported_le_of_sides (design : WeightedDesign n k)
    {stressCoeff : Fin n → ℝ}
    (hposSpans : ∀ probe : Fin k → ℝ,
      (∀ c, 0 < stressCoeff c → design.atom c ⬝ᵥ probe = 0) → probe = 0)
    (hnegSpans : ∀ probe : Fin k → ℝ,
      (∀ c, stressCoeff c < 0 → design.atom c ⬝ᵥ probe = 0) → probe = 0) :
    (Finset.univ.filter fun c => stressCoeff c = 0).card ≤ n - 2 * k := by
  have hpos := rank_le_posSideCard_of_spans design hposSpans
  have hneg := rank_le_negSideCard_of_spans design hnegSpans
  have hsum := card_split_by_sign stressCoeff
  omega

/-- The same bound at the deciding cell of a rank. -/
theorem card_unsupported_le_bandWidth (design : WeightedDesign (thresholdSize rank) rank)
    {stressCoeff : Fin (thresholdSize rank) → ℝ} (hrank : 3 ≤ rank)
    (hposSpans : ∀ probe : Fin rank → ℝ,
      (∀ c, 0 < stressCoeff c → design.atom c ⬝ᵥ probe = 0) → probe = 0)
    (hnegSpans : ∀ probe : Fin rank → ℝ,
      (∀ c, stressCoeff c < 0 → design.atom c ⬝ᵥ probe = 0) → probe = 0) :
    (Finset.univ.filter fun c => stressCoeff c = 0).card ≤ rank * (rank - 3) / 2 := by
  have hbound := card_unsupported_le_of_sides design hposSpans hnegSpans
  rw [thresholdSplitWindow rank hrank] at hbound
  exact hbound

/-- At rank four the deciding cell leaves at most TWO labels unsupported, thus
the partial-support arm there is a two-label question. -/
theorem card_unsupported_le_two_rank_four (design : WeightedDesign (thresholdSize 4) 4)
    {stressCoeff : Fin (thresholdSize 4) → ℝ}
    (hposSpans : ∀ probe : Fin 4 → ℝ,
      (∀ c, 0 < stressCoeff c → design.atom c ⬝ᵥ probe = 0) → probe = 0)
    (hnegSpans : ∀ probe : Fin 4 → ℝ,
      (∀ c, stressCoeff c < 0 → design.atom c ⬝ᵥ probe = 0) → probe = 0) :
    (Finset.univ.filter fun c => stressCoeff c = 0).card ≤ 2 := by
  have hbound := card_unsupported_le_bandWidth design (by norm_num) hposSpans hnegSpans
  norm_num at hbound
  exact hbound

/-! ### The mass gap over the missed labels

The shipped `Gtz.posDef_gap_of_stressMassGap` demands FULL support, and its
proof shows exactly why: the missed labels enter the gap with the wrong sign.
The law below carries them explicitly, thus it holds on both sub-arms and its
full-support instance is the shipped law. -/

/-- **THE MASS GAP, WITH THE MISSED LABELS PRICED IN.**  The free floor and the
bound ceiling are the shipped ones. The third clause replaces the bare
inequality `boundCeiling < freeFloor` by the demand that the gap between them
beat the Parseval mass the stress misses. -/
def HasStressMassGapOverUnsupported (design : WeightedDesign size rank)
    (stressCoeff : Fin size → ℝ) : Prop :=
  ∃ freeFloor boundCeiling : ℝ,
    (∀ c, 0 < stressCoeff c → freeFloor * stressCoeff c ≤ 1 - design.weight c)
    ∧ (∀ c, stressCoeff c < 0 → design.weight c ≤ boundCeiling * (-stressCoeff c))
    ∧ ∀ probe : Fin rank → ℝ, probe ≠ 0 →
        (∑ c ∈ Finset.univ.filter (fun c => stressCoeff c = 0),
            design.weight c * (design.atom c ⬝ᵥ probe) ^ 2)
          < (freeFloor - boundCeiling)
            * ∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
                stressCoeff c * (design.atom c ⬝ᵥ probe) ^ 2

/-- The two-frame equality, read against one direction. -/
theorem posSideForm_eq_negSideForm (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0) (probe : Fin rank → ℝ) :
    ∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
        stressCoeff c * (design.atom c ⬝ᵥ probe) ^ 2
      = ∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
          (-stressCoeff c) * (design.atom c ⬝ᵥ probe) ^ 2 := by
  have hmatrix := posSideSum_eq_negSideSum design.atom hstress
  have hleft := weighted_atomForm_eq_on (Finset.univ.filter fun c => 0 < stressCoeff c)
    stressCoeff design.atom probe
  have hright := weighted_atomForm_eq_on (Finset.univ.filter fun c => stressCoeff c < 0)
    (fun c => -stressCoeff c) design.atom probe
  rw [← hleft, ← hright, hmatrix]

/-- **THE POSITIVE SIDE STRICTLY DOMINATES, WITH OR WITHOUT FULL SUPPORT.**  The
gap along any direction is the free mass of the positive side minus the bound
mass of the negative side minus the missed mass. The first two collapse onto the
same quadratic form by the two-frame equality, thus the whole gap is
`(freeFloor - boundCeiling)` times that form minus the missed mass, which the
third clause makes positive. -/
theorem posDef_gap_posSide_of_gapOverUnsupported (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hgap : HasStressMassGapOverUnsupported design stressCoeff) :
    (subsetSum design (Finset.univ.filter fun c => 0 < stressCoeff c) - 1).PosDef := by
  classical
  obtain ⟨freeFloor, boundCeiling, hfree, hbound, hbeats⟩ := hgap
  have hsymm : (subsetSum design (Finset.univ.filter fun c => 0 < stressCoeff c) - 1)ᵀ
      = subsetSum design (Finset.univ.filter fun c => 0 < stressCoeff c) - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, transpose_subsetSum]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobeNe => ?_⟩
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, subsetSum_form, Matrix.one_mulVec]
  set posSide : Finset (Fin size) := Finset.univ.filter (fun c => 0 < stressCoeff c)
    with hposSide
  set negSide : Finset (Fin size) := Finset.univ.filter (fun c => stressCoeff c < 0)
    with hnegSide
  set zeroSide : Finset (Fin size) := Finset.univ.filter (fun c => stressCoeff c = 0)
    with hzeroSide
  have hparseval : probe ⬝ᵥ probe
      = (∑ c ∈ posSide, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2)
        + (∑ c ∈ negSide, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2)
        + ∑ c ∈ zeroSide, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2 := by
    rw [← parseval_along design probe]
    exact sum_split_by_sign stressCoeff
      (fun c => design.weight c * (design.atom c ⬝ᵥ probe) ^ 2)
  have hfreeMass : freeFloor * ∑ c ∈ posSide, stressCoeff c * (design.atom c ⬝ᵥ probe) ^ 2
      ≤ ∑ c ∈ posSide, (1 - design.weight c) * (design.atom c ⬝ᵥ probe) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have hpos : 0 < stressCoeff c := (Finset.mem_filter.mp hc).2
    nlinarith [hfree c hpos, sq_nonneg (design.atom c ⬝ᵥ probe)]
  have hboundMass : ∑ c ∈ negSide, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
      ≤ boundCeiling * ∑ c ∈ negSide, (-stressCoeff c) * (design.atom c ⬝ᵥ probe) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have hneg : stressCoeff c < 0 := (Finset.mem_filter.mp hc).2
    nlinarith [hbound c hneg, sq_nonneg (design.atom c ⬝ᵥ probe)]
  have hframes := posSideForm_eq_negSideForm design hstress probe
  rw [← hposSide, ← hnegSide] at hframes
  have hbeatsFires := hbeats probe hprobeNe
  rw [← hframes] at hboundMass
  have hexpand : (freeFloor - boundCeiling)
        * ∑ c ∈ posSide, stressCoeff c * (design.atom c ⬝ᵥ probe) ^ 2
      = freeFloor * ∑ c ∈ posSide, stressCoeff c * (design.atom c ⬝ᵥ probe) ^ 2
        - boundCeiling * ∑ c ∈ posSide, stressCoeff c * (design.atom c ⬝ᵥ probe) ^ 2 := by
    ring
  have hposExpand : ∑ c ∈ posSide, (design.atom c ⬝ᵥ probe) ^ 2
      = (∑ c ∈ posSide, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2)
        + ∑ c ∈ posSide, (1 - design.weight c) * (design.atom c ⬝ᵥ probe) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hposExpand, hparseval]
  linarith [hfreeMass, hboundMass, hbeatsFires, hexpand]

/-- **THE GENERALIZATION IS FAITHFUL.**  At full support the missed labels are
gone and the positive side's form is positive by spanning, thus the shipped mass
gap gives the general one. -/
theorem hasStressMassGapOverUnsupported_of_massGap (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ} (hfull : ∀ c, stressCoeff c ≠ 0)
    (hposSpans : ∀ probe : Fin rank → ℝ,
      (∀ c, 0 < stressCoeff c → design.atom c ⬝ᵥ probe = 0) → probe = 0)
    (hgap : HasStressMassGap design stressCoeff) :
    HasStressMassGapOverUnsupported design stressCoeff := by
  classical
  obtain ⟨freeFloor, boundCeiling, hfree, hbound, hstrict⟩ := hgap
  refine ⟨freeFloor, boundCeiling, hfree, hbound, fun probe hprobeNe => ?_⟩
  have hempty : (Finset.univ.filter fun c => stressCoeff c = 0) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun c hc => ?_
    exact hfull c (Finset.mem_filter.mp hc).2
  have hposForm : 0 < ∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
      stressCoeff c * (design.atom c ⬝ᵥ probe) ^ 2 := by
    have hposDef := posDef_posSideSum_of_spans design.atom hposSpans
    have hvalue := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 (x := probe) hprobeNe
    rw [star_trivial, weighted_atomForm_eq_on] at hvalue
    exact hvalue
  rw [hempty, Finset.sum_empty]
  nlinarith [hposForm, hstrict]

/-! ### The two residuals of the partial-support arm -/

/-- The partial-support analogue of `Gtz.MassGapSideIsRankSized`: when the
generalized mass gap fires, the strictly dominating set it returns is
rank-sized. The full-support half of this question is the sibling residual
`Gtz.MassGapSideIsRankSized`, and the obstruction is the same one -- the firing
returns the whole positive side. -/
def PartialSupportSideIsRankSized (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ),
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    HasStressMassGapOverUnsupported design stressCoeff →
    ∃ dominating : Finset (Fin size), dominating.card = rank
      ∧ (subsetSum design dominating - 1).PosDef

/-- Whenever the positive side is rank-sized the residual is discharged. -/
theorem partialSupportSideIsRankSized_of_posSideCard (size rank : ℕ)
    (hcard : ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ),
      (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
        (Finset.univ.filter fun c => 0 < stressCoeff c).card = rank) :
    PartialSupportSideIsRankSized size rank :=
  fun design stressCoeff hstress hgap =>
    ⟨Finset.univ.filter fun c => 0 < stressCoeff c, hcard design stressCoeff hstress,
      posDef_gap_posSide_of_gapOverUnsupported design hstress hgap⟩

/-- The partial-support analogue of `Gtz.BalancedStratumSelectionAtRank`. Every
unconditional firing available on this branch is already spent: the two
orientations of the generalized mass gap and the free-mass budget at every
card-`rank` subset. -/
def PartialSupportSelectionAtRank (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ),
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    stressCoeff ≠ 0 →
    (∃ c, stressCoeff c = 0) →
    (∀ probe : Fin rank → ℝ,
      (∀ c, 0 < stressCoeff c → design.atom c ⬝ᵥ probe = 0) → probe = 0) →
    (∀ probe : Fin rank → ℝ,
      (∀ c, stressCoeff c < 0 → design.atom c ⬝ᵥ probe = 0) → probe = 0) →
    IsPrimitiveDesign design →
    ¬ HasStressMassGapOverUnsupported design stressCoeff →
    ¬ HasStressMassGapOverUnsupported design (-stressCoeff) →
    (∀ selected : Finset (Fin size), selected.card = rank →
      ¬ HasFreeMassBudget design selected) →
    ∃ dominating : Finset (Fin size), dominating.card = rank
      ∧ (subsetSum design dominating - 1).PosDef

/-- **THE PARTIAL-SUPPORT ARM FROM ITS TWO RESIDUALS.**  The shape is the
full-support one (`Gtz.balancedFullSupportArmAt_of_selection`), with the
generalized mass gap in place of the shipped one. Thus the arm with no
rank-three analogue is decomposed exactly like the arm that has one. -/
theorem balancedPartialSupportArmAt_of_residuals
    (hsided : PartialSupportSideIsRankSized size rank)
    (hselection : PartialSupportSelectionAtRank size rank) :
    BalancedPartialSupportArmAt size rank := by
  classical
  intro design stressCoeff hstressNe hstress hunsupported hposSpans hnegSpans htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  have hnostrict := htie.2
  by_cases hgapPos : HasStressMassGapOverUnsupported design stressCoeff
  · obtain ⟨dominating, hcard, hposDef⟩ := hsided design stressCoeff hstress hgapPos
    exact hnostrict dominating hcard hposDef
  by_cases hgapNeg : HasStressMassGapOverUnsupported design (-stressCoeff)
  · obtain ⟨dominating, hcard, hposDef⟩ := hsided design (-stressCoeff)
      (stress_of_neg_stress hstress) hgapNeg
    exact hnostrict dominating hcard hposDef
  by_cases hbudget : ∀ selected : Finset (Fin size), selected.card = rank →
      ¬ HasFreeMassBudget design selected
  · obtain ⟨dominating, hcard, hposDef⟩ := hselection design stressCoeff hstress hstressNe
      hunsupported hposSpans hnegSpans hprimitive hgapPos hgapNeg hbudget
    exact hnostrict dominating hcard hposDef
  · push Not at hbudget
    obtain ⟨selected, hcard, hbudgetFires⟩ := hbudget
    exact hnostrict selected hcard
      (posDef_gap_of_freeMassBudget design selected hbudgetFires.1 hbudgetFires.2)

/-- **THE WHOLE BALANCED ARM ON FOUR RESIDUALS.**  The full-support half through
the shipped pair, the partial-support half through the pair above. -/
theorem balancedArmAt_of_bothResiduals
    (hmassGap : MassGapSideIsRankSized size rank)
    (hselection : BalancedStratumSelectionAtRank size rank)
    (hpartialSided : PartialSupportSideIsRankSized size rank)
    (hpartialSelection : PartialSupportSelectionAtRank size rank) :
    BalancedArmAt size rank :=
  balancedArmAt_of_residuals hmassGap hselection
    (balancedPartialSupportArmAt_of_residuals hpartialSided hpartialSelection)

/-- The partial-support residuals are not needed at rank three: the sub-arm is
empty there (`Gtz.balancedPartialSupportArm_sixThree`), because the two spanning
sides already fill the deciding cell. -/
theorem balancedArmAt_three_of_fullSupportResiduals :
    ThresholdBalancedArm 3 :=
  thresholdBalancedArm_three_of_residuals

/-- **THE FULL RESIDUAL LIST AT RANK FOUR AND UP, AFTER THIS MODULE.**  Six
Props and no predecessor cell of either kind:

- `Gtz.ThresholdStressFreeArm` -- the basis arm, the rank-three frontier one
  rank up
- `Gtz.MassGapSideIsRankSized` -- the full-support positive side is too big
- `Gtz.BalancedStratumSelectionAtRank` -- the verbatim lift of the closed
  rank-three selection
- `Gtz.PartialSupportSideIsRankSized` -- the same question on the missed-label
  branch
- `Gtz.PartialSupportSelectionAtRank` -- the selection on that branch
- `Gtz.DegenerateHyperplaneCover` -- the cover inequality at a subset holding a
  surplus pole.

Against the inherited list this trades `Gtz.BalancedPartialSupportArmAt` for two
named Props of the shape the closed rank-three chain already has, and it
replaces `Gtz.HyperplaneFrameExists` plus `Gtz.DegeneratePoleAugmentation` under
`Gtz.GtzWeightedAll (rank - 1)` by one Prop and no hypothesis. -/
theorem thresholdCellHingeRankFourAndUp_of_fullResidualList
    (hfreeArm : ∀ rank : ℕ, 4 ≤ rank → ThresholdStressFreeArm rank)
    (hmassGap : ∀ rank : ℕ, 4 ≤ rank → MassGapSideIsRankSized (thresholdSize rank) rank)
    (hselection : ∀ rank : ℕ, 4 ≤ rank →
      BalancedStratumSelectionAtRank (thresholdSize rank) rank)
    (hpartialSided : ∀ rank : ℕ, 4 ≤ rank →
      PartialSupportSideIsRankSized (thresholdSize rank) rank)
    (hpartialSelection : ∀ rank : ℕ, 4 ≤ rank →
      PartialSupportSelectionAtRank (thresholdSize rank) rank)
    (hcover : ∀ rank : ℕ, 4 ≤ rank → DegenerateHyperplaneCover (thresholdSize rank) rank) :
    ∀ rank : ℕ, 4 ≤ rank →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  refine thresholdCellHingeRankFourAndUp_of_repairedResiduals hfreeArm hmassGap hselection
    (fun rank hrank => ?_) hcover
  exact balancedPartialSupportArmAt_of_residuals (hpartialSided rank hrank)
    (hpartialSelection rank hrank)

/-! ## Part 6: the ledger of the repair

Three readings that make the repair auditable: the surplus pole is one of the
unsupported labels the branch already names, the rank-three assembly comes back
out of the repaired chain, and the refuted residual is refuted by a named
configuration. -/

/-- **THE SURPLUS POLE IS UNSUPPORTED.**  A label the stress touches meets the
hyperplane, thus its reading is zero and cannot overshoot. So the pole that
`Gtz.exists_pole_surplus_of_degenerate` produces is one of the labels the stress
misses, exactly the set `Gtz.offHyperplane_subset_unsupported` describes. -/
theorem surplusPole_unsupported (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ} {unitNormal : Fin rank → ℝ}
    (hsupport : ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ unitNormal = 0)
    {pole : Fin size} (hpole : 1 < (design.atom pole ⬝ᵥ unitNormal) ^ 2) :
    stressCoeff pole = 0 := by
  by_contra hne
  rw [hsupport pole hne] at hpole
  norm_num at hpole

/-- The surplus pole is a pole. -/
theorem surplusPole_mem_offHyperplane (design : WeightedDesign size rank)
    {unitNormal : Fin rank → ℝ} {pole : Fin size}
    (hpole : 1 < (design.atom pole ⬝ᵥ unitNormal) ^ 2) :
    pole ∈ offHyperplane design unitNormal := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ pole, fun hzero => ?_⟩
  rw [hzero] at hpole
  norm_num at hpole

/-- **THE DEGENERATE BRANCH ALWAYS CARRIES A SURPLUS POLE.**  The combined
reading: the branch data alone produces a label that is unsupported, off the
hyperplane, and overshooting. At rank three the tree bounds the poles by TWO
(`Gtz.sixThree_offPlaneCard_le_two_of_coplanarStress`), thus this pole is one of
the two the two-pole capstone selects among. -/
theorem exists_surplusPole_unsupported (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ} {unitNormal : Fin rank → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) (hstressNe : stressCoeff ≠ 0)
    (hsupport : ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ unitNormal = 0) :
    ∃ pole : Fin size, stressCoeff pole = 0 ∧ pole ∈ offHyperplane design unitNormal
      ∧ 1 < (design.atom pole ⬝ᵥ unitNormal) ^ 2 := by
  obtain ⟨pole, hpole⟩ := exists_pole_surplus_of_degenerate design hunit hstressNe hsupport
  exact ⟨pole, surplusPole_unsupported design hsupport hpole,
    surplusPole_mem_offHyperplane design hpole, hpole⟩

/-- **THE REPAIRED CHAIN REPRODUCES THE RANK-THREE ASSEMBLY.**  The hinge at the
rank-three deciding cell comes back out of the tree's own three inputs, with the
degenerate arm routed through the repaired cover residual rather than through
the refuted producer. This is the check that the repair is a lift of the closed
rank-three branch and not a different decomposition. -/
theorem thresholdArms_rank_three_faithful_repaired
    (hselection : TwoPoleStratumSelection 6) (hbalanced : BalancedStratumCapstone)
    (hstressFreeArm : StressFreeHingeHoldsSixThree) :
    HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_thresholdCell_of_arms 3 hstressFreeArm
    (thresholdBalancedArm_three_of_capstone hbalanced)
    (thresholdDegenerateArm_three_of_cover hselection)

/-- **THE REFUTATION, CONDITIONAL ON A NAMED CONFIGURATION.**  A cell that
carries a tie with a parallel pair refutes `Gtz.DegenerateHyperplaneProducer`
outright, and thus refutes `Gtz.DegeneratePoleAugmentation` under the
predecessor rank. The repaired `Gtz.DegenerateHyperplaneCover` is untouched by
such a configuration, because a design with a parallel pair is not primitive. -/
theorem parallelPairTie_refutes_hyperplaneProducer (hrank : 2 ≤ rank)
    (design : WeightedDesign size rank) (hpair : HasParallelPair design)
    (htie : IsTie design) : ¬ DegenerateHyperplaneProducer size rank :=
  fun hproducer =>
    hyperplaneProducer_forbids_parallelPair_tie hrank hproducer design hpair htie

/-- The same refutation one step earlier, at the pole augmentation. -/
theorem parallelPairTie_refutes_poleAugmentation (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    (hpair : HasParallelPair design) (htie : IsTie design) :
    ¬ DegeneratePoleAugmentation size rank :=
  fun haugment =>
    poleAugmentation_forbids_parallelPair_tie hrank hpredecessor haugment design hpair htie

/-- A design with a parallel pair is not primitive, thus the repaired residual
says nothing about it. This is the whole difference between the two Props. -/
theorem not_isPrimitiveDesign_of_hasParallelPair (design : WeightedDesign size rank)
    (hpair : HasParallelPair design) : ¬ IsPrimitiveDesign design :=
  fun hprimitive => (isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive hpair

/-- **THE PARTIAL-SUPPORT ARM IS THE ONLY ARM WITH NO RANK-THREE CONTENT.**  Its
missed-label count is bounded by the band width, which is zero at rank three and
positive at rank four and up (`Gtz.pos_thresholdSplitWindow`). The degenerate
arm and the full-support arm both have closed rank-three instances. -/
theorem partialSupportArm_bandWidth_reading (rank : ℕ) (hrank : 4 ≤ rank) :
    thresholdSize 3 - 2 * 3 = 0 ∧ 0 < thresholdSize rank - 2 * rank :=
  ⟨by rw [thresholdSize_three], pos_thresholdSplitWindow rank hrank⟩

/-! ## Part 7: the refutation, unconditional

The tree already carries the configuration that decides the two inherited
degenerate residuals. `Gtz.sixSplitDiamondDesign` is the five-atom diamond with
one atom split into two parallel copies. It is a TIE
(`Gtz.sixSplitDiamondDesign_isTie`) and it CARRIES A PARALLEL PAIR
(`Gtz.sixSplitDiamondDesign_hasParallelPair`). Both halves are kernel facts, and
together they refute the producer at the rank-three deciding cell. -/

/-- **THE INHERITED PRODUCER RESIDUAL IS FALSE AT THE RANK-THREE DECIDING
CELL.**  `Gtz.DegenerateHyperplaneProducer 6 3` demands a strictly dominating
triple at every `(6,3)` design whose stress lies in a plane. The split diamond
is such a design, and it is a tie, thus it has no strictly dominating triple at
all. -/
theorem not_degenerateHyperplaneProducer_six_three : ¬ DegenerateHyperplaneProducer 6 3 :=
  parallelPairTie_refutes_hyperplaneProducer (by norm_num) sixSplitDiamondDesign
    sixSplitDiamondDesign_hasParallelPair sixSplitDiamondDesign_isTie

/-- **THE INHERITED POLE AUGMENTATION IS FALSE AT THE SAME CELL.**  The rank-down
composition `Gtz.degenerateHyperplaneProducer_of_augmentation` takes it to the
producer, the frame is the theorem `Gtz.hyperplaneFrameExists`, and the
predecessor rank is the theorem `Gtz.gtz_rank_two`. So nothing in the chain is
assumed, and the augmentation itself is what is false. -/
theorem not_degeneratePoleAugmentation_six_three : ¬ DegeneratePoleAugmentation 6 3 :=
  parallelPairTie_refutes_poleAugmentation (by norm_num) gtz_rank_two sixSplitDiamondDesign
    sixSplitDiamondDesign_hasParallelPair sixSplitDiamondDesign_isTie

/-- The split diamond is not primitive, thus the repaired residual says nothing
about it. This is why the same configuration does not touch
`Gtz.DegenerateHyperplaneCover`. -/
theorem not_isPrimitiveDesign_sixSplitDiamondDesign :
    ¬ IsPrimitiveDesign sixSplitDiamondDesign :=
  not_isPrimitiveDesign_of_hasParallelPair sixSplitDiamondDesign
    sixSplitDiamondDesign_hasParallelPair

/-- **THE REPAIRED RESIDUAL IS TRUE AT THE SAME CELL, UNCONDITIONALLY.**  The
two-pole capstone is closed in the tree, thus the repaired cover holds at
`(6,3)` with no hypothesis. Against
`Gtz.not_degenerateHyperplaneProducer_six_three` this is the whole content of
the repair: at one and the same cell the inherited residual is FALSE and the
repaired one is a THEOREM. -/
theorem degenerateHyperplaneCover_six_three : DegenerateHyperplaneCover 6 3 :=
  degenerateHyperplaneCover_three_of_selection twoPoleStratumSelection_six_unconditional

/-- The rank-three degenerate arm, unconditionally, through the repaired
route. -/
theorem thresholdDegenerateArm_three : ThresholdDegenerateArm 3 :=
  degenerateArmAt_of_hyperplaneCover degenerateHyperplaneCover_six_three

/-- **THE TWO VERDICTS SIDE BY SIDE.**  One kernel statement that records the
whole finding of this module about the degenerate arm. -/
theorem degenerate_residual_verdict_six_three :
    ¬ DegenerateHyperplaneProducer 6 3 ∧ ¬ DegeneratePoleAugmentation 6 3
      ∧ DegenerateHyperplaneCover 6 3 ∧ ThresholdDegenerateArm 3 :=
  ⟨not_degenerateHyperplaneProducer_six_three, not_degeneratePoleAugmentation_six_three,
    degenerateHyperplaneCover_six_three, thresholdDegenerateArm_three⟩

end Gtz

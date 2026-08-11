/-
# Zero leak forces an atom dependency

A tight direction of a chart block satisfies `W v = value * v` only ON its block; the
coordinates OFF the block are the LEAK, and `Gtz.IsChartStationaryData.tightDir_isTight`
says so in its own docstring ("Nothing is asserted about the coordinates OFF the subset,
where the ambient product is generally nonzero").  This file settles what happens when
the leak VANISHES, at every size and rank, in ONE statement and with NO case split.

## The theorem

`Gtz.sum_smul_atom_eq_zero_of_chartStationaryGap_mulVec_eq_smul`:

    W *ᵥ v = value • v   (the GLOBAL equation, i.e. zero leak)
      ⟹  ∑ c, ((1 - value - t c) * √(t c) * v c) • a c = 0.

So the atoms sitting on the support of `v` are LINEARLY DEPENDENT, with an explicit
dependency, and the coefficient `1 - value - t c` is strictly positive whenever the
value is negative — which is the only regime a counterexample can occupy.

The proof is two steps and neither is a case analysis.

* THE SHIFT.  `w := v - P *ᵥ v` lies in `ker P` by IDEMPOTENCE alone, and the global
  equation evaluates it coordinatewise as `w c = (1 - value - t c) * v c`, so `w` has
  the SAME support as `v` once the factor is nonzero.
* THE KERNEL IS A DEPENDENCY.  `P = V Vᵀ` with `V = Gtz.scaledAtomRows`, so
  `P *ᵥ w = 0` forces `Vᵀ *ᵥ w = 0` — the squared length of `Vᵀ *ᵥ w` IS `w ⬝ᵥ (P *ᵥ w)`
  — and `Vᵀ *ᵥ w` is exactly the vector `∑ c, (√(t c) * w c) • a c`.

## What it gives at a support of size two, and the converse

At support two the dependency is a PARALLEL PAIR
(`Gtz.hasParallelPair_of_zeroLeak_on_support_pair`), which a `Gtz.SixThreeCrux` forbids
by its own field.  The hypothesis is NOT vacuous:
`Gtz.exists_projectionOfDesign_mulVec_eq_zero_on_support_pair_of_parallel` is the exact
converse and builds a two-supported kernel vector out of any parallel pair, so
`Gtz.hasParallelPair_iff_exists_kernel_on_support_pair` is an EQUIVALENCE.

## Scope, stated rather than implied

The kernel-vector layer is unconditional at every size and rank.  The zero-leak layer
needs `value + t c ≠ 1`, which is free at a negative value and is stated as a hypothesis
rather than assumed.  Nothing here needs the multiplier assembly, the diagonal law or
the commutation law, so it composes with `Gtz.IsChartStationaryData` without consuming
any of its first-order content.

MEASURED, OUTSIDE THE KERNEL, AND IT BOUNDS WHAT THIS FILE CAN BE ABOUT: across the 84
active blocks of the eight landed fixtures — `Gtz.tetraDesign`, `Gtz.splitTetraDesign`
at four parameter pairs, `Gtz.nonUniformLeverageTieDesign`, and the two bundled cycles
of `Gtz.Design.EqualityLocus` — NO active tight direction has zero leak, and every tight
support has size exactly three.  That is forced: an active block at a nonnegative value
has `Gram_C ⪰ I`, hence nonsingular, hence independent, so the dependency below cannot
occur.  At a negative value the same reading against the landed weight floor
`Gtz.weight_ge_neg_value_of_isChartStationaryData` leaves only the exact-equality
stratum `t c = -value`.
-/

import Mathlib
import Gtz.Quantitative.SixThreeCrux

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The kernel of the projection form IS an atom dependency -/

/-- A two-supported family of scalars collapses its sum to two terms. -/
theorem sum_smul_eq_pair_of_support {carrier : Type*} [AddCommMonoid carrier]
    [Module ℝ carrier] (coefficient : Fin size → ℝ) (vector : Fin size → carrier)
    {firstLabel secondLabel : Fin size} (hdistinct : firstLabel ≠ secondLabel)
    (hsupport : ∀ atomIndex, atomIndex ≠ firstLabel → atomIndex ≠ secondLabel →
      coefficient atomIndex = 0) :
    ∑ atomIndex, coefficient atomIndex • vector atomIndex
      = coefficient firstLabel • vector firstLabel
        + coefficient secondLabel • vector secondLabel := by
  classical
  have hreduce : ∑ atomIndex ∈ ({firstLabel, secondLabel} : Finset (Fin size)),
      coefficient atomIndex • vector atomIndex
      = ∑ atomIndex, coefficient atomIndex • vector atomIndex :=
    Finset.sum_subset (Finset.subset_univ _) (by
      intro atomIndex _ hnotmem
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnotmem
      rw [hsupport atomIndex hnotmem.1 hnotmem.2, zero_smul])
  rw [← hreduce, Finset.sum_pair hdistinct]

/-- **The scaled frame applied to an index vector IS the atom combination.**  The `c`-th
row of `Gtz.scaledAtomRows` is `√(t c) • a c`, so `Vᵀ *ᵥ w = ∑ c, (√(t c) * w c) • a c`. -/
theorem transposeScaledAtomRows_mulVec_eq_sum (design : WeightedDesign size rank)
    (direction : Fin size → ℝ) :
    (scaledAtomRows design)ᵀ *ᵥ direction
      = ∑ atomIndex, (Real.sqrt (design.weight atomIndex) * direction atomIndex)
          • design.atom atomIndex := by
  funext coord
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, scaledAtomRows,
    Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun atomIndex _ => by ring

/-- **The projection form and the scaled frame have the same kernel.**  `P = V Vᵀ`, so
`w ⬝ᵥ (P *ᵥ w)` is the squared length of `Vᵀ *ᵥ w`; a vector killed by `P` is therefore
killed by `Vᵀ`.  Unconditional, any size and rank. -/
theorem transposeScaledAtomRows_mulVec_eq_zero_of_projectionOfDesign_mulVec_eq_zero
    (design : WeightedDesign size rank) {direction : Fin size → ℝ}
    (hkernel : projectionOfDesign design *ᵥ direction = 0) :
    (scaledAtomRows design)ᵀ *ᵥ direction = 0 := by
  have hsquare : direction ⬝ᵥ (projectionOfDesign design *ᵥ direction)
      = ((scaledAtomRows design)ᵀ *ᵥ direction) ⬝ᵥ ((scaledAtomRows design)ᵀ *ᵥ direction) := by
    rw [projectionOfDesign, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose]
  rw [hkernel, dotProduct_zero] at hsquare
  exact dotProduct_self_eq_zero.mp hsquare.symm

/-- **A kernel vector of the projection form is a linear dependency among the atoms.**
Unconditional, any size and rank. -/
theorem sum_smul_atom_eq_zero_of_projectionOfDesign_mulVec_eq_zero
    (design : WeightedDesign size rank) {direction : Fin size → ℝ}
    (hkernel : projectionOfDesign design *ᵥ direction = 0) :
    ∑ atomIndex, (Real.sqrt (design.weight atomIndex) * direction atomIndex)
        • design.atom atomIndex = 0 := by
  rw [← transposeScaledAtomRows_mulVec_eq_sum design direction]
  exact transposeScaledAtomRows_mulVec_eq_zero_of_projectionOfDesign_mulVec_eq_zero
    design hkernel

/-- **Conversely, an atom dependency is a kernel vector.** -/
theorem projectionOfDesign_mulVec_eq_zero_of_sum_smul_atom_eq_zero
    (design : WeightedDesign size rank) {direction : Fin size → ℝ}
    (hdependency : ∑ atomIndex, (Real.sqrt (design.weight atomIndex) * direction atomIndex)
      • design.atom atomIndex = 0) :
    projectionOfDesign design *ᵥ direction = 0 := by
  have hframe : (scaledAtomRows design)ᵀ *ᵥ direction = 0 := by
    rw [transposeScaledAtomRows_mulVec_eq_sum design direction]; exact hdependency
  rw [projectionOfDesign, ← Matrix.mulVec_mulVec, hframe, Matrix.mulVec_zero]

/-! ## Support two: the dependency is a parallel pair, and conversely -/

/-- **A two-supported kernel vector of the projection form is a parallel pair.**  The
dependency has exactly two nonzero coefficients, so one atom is a multiple of the
other.  Unconditional, any size and rank. -/
theorem hasParallelPair_of_projectionOfDesign_mulVec_eq_zero_on_support_pair
    (design : WeightedDesign size rank) {direction : Fin size → ℝ}
    (hkernel : projectionOfDesign design *ᵥ direction = 0)
    {firstLabel secondLabel : Fin size} (hdistinct : firstLabel ≠ secondLabel)
    (hsecondNonzero : direction secondLabel ≠ 0)
    (hsupport : ∀ atomIndex, atomIndex ≠ firstLabel → atomIndex ≠ secondLabel →
      direction atomIndex = 0) :
    HasParallelPair design := by
  classical
  have hdependency := sum_smul_atom_eq_zero_of_projectionOfDesign_mulVec_eq_zero
    design hkernel
  rw [sum_smul_eq_pair_of_support _ _ hdistinct
    (fun atomIndex hfirst hsecond => by rw [hsupport atomIndex hfirst hsecond, mul_zero])]
    at hdependency
  have hfirstPos : 0 < Real.sqrt (design.weight firstLabel) :=
    Real.sqrt_pos.mpr (design.weight_pos firstLabel)
  have hsecondPos : 0 < Real.sqrt (design.weight secondLabel) :=
    Real.sqrt_pos.mpr (design.weight_pos secondLabel)
  have hsecondCoefficient :
      Real.sqrt (design.weight secondLabel) * direction secondLabel ≠ 0 :=
    mul_ne_zero (ne_of_gt hsecondPos) hsecondNonzero
  refine ⟨firstLabel, secondLabel,
    -((Real.sqrt (design.weight firstLabel) * direction firstLabel)
      / (Real.sqrt (design.weight secondLabel) * direction secondLabel)),
    hdistinct, ?_⟩
  funext coord
  have hentry := congrFun hdependency coord
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hentry
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linarith [hentry]

/-- **THE CONVERSE, so the hypothesis above is not vacuous.**  Every parallel pair with
a nonzero ratio produces a two-supported kernel vector of the projection form. -/
theorem exists_projectionOfDesign_mulVec_eq_zero_on_support_pair_of_parallel
    (design : WeightedDesign size rank) {firstLabel secondLabel : Fin size}
    (hdistinct : firstLabel ≠ secondLabel) {ratio : ℝ} (hratio : ratio ≠ 0)
    (hparallel : design.atom secondLabel = ratio • design.atom firstLabel) :
    ∃ direction : Fin size → ℝ,
      projectionOfDesign design *ᵥ direction = 0
        ∧ direction firstLabel ≠ 0 ∧ direction secondLabel ≠ 0
        ∧ ∀ atomIndex, atomIndex ≠ firstLabel → atomIndex ≠ secondLabel →
            direction atomIndex = 0 := by
  classical
  set firstRoot := Real.sqrt (design.weight firstLabel) with hfirstRoot
  set secondRoot := Real.sqrt (design.weight secondLabel) with hsecondRoot
  have hfirstPos : 0 < firstRoot := Real.sqrt_pos.mpr (design.weight_pos firstLabel)
  have hsecondPos : 0 < secondRoot := Real.sqrt_pos.mpr (design.weight_pos secondLabel)
  refine ⟨fun atomIndex =>
      if atomIndex = firstLabel then ratio * secondRoot
      else if atomIndex = secondLabel then -firstRoot else 0, ?_, ?_, ?_, ?_⟩
  · refine projectionOfDesign_mulVec_eq_zero_of_sum_smul_atom_eq_zero design ?_
    rw [sum_smul_eq_pair_of_support _ _ hdistinct
      (fun atomIndex hfirst hsecond => by simp [hfirst, hsecond])]
    rw [if_pos rfl, if_neg hdistinct.symm, if_pos rfl, hparallel]
    funext coord
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring
  · dsimp only
    rw [if_pos rfl]
    exact mul_ne_zero hratio (ne_of_gt hsecondPos)
  · dsimp only
    rw [if_neg hdistinct.symm, if_pos rfl]
    exact neg_ne_zero.mpr (ne_of_gt hfirstPos)
  · intro atomIndex hfirst hsecond
    simp [hfirst, hsecond]

/-- **The two readings agree.**  A design has a parallel pair exactly when its
projection form has a kernel vector supported on two labels. -/
theorem hasParallelPair_iff_exists_kernel_on_support_pair
    (design : WeightedDesign size rank)
    (hatomNonzero : ∀ atomIndex, design.atom atomIndex ≠ 0) :
    HasParallelPair design ↔
      ∃ (direction : Fin size → ℝ) (firstLabel secondLabel : Fin size),
        firstLabel ≠ secondLabel
          ∧ projectionOfDesign design *ᵥ direction = 0
          ∧ direction firstLabel ≠ 0 ∧ direction secondLabel ≠ 0
          ∧ ∀ atomIndex, atomIndex ≠ firstLabel → atomIndex ≠ secondLabel →
              direction atomIndex = 0 := by
  constructor
  · rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
    have hratio : ratio ≠ 0 := by
      intro hzero
      exact hatomNonzero dropLabel (by rw [hparallel, hzero, zero_smul])
    obtain ⟨direction, hkernel, hfirst, hsecond, hsupport⟩ :=
      exists_projectionOfDesign_mulVec_eq_zero_on_support_pair_of_parallel design
        hdistinct hratio hparallel
    exact ⟨direction, keptLabel, dropLabel, hdistinct, hkernel, hfirst, hsecond, hsupport⟩
  · rintro ⟨direction, firstLabel, secondLabel, hdistinct, hkernel, hfirst, hsecond,
      hsupport⟩
    exact hasParallelPair_of_projectionOfDesign_mulVec_eq_zero_on_support_pair design
      hkernel hdistinct hsecond hsupport

/-! ## The shift: zero leak lands in the kernel with the same support -/

/-- **The shifted vector lies in the kernel of the chart.**  `w := v - P v` is killed by
`P` by IDEMPOTENCE alone -- no stationarity, no design. -/
theorem projection_mulVec_sub_projection_mulVec_eq_zero
    {projection : Matrix (Fin size) (Fin size) ℝ}
    (hidempotent : projection * projection = projection) (direction : Fin size → ℝ) :
    projection *ᵥ (direction - projection *ᵥ direction) = 0 := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hidempotent, sub_self]

/-- **Zero leak evaluates the shift coordinatewise.**  If the chart gap sends `v` to
`value • v` on the WHOLE index set, then `(v - P v) c = (1 - value - t c) * v c`. -/
theorem sub_projection_mulVec_apply_of_chartStationaryGap_mulVec_eq_smul
    {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ} {value : ℝ}
    {direction : Fin size → ℝ}
    (hzeroLeak : chartStationaryGap projection weight *ᵥ direction = value • direction)
    (atomIndex : Fin size) :
    (direction - projection *ᵥ direction) atomIndex
      = (1 - value - weight atomIndex) * direction atomIndex := by
  have hentry : (projection *ᵥ direction) atomIndex
      - weight atomIndex * direction atomIndex = value * direction atomIndex := by
    have hgap := hzeroLeak
    rw [chartStationaryGap, Matrix.sub_mulVec] at hgap
    have hcoord := congrFun hgap atomIndex
    simpa [Matrix.mulVec_diagonal] using hcoord
  simp only [Pi.sub_apply]
  linarith [hentry]

/-! ## The headline: zero leak forces an atom dependency, with no case split -/

/-- **ZERO LEAK FORCES A LINEAR DEPENDENCY AMONG THE ATOMS ON THE SUPPORT.**

If the chart gap of `Gtz.projectionOfDesign` sends `v` to `value • v` on the WHOLE index
set -- that is, if the leak off every block vanishes -- then

    ∑ c, ((1 - value - t c) * √(t c) * v c) • a c = 0.

The coefficient at `c` vanishes exactly when `v c = 0` or `value + t c = 1`, so at a
negative value the dependency is supported precisely on the support of `v`.

Unconditional in `(size, rank)`, and it consumes no part of the first-order system:
no multiplier, no diagonal law, no commutation. -/
theorem sum_smul_atom_eq_zero_of_chartStationaryGap_mulVec_eq_smul
    (design : WeightedDesign size rank) {value : ℝ} {direction : Fin size → ℝ}
    (hzeroLeak : chartStationaryGap (projectionOfDesign design) design.weight *ᵥ direction
      = value • direction) :
    ∑ atomIndex, ((1 - value - design.weight atomIndex)
        * Real.sqrt (design.weight atomIndex) * direction atomIndex)
        • design.atom atomIndex = 0 := by
  have hshift := sum_smul_atom_eq_zero_of_projectionOfDesign_mulVec_eq_zero design
    (projection_mulVec_sub_projection_mulVec_eq_zero
      (projectionOfDesign_mul_self design) direction)
  rw [← hshift]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [sub_projection_mulVec_apply_of_chartStationaryGap_mulVec_eq_smul hzeroLeak atomIndex]
  ring_nf

/-- **AT SUPPORT TWO THE DEPENDENCY IS A PARALLEL PAIR.**  The nondegeneracy the
statement needs is `value + t c ≠ 1` at the two supported labels, which is FREE at a
negative value; it is a hypothesis here so the theorem does not silently assume a
crux. -/
theorem hasParallelPair_of_zeroLeak_on_support_pair
    (design : WeightedDesign size rank) {value : ℝ} {direction : Fin size → ℝ}
    (hzeroLeak : chartStationaryGap (projectionOfDesign design) design.weight *ᵥ direction
      = value • direction)
    {firstLabel secondLabel : Fin size} (hdistinct : firstLabel ≠ secondLabel)
    (hsecondNonzero : direction secondLabel ≠ 0)
    (hsecondShift : value + design.weight secondLabel ≠ 1)
    (hsupport : ∀ atomIndex, atomIndex ≠ firstLabel → atomIndex ≠ secondLabel →
      direction atomIndex = 0) :
    HasParallelPair design := by
  refine hasParallelPair_of_projectionOfDesign_mulVec_eq_zero_on_support_pair design
    (projection_mulVec_sub_projection_mulVec_eq_zero
      (projectionOfDesign_mul_self design) direction) hdistinct ?_ ?_
  · rw [sub_projection_mulVec_apply_of_chartStationaryGap_mulVec_eq_smul hzeroLeak]
    exact mul_ne_zero (fun hzero => hsecondShift (by linarith)) hsecondNonzero
  · intro atomIndex hfirst hsecond
    rw [sub_projection_mulVec_apply_of_chartStationaryGap_mulVec_eq_smul hzeroLeak,
      hsupport atomIndex hfirst hsecond, mul_zero]

/-! ## At a `(6,3)` crux -/

/-- **A CRUX ADMITS NO ZERO-LEAK TIGHT DIRECTION SUPPORTED ON A PAIR.**  The shift
factor is positive because the value is negative and the weights sum to one, so the
dependency is a genuine parallel pair and the crux field forbids it. -/
theorem SixThreeCrux.false_of_zeroLeak_on_support_pair (crux : SixThreeCrux)
    {direction : Fin 6 → ℝ}
    (hzeroLeak : chartStationaryGap (projectionOfDesign crux.design) crux.design.weight
        *ᵥ direction
      = chartObjective (chartPointOfDesign crux.design) • direction)
    {firstLabel secondLabel : Fin 6} (hdistinct : firstLabel ≠ secondLabel)
    (hsecondNonzero : direction secondLabel ≠ 0)
    (hsupport : ∀ atomIndex, atomIndex ≠ firstLabel → atomIndex ≠ secondLabel →
      direction atomIndex = 0) :
    False := by
  have hnegative : chartObjective (chartPointOfDesign crux.design) < 0 :=
    crux.hasNegativeChartValue
  have hweightLt : crux.design.weight secondLabel < 1 :=
    weight_lt_one crux.design (by norm_num) secondLabel
  exact crux.hasNoParallelPair
    (hasParallelPair_of_zeroLeak_on_support_pair crux.design hzeroLeak hdistinct
      hsecondNonzero (by intro heq; linarith) hsupport)

end Gtz

/-
# THE PRIVATE-ATOM SPECTRAL FLOOR, THE VALUE LATTICE IT QUANTIZES, AND TWO CLASS DISCHARGES

An active label of a chart stationarity datum OWNS an atom when every OTHER active tight
direction vanishes there.  `HasPrivateAtomSystem` hands each active label a whole SET of
owned atoms.  On that stratum one field of `Gtz.IsChartStationaryData` -- the constant
assembly diagonal `Xi_cc = 1/size`, read through `Gtz.chartMultiplierAssembly_diagonal` --
collapses at an owned atom to the MASS LAW

    lambda_a * u_a(c)^2 = 1/size ,

and summing only the squares that survive when every unowned coordinate is discarded (the
owned sets are pairwise disjoint, so what survives is a genuine subsum) gives the
PER-VECTOR FLOOR

    (floorCount / size) * <probe, Xi probe>  <=  |Xi probe|^2 ,

`floorCount` any common lower bound on the owned cardinalities.  Running that at the
chart's own columns, and combining with `trace (S * S) <= (trace S)^2` for positive
semidefinite `S` (`Gtz.sq_le_mul_diag_of_posSemidef`) and the shipped trace identity
`Gtz.trace_projection_mul_multiplier_of_isChartStationaryData`, yields the headline.

## THE GRADED DICHOTOMY, at general `(size, rank)`

`value_eq_neg_inv_size_or_privateFloor_le_of_hasPrivateAtomSystem`:

    value = -1/size    or    (floorCount - 1)/size <= value ,

so the open band `(-1/size, (floorCount-1)/size)` is EMPTY on the stratum.  No eigenvalue,
no Schur complement and no range projection appears anywhere in the proof; the three steps
are the per-vector inequality, its columnwise sum, and one Cauchy-Schwarz.

* `floorCount = 1` -- `value_eq_neg_inv_size_or_zero_le_of_hasPrivateAtomSystem`, and its
  combinatorial form `value_eq_neg_inv_size_or_zero_le_of_privateAtomSelector`, where the
  hypothesis is a system of distinct representatives on the SUBSETS and mentions no tight
  direction at all.  At `(6,3)` the excluded band `(-1/6, 0)` strictly contains the whole
  crux window `[-4/27, 0)`, because `-1/6 < -4/27`.
* `floorCount = rank` -- what PAIRWISE DISJOINT active subsets supply, since then every
  atom of a subset is owned by its label and `Gtz.IsChartStationaryData.activeSubset_card`
  says there are `rank` of them.  At `(6,3)`: `value = -1/6` or `1/3 <= value`.

## THE QUANTIZATION, AND WHAT ITS UNIT IS

At pairwise disjoint subsets the multipliers are all `rank/size`
(`activeWeight_eq_rank_div_size_of_pairwiseDisjoint_activeSubset`), distinct tight
directions are orthogonal, and the assembly is a scalar multiple of an idempotent
(`chartMultiplierAssembly_mul_self_of_pairwiseDisjoint_activeSubset`).  So
`(size/rank) * (projection * assembly)` is idempotent, its trace is a NATURAL NUMBER
(`exists_natCast_trace_of_isIdempotentElem`, the one ingredient of this file that is not
bookkeeping and that the repository did not have), and

    value = (rank * capturedRank - 1)/size ,   rank * capturedRank <= size ,

`exists_value_eq_of_pairwiseDisjoint_activeSubset`.  THE UNIT IS `rank/size`, NOT `1/size`:
the lattice is `(rank * Z - 1)/size`.  At `(6,3)` it is `{-1/6, 1/3, 5/6}`
(`value_eq_of_pairwiseDisjoint_activeSubset_sixThree`) -- exactly the root set of the
shipped two-block cubic `108 g^3 - 108 g^2 + 9 g + 5 = (3g-1)(6g-5)(6g+1)`, reached here by
counting rather than by any distinctness hypothesis on the weights.

## TWO `(6,3)` CLASSES DISCHARGED

`Gtz.EliminatesThreeMemberValue` is a shipped named hypothesis -- a citable hole,
instantiated at two families on the evidence of an msolve elimination with no cofactor
list.  `eliminatesThreeMemberValue_of_privateAtomSelector` turns it into a THEOREM for
EVERY family carrying a private system of distinct representatives, by the
`floorCount = 1` dichotomy plus the arithmetic fact that `-1/6` is a root of `E3` -- the
smallest of its seven consecutive sixths.  No Groebner basis, no admissibility, no
numerics.  Two families qualify and each costs one `decide`:

* `Gtz.chartTriplePairwiseMeetFamily = {{0,1,5},{0,2,4},{1,2,3}}` -- representatives
  `5, 4, 3`.  Its shipped conditional closure
  `Gtz.zero_le_value_of_chartTriplePairwiseMeetFamily_of_eliminates` becomes
  unconditional.
* `Gtz.chartTripleStarFamily = {{0,1,4},{0,1,5},{0,2,3}}` -- representatives `4, 5, 2`.
  READ THE SIDES CORRECTLY, as `Gtz.Quantitative.ClassRouteCost` itself insists: that
  class is already dead on the LEG side, where `Gtz.hasSaturatedAtom_chartTripleStarFamily`
  feeds the quadric-side filter `Gtz.one_le_value_of_saturatedAtom`, whose datum is
  `Gtz.IsQuadricStationaryData`.  `Gtz.EliminatesThreeMemberValue` quantifies over
  `Gtz.IsChartStationaryData`, and nothing discharged it there.  This file does.

The THIRD surviving class is out of reach and that is a theorem, not a gap:
`not_exists_privateAtomSelector_chartTripleSharedEdgeFamily` -- in
`Gtz.chartTripleSharedEdgeFamily = {{0,1,2},{0,4,5},{1,2,3}}` the other two members cover
all six atoms, so no representative for `{0,1,2}` can avoid both.  Its instance of
`Gtz.EliminatesThreeMemberValue` stays a citable hole.

## SCOPE, HONESTLY -- THREE THINGS THIS CANNOT DO

1. **IT CANNOT REACH THE CELL.**  A private system forces `|A| <= size - rank + 1`, which
   is `4` at `(6,3)`, while the measured admissible index floor there is `|A| >= 8`.  So
   the stratum and the admissible locus are disjoint.  [The counting bound and the floor
   are both MEASURED outside Lean and neither is mechanized here; the bound is an
   incidence count, the floor a census.]
2. **IT IS FIELD-BLIND, so by boundary condition B1 it cannot close the cell.**  Every
   step -- the constant diagonal, the mass law, the disjointness, the commutation, the
   trace argument, the integrality -- is a statement about Hermitian positive semidefinite
   matrices and transports verbatim to `C`.  A complex datum at `value = -1/size` with
   pairwise disjoint subsets exists for EVERY choice of phases and has the same spectrum
   `(0,0,0,0,1/2,1/2)` as the real one [MEASURED, residuals at `1e-16`, not mechanized].
3. **THE SPECTRUM IS NOT PINNED, and the prediction that it was is REFUTED.**  The
   mechanism this file lands is COMBINATORIAL -- a system of distinct representatives on
   the active subsets -- not spectral.  At `|A| = 3` the assembly's nonzero spectrum sweeps
   a positive-dimensional family within each of the three `(6,3)` covering classes
   [MEASURED at 80 digits over 5428 solutions of the stationarity system; the predicted
   pinning to `(1/2, 1/3, 1/6, 0, 0, 0)` does not occur].  What IS pinned, and only at
   `floorCount >= 1`, is the VALUE.

## RELATION TO WHAT IS ALREADY SHIPPED

* `Gtz.rank_le_value_of_pairwiseDisjoint_activeSubset`
  (`Gtz.Quantitative.IsolatedBlockExclusion`) is the LEG-side twin: the same
  pairwise-disjointness hypothesis, over `Gtz.IsQuadricStationaryData`, concluding
  `rank <= value`.  Nothing here reproves it and nothing here consumes it; the two live on
  different data and in different normalisations.  The naming suffix
  `_of_pairwiseDisjoint_activeSubset` is taken from it deliberately, and for the same
  reason no new predicate is defined -- the hypothesis travels inline.
  `Gtz.IsIsolatedActiveBlock` is the one-block weakening it uses.
* `Gtz.zero_le_value_of_isChartTwoBlockFamily` (`Gtz.Quantitative.ChartTwoBlock`) gets
  `0 <= value` from TWO complementary blocks plus pairwise distinct weights inside each.
  The dichotomy here is INCOMPARABLE: weaker conclusion (a disjunction, not
  `value = (rank-1)/size`), weaker hypothesis (no distinctness, any number of blocks).
  The disjunction cannot be collapsed, and the shipped uniform witness is the proof --
  see the non-vacuity section.
* `Gtz.activeWeight_le_rank_div_size_of_isChartStationaryData` bounds every multiplier by
  `rank/size` unconditionally; `activeWeight_eq_rank_div_size_of_pairwiseDisjoint_activeSubset`
  turns that into an EQUALITY on this stratum.
* `Gtz.Quantitative.PrivateAtomLocalisation` and `Gtz.blockPrivatePart`
  (`Gtz.Quantitative.ActiveOverlapPatternsSixThree`) carry a private-atom notion on the
  QUADRIC side, as an inline hypothesis about one atom of one block.  Neither is usable
  here and neither is duplicated: their datum is `Gtz.IsQuadricStationaryData`.
* `Gtz.rank_pos_of_isChartStationaryData` and `Gtz.atomMatrix_mul_atomMatrix` are consumed,
  not restated.

## THE GENERAL DEGREE CAP

`card_filter_powersetCard_mem` and `le_multiplierDegree_constant` close the one
`(6,3)`-only statement of the balanced layer.  `Gtz.le_multiplierDegree_constant_sixThree`
was landed at size six because the count `|{C : |C| = rank, c in C}| = C(size-1, rank-1)`
was believed available only there and only by `decide`
(`Gtz.card_powersetCard_three_through_atom`).  It is a Mathlib theorem,
`Finset.card_filter_powersetCard_subset`, and the general form costs one binder plus the
absorption identity `size * C(size-1, rank-1) = C(size, rank) * rank`.  The general
hypothesis `weight c <= rank/size` is literally what
`Gtz.activeWeight_le_rank_div_size_of_isChartStationaryData` produces; at `(6,3)` it is the
landed `weight <= 1/2`.

## NON-VACUITY

Every hypothesis bundle above is inhabited in the kernel, and the two branches of the
dichotomy are BOTH attained, so neither can be deleted.

* `exists_isChartStationaryData_hasPrivateAtomSystem` -- the shipped octahedron datum
  `Gtz.chartOctaProjection_isChartStationaryData`, at the OPEN cell `(6,3)`.  Its tight
  directions are the six coordinate vectors, so atom `c` is owned by label `c`; its value
  is `1/3`, the second branch.
* `exists_isChartStationaryData_pairwiseDisjoint_value_eq_neg_inv_size` -- the shipped
  uniform two-block datum `Gtz.chartTwoBlockUniformProjection_isChartStationaryData`, whose
  two blocks `{0,1}` and `{2,3}` are disjoint, at `value = -1/4 = -1/size` exactly.  THE
  FIRST BRANCH IS ATTAINED, so the disjunction is not decoration; this is also the lattice
  point `capturedRank = 0`.
* `exists_isChartStationaryData_pairwiseDisjoint_value_eq_rank_sub_one_div_size` -- a
  rational `(4,4)` datum built here (identity chart, uniform weights, one active label with
  the all-halves tight direction) at `value = 3/4 = (rank-1)/size` exactly.  THE SECOND
  BRANCH IS ATTAINED, so the bound `(rank-1)/size` is SHARP and cannot be improved; this is
  the lattice point `capturedRank = 1`, and `rank * capturedRank = size` shows the cap is
  tight too.
* `pairwiseMeetPrivateAtom_notMem` and `starPrivateAtom_notMem` are `decide` checks that
  FIRE; `not_exists_privateAtomSelector_chartTripleSharedEdgeFamily` is the matching
  negative, so the combinatorial hypothesis separates the three surviving classes rather
  than holding everywhere.
-/

import Mathlib
import Gtz.Corner.CornerFiber
import Gtz.Quantitative.ChartTwoBlock
import Gtz.Quantitative.BalancedCollections
import Gtz.Quantitative.ClassRouteCost
import Gtz.Reduction.MaximalVolume

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size : ℕ} {activeIndex : Type*}
variable {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
  {value : ℝ} {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
  {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## The arithmetic engine -/

/-- **THE TRACE OF A REAL IDEMPOTENT MATRIX IS A NATURAL NUMBER** -- the rank of the
projection it performs.  The repository did not have this, and it is the one ingredient of
the quantization below that is not bookkeeping. -/
theorem exists_natCast_trace_of_isIdempotentElem
    {square : Matrix (Fin size) (Fin size) ℝ} (hidem : square * square = square) :
    ∃ projectionRank : ℕ, Matrix.trace square = (projectionRank : ℝ) := by
  classical
  have hendoIdem : IsIdempotentElem (Matrix.toLin' square) := by
    show Matrix.toLin' square * Matrix.toLin' square = Matrix.toLin' square
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hidem]
  refine ⟨Module.finrank ℝ (LinearMap.range (Matrix.toLin' square)), ?_⟩
  rw [← Matrix.trace_toLin'_eq square]
  exact (LinearMap.isProj_range_iff_isIdempotentElem _ |>.2 hendoIdem).trace

/-! ## Private-atom systems and the mass law -/

/-- **A PRIVATE-ATOM SYSTEM.**  Every active label is handed a whole SET of atoms at which
every OTHER active tight direction vanishes.  Nothing is asserted about the owner's own
direction there, and nothing about the sets being nonempty -- the graded floor below reads
their cardinalities and the empty system is the trivial instance. -/
def HasPrivateAtomSystem (activeSet : Finset activeIndex)
    (tightDir : activeIndex → (Fin size → ℝ))
    (privateAtomSet : activeIndex → Finset (Fin size)) : Prop :=
  ∀ ownerLabel ∈ activeSet, ∀ atomIndex ∈ privateAtomSet ownerLabel,
    ∀ otherLabel ∈ activeSet, otherLabel ≠ ownerLabel → tightDir otherLabel atomIndex = 0

/-- The COMBINATORIAL sufficient condition a family census supplies: the owned set is
carved out by membership in the SUBSETS, with no reference to a tight direction.  The
support field of the bundle does the rest. -/
theorem hasPrivateAtomSystem_of_notMem_activeSubset
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {privateAtomSet : activeIndex → Finset (Fin size)}
    (hout : ∀ ownerLabel ∈ activeSet, ∀ atomIndex ∈ privateAtomSet ownerLabel,
      ∀ otherLabel ∈ activeSet, otherLabel ≠ ownerLabel →
        atomIndex ∉ activeSubset otherLabel) :
    HasPrivateAtomSystem activeSet tightDir privateAtomSet :=
  fun ownerLabel hownerMem atomIndex hatomMem otherLabel hotherMem hne =>
    hdata.tightDir_support otherLabel hotherMem atomIndex
      (hout ownerLabel hownerMem atomIndex hatomMem otherLabel hotherMem hne)

/-- **THE PRIVATE MASS LAW**, one atom at a time: `lambda_a * u_a(c)^2 = 1/size` at every
atom `c` owned by `a`.  This is the constant assembly diagonal
(`Gtz.chartMultiplierAssembly_diagonal`) with every other summand killed by ownership. -/
theorem activeWeight_mul_sq_mem_privateAtomSet
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {privateAtomSet : activeIndex → Finset (Fin size)}
    (hprivate : HasPrivateAtomSystem activeSet tightDir privateAtomSet)
    {ownerLabel : activeIndex} (hmem : ownerLabel ∈ activeSet)
    {atomIndex : Fin size} (hatomMem : atomIndex ∈ privateAtomSet ownerLabel) :
    activeWeight ownerLabel * tightDir ownerLabel atomIndex ^ 2 = ((size : ℝ))⁻¹ := by
  classical
  have hdiagonal := hdata.assembly_diagonal atomIndex
  rw [chartMultiplierAssembly_diagonal] at hdiagonal
  rw [← hdiagonal]
  symm
  refine Finset.sum_eq_single_of_mem ownerLabel hmem ?_
  intro otherLabel hotherMem hne
  rw [hprivate ownerLabel hmem atomIndex hatomMem otherLabel hotherMem hne]
  ring

/-- **OWNED SETS ARE PAIRWISE DISJOINT.**  A shared atom would force the first owner's own
direction to vanish there, and the mass law says it does not.  This is what makes the
per-vector floor a subsum rather than an overcount. -/
theorem disjoint_privateAtomSet_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {privateAtomSet : activeIndex → Finset (Fin size)}
    (hprivate : HasPrivateAtomSystem activeSet tightDir privateAtomSet)
    {firstLabel : activeIndex} (hfirstMem : firstLabel ∈ activeSet)
    {secondLabel : activeIndex} (hsecondMem : secondLabel ∈ activeSet)
    (hne : firstLabel ≠ secondLabel) :
    Disjoint (privateAtomSet firstLabel) (privateAtomSet secondLabel) := by
  classical
  rw [Finset.disjoint_left]
  intro atomIndex hfirstAtom hsecondAtom
  have hvanish : tightDir firstLabel atomIndex = 0 :=
    hprivate secondLabel hsecondMem atomIndex hsecondAtom firstLabel hfirstMem hne
  have hmass := activeWeight_mul_sq_mem_privateAtomSet hdata hprivate hfirstMem hfirstAtom
  rw [hvanish] at hmass
  have hsizeCast := size_cast_pos_of_isChartStationaryData hdata
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hmass
  exact absurd hmass.symm (inv_ne_zero (ne_of_gt hsizeCast))

/-- At an owned atom the assembly's action collapses to the owner's single term. -/
theorem mulVec_mem_privateAtomSet_eq (activeSet : Finset activeIndex)
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → (Fin size → ℝ))
    {privateAtomSet : activeIndex → Finset (Fin size)}
    (hprivate : HasPrivateAtomSystem activeSet tightDir privateAtomSet)
    {ownerLabel : activeIndex} (hmem : ownerLabel ∈ activeSet)
    {atomIndex : Fin size} (hatomMem : atomIndex ∈ privateAtomSet ownerLabel)
    (probe : Fin size → ℝ) :
    (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ probe) atomIndex
      = activeWeight ownerLabel * tightDir ownerLabel atomIndex
        * (tightDir ownerLabel ⬝ᵥ probe) := by
  classical
  rw [Matrix.mulVec, dotProduct]
  have hexpand : ∀ colIndex : Fin size,
      chartMultiplierAssembly activeSet activeWeight tightDir atomIndex colIndex
          * probe colIndex
        = ∑ activeLabel ∈ activeSet, activeWeight activeLabel
            * (tightDir activeLabel atomIndex * tightDir activeLabel colIndex
              * probe colIndex) := by
    intro colIndex
    rw [chartMultiplierAssembly_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun activeLabel _ => by ring
  rw [Finset.sum_congr rfl fun colIndex _ => hexpand colIndex, Finset.sum_comm,
    Finset.sum_eq_single_of_mem ownerLabel hmem]
  · rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun colIndex _ => by ring
  · intro otherLabel hotherMem hne
    rw [hprivate ownerLabel hmem atomIndex hatomMem otherLabel hotherMem hne]
    simp

/-- The assembly's quadratic form, expanded over the active labels.  A generic identity
about `Gtz.chartMultiplierAssembly`: no datum, no ownership, no hypothesis at all. -/
theorem dotProduct_mulVec_chartMultiplierAssembly (activeSet : Finset activeIndex)
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → (Fin size → ℝ))
    (probe : Fin size → ℝ) :
    probe ⬝ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ probe)
      = ∑ activeLabel ∈ activeSet,
          activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probe) ^ 2 := by
  classical
  rw [chartMultiplierAssembly, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun activeLabel _ => ?_
  have hrow : ∀ rowIndex : Fin size,
      ((activeWeight activeLabel • atomMatrix (tightDir activeLabel)) *ᵥ probe) rowIndex
        = activeWeight activeLabel * tightDir activeLabel rowIndex
          * (tightDir activeLabel ⬝ᵥ probe) := by
    intro rowIndex
    rw [Matrix.mulVec, dotProduct, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun colIndex _ => ?_
    simp only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
    ring
  rw [dotProduct]
  have hstep : ∑ rowIndex : Fin size, probe rowIndex
        * ((activeWeight activeLabel • atomMatrix (tightDir activeLabel)) *ᵥ probe) rowIndex
      = ∑ rowIndex : Fin size, probe rowIndex
        * (activeWeight activeLabel * tightDir activeLabel rowIndex
          * (tightDir activeLabel ⬝ᵥ probe)) :=
    Finset.sum_congr rfl fun rowIndex _ => by rw [hrow rowIndex]
  rw [hstep]
  have hfactor : ∑ rowIndex : Fin size, probe rowIndex
        * (activeWeight activeLabel * tightDir activeLabel rowIndex
          * (tightDir activeLabel ⬝ᵥ probe))
      = (activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probe))
        * ∑ rowIndex : Fin size, tightDir activeLabel rowIndex * probe rowIndex := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun rowIndex _ => by ring
  rw [hfactor, ← dotProduct]
  ring

/-! ## The graded per-vector floor and the value dichotomy -/

/-- **THE GRADED PER-VECTOR FLOOR**: `(floorCount/size) <v, Xi v> <= |Xi v|^2` whenever
every owned set has at least `floorCount` atoms.  Discard every coordinate outside the
owned sets -- they are pairwise disjoint, so what survives is a genuine subsum of squares
-- and evaluate the survivors by the mass law. -/
theorem privateFloor_mul_form_le_normSq_mulVec
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {privateAtomSet : activeIndex → Finset (Fin size)}
    (hprivate : HasPrivateAtomSystem activeSet tightDir privateAtomSet)
    {floorCount : ℕ}
    (hfloor : ∀ activeLabel ∈ activeSet, floorCount ≤ (privateAtomSet activeLabel).card)
    (probe : Fin size → ℝ) :
    (floorCount : ℝ) * ((size : ℝ))⁻¹
        * (probe ⬝ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ probe))
      ≤ (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ probe)
        ⬝ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ probe) := by
  classical
  set assembly := chartMultiplierAssembly activeSet activeWeight tightDir with hassembly
  have hsizeCast := size_cast_pos_of_isChartStationaryData hdata
  have hlabel : ∀ activeLabel ∈ activeSet,
      (floorCount : ℝ) * ((size : ℝ))⁻¹
          * (activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probe) ^ 2)
        ≤ ∑ atomIndex ∈ privateAtomSet activeLabel, (assembly *ᵥ probe) atomIndex ^ 2 := by
    intro activeLabel hmem
    have hterm : ∀ atomIndex ∈ privateAtomSet activeLabel,
        (assembly *ᵥ probe) atomIndex ^ 2
          = ((size : ℝ))⁻¹
            * (activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probe) ^ 2) := by
      intro atomIndex hatomMem
      rw [hassembly,
        mulVec_mem_privateAtomSet_eq activeSet activeWeight tightDir hprivate hmem hatomMem probe]
      have hmass := activeWeight_mul_sq_mem_privateAtomSet hdata hprivate hmem hatomMem
      have hsplit : (activeWeight activeLabel * tightDir activeLabel atomIndex
            * (tightDir activeLabel ⬝ᵥ probe)) ^ 2
          = (activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2)
            * (activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probe) ^ 2) := by ring
      rw [hsplit, hmass]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    have hnonneg : 0 ≤ ((size : ℝ))⁻¹
        * (activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probe) ^ 2) :=
      mul_nonneg (le_of_lt (inv_pos.mpr hsizeCast))
        (mul_nonneg (hdata.activeWeight_nonneg activeLabel hmem) (sq_nonneg _))
    have hcast : (floorCount : ℝ) ≤ ((privateAtomSet activeLabel).card : ℝ) :=
      Nat.cast_le.mpr (hfloor activeLabel hmem)
    calc (floorCount : ℝ) * ((size : ℝ))⁻¹
            * (activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probe) ^ 2)
        = (floorCount : ℝ) * (((size : ℝ))⁻¹
            * (activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probe) ^ 2)) := by ring
      _ ≤ ((privateAtomSet activeLabel).card : ℝ) * (((size : ℝ))⁻¹
            * (activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probe) ^ 2)) :=
          mul_le_mul_of_nonneg_right hcast hnonneg
  have hleft : (floorCount : ℝ) * ((size : ℝ))⁻¹ * (probe ⬝ᵥ (assembly *ᵥ probe))
      ≤ ∑ activeLabel ∈ activeSet,
          ∑ atomIndex ∈ privateAtomSet activeLabel, (assembly *ᵥ probe) atomIndex ^ 2 := by
    rw [hassembly, dotProduct_mulVec_chartMultiplierAssembly, Finset.mul_sum]
    exact Finset.sum_le_sum hlabel
  have hbiUnion : ∑ activeLabel ∈ activeSet,
        ∑ atomIndex ∈ privateAtomSet activeLabel, (assembly *ᵥ probe) atomIndex ^ 2
      = ∑ atomIndex ∈ activeSet.biUnion privateAtomSet, (assembly *ᵥ probe) atomIndex ^ 2 := by
    symm
    refine Finset.sum_biUnion ?_
    intro firstLabel hfirstMem secondLabel hsecondMem hne
    exact disjoint_privateAtomSet_of_isChartStationaryData hdata hprivate
      (Finset.mem_coe.mp hfirstMem) (Finset.mem_coe.mp hsecondMem) hne
  have hsubset : ∑ atomIndex ∈ activeSet.biUnion privateAtomSet,
        (assembly *ᵥ probe) atomIndex ^ 2
      ≤ ∑ atomIndex : Fin size, (assembly *ᵥ probe) atomIndex ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun atomIndex _ _ => sq_nonneg _
  have hnorm : ∑ atomIndex : Fin size, (assembly *ᵥ probe) atomIndex ^ 2
      = (assembly *ᵥ probe) ⬝ᵥ (assembly *ᵥ probe) := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun atomIndex _ => by rw [pow_two]
  rw [← hnorm]
  exact hleft.trans (le_of_eq hbiUnion) |>.trans hsubset

/-- **THE GRADED VALUE DICHOTOMY**, at general `(size, rank)`.  With `floorCount` owned
atoms per active label the open band `(-1/size, (floorCount-1)/size)` is EMPTY:

    value = -1/size    or    (floorCount - 1)/size <= value .

The columnwise sum of the per-vector floor against
`trace (S * S) <= (trace S)^2` (`Gtz.sq_le_mul_diag_of_posSemidef`), read through the
shipped trace identity `Gtz.trace_projection_mul_multiplier_of_isChartStationaryData`.
Both branches are attained -- see the non-vacuity section at the end of the file. -/
theorem value_eq_neg_inv_size_or_privateFloor_le_of_hasPrivateAtomSystem
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {privateAtomSet : activeIndex → Finset (Fin size)}
    (hprivate : HasPrivateAtomSystem activeSet tightDir privateAtomSet)
    {floorCount : ℕ}
    (hfloor : ∀ activeLabel ∈ activeSet, floorCount ≤ (privateAtomSet activeLabel).card) :
    value = -((size : ℝ))⁻¹ ∨ ((floorCount : ℝ) - 1) * ((size : ℝ))⁻¹ ≤ value := by
  classical
  set assembly := chartMultiplierAssembly activeSet activeWeight tightDir with hassembly
  set product := projection * assembly with hproduct
  have hpsd : product.PosSemidef :=
    posSemidef_projection_mul_multiplier_of_isChartStationaryData hdata
  have htrace : Matrix.trace product = value + ((size : ℝ))⁻¹ :=
    trace_projection_mul_multiplier_of_isChartStationaryData hdata
  have hsizeCast := size_cast_pos_of_isChartStationaryData hdata
  have hsymmetric : ∀ rowIndex colIndex : Fin size,
      product colIndex rowIndex = product rowIndex colIndex := by
    intro rowIndex colIndex
    have hherm := hpsd.isHermitian.apply rowIndex colIndex
    simpa using hherm
  have hentry : ∀ rowIndex colIndex : Fin size,
      product rowIndex colIndex
        = (assembly *ᵥ (fun otherIndex => projection otherIndex colIndex)) rowIndex := by
    intro rowIndex colIndex
    have hswap : product = assembly * projection := by
      rw [hproduct, hassembly, hdata.assembly_commutes]
    rw [hswap, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hupper : Matrix.trace (product * product) ≤ (Matrix.trace product) ^ 2 := by
    have hexpand : Matrix.trace (product * product)
        = ∑ rowIndex : Fin size, ∑ colIndex : Fin size,
            product rowIndex colIndex * product colIndex rowIndex :=
      Finset.sum_congr rfl fun rowIndex _ => by rw [Matrix.diag_apply, Matrix.mul_apply]
    have hsquare : (Matrix.trace product) ^ 2
        = ∑ rowIndex : Fin size, ∑ colIndex : Fin size,
            product rowIndex rowIndex * product colIndex colIndex := by
      rw [Matrix.trace, pow_two, Finset.sum_mul_sum]
      rfl
    rw [hexpand, hsquare]
    refine Finset.sum_le_sum fun rowIndex _ => Finset.sum_le_sum fun colIndex _ => ?_
    rw [hsymmetric rowIndex colIndex, ← pow_two]
    exact sq_le_mul_diag_of_posSemidef hpsd rowIndex colIndex
  have hdiagColumn : ∀ colIndex : Fin size,
      (fun otherIndex => projection otherIndex colIndex)
          ⬝ᵥ (assembly *ᵥ (fun otherIndex => projection otherIndex colIndex))
        = product colIndex colIndex := by
    intro colIndex
    have hfold : (projection * product) colIndex colIndex = product colIndex colIndex := by
      rw [hproduct, ← Matrix.mul_assoc, hdata.isIdempotent]
    rw [dotProduct, ← hfold, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun otherIndex _ => ?_
    rw [← hentry otherIndex colIndex]
    have hsym : projection otherIndex colIndex = projection colIndex otherIndex := by
      have htranspose := congrFun (congrFun hdata.isSymmetric colIndex) otherIndex
      simpa [Matrix.transpose_apply] using htranspose
    rw [hsym]
  have hnormColumn : ∀ colIndex : Fin size,
      (assembly *ᵥ (fun otherIndex => projection otherIndex colIndex))
          ⬝ᵥ (assembly *ᵥ (fun otherIndex => projection otherIndex colIndex))
        = ∑ rowIndex : Fin size, product rowIndex colIndex ^ 2 := by
    intro colIndex
    rw [dotProduct]
    exact Finset.sum_congr rfl fun rowIndex _ => by
      rw [← hentry rowIndex colIndex, ← pow_two]
  have hlower : (floorCount : ℝ) * ((size : ℝ))⁻¹ * Matrix.trace product
      ≤ Matrix.trace (product * product) := by
    have hleft : (floorCount : ℝ) * ((size : ℝ))⁻¹ * Matrix.trace product
        = ∑ colIndex : Fin size, (floorCount : ℝ) * ((size : ℝ))⁻¹
            * ((fun otherIndex => projection otherIndex colIndex)
              ⬝ᵥ (assembly *ᵥ (fun otherIndex => projection otherIndex colIndex))) := by
      rw [Matrix.trace, Finset.mul_sum]
      exact Finset.sum_congr rfl fun colIndex _ => by
        rw [hdiagColumn colIndex, Matrix.diag_apply]
    have hright : Matrix.trace (product * product)
        = ∑ colIndex : Fin size,
            (assembly *ᵥ (fun otherIndex => projection otherIndex colIndex))
              ⬝ᵥ (assembly *ᵥ (fun otherIndex => projection otherIndex colIndex)) := by
      have hexpand : Matrix.trace (product * product)
          = ∑ rowIndex : Fin size, ∑ colIndex : Fin size,
              product rowIndex colIndex * product colIndex rowIndex :=
        Finset.sum_congr rfl fun rowIndex _ => by rw [Matrix.diag_apply, Matrix.mul_apply]
      rw [hexpand, Finset.sum_comm]
      refine Finset.sum_congr rfl fun colIndex _ => ?_
      rw [hnormColumn colIndex]
      exact Finset.sum_congr rfl fun rowIndex _ => by
        rw [hsymmetric rowIndex colIndex, ← pow_two]
    rw [hleft, hright]
    exact Finset.sum_le_sum fun colIndex _ =>
      privateFloor_mul_form_le_normSq_mulVec hdata hprivate hfloor _
  have htraceNonneg : 0 ≤ Matrix.trace product := hpsd.trace_nonneg
  rcases eq_or_lt_of_le htraceNonneg with hzero | hpositive
  · refine Or.inl ?_
    rw [← hzero] at htrace
    linarith
  · refine Or.inr ?_
    have hchain : (floorCount : ℝ) * ((size : ℝ))⁻¹ * Matrix.trace product
        ≤ Matrix.trace product * Matrix.trace product := by
      rw [← pow_two]
      exact hlower.trans hupper
    have hfloorTrace : (floorCount : ℝ) * ((size : ℝ))⁻¹ ≤ Matrix.trace product :=
      le_of_mul_le_mul_right (by linarith [hchain]) hpositive
    rw [htrace] at hfloorTrace
    have hshift : ((floorCount : ℝ) - 1) * ((size : ℝ))⁻¹
        = (floorCount : ℝ) * ((size : ℝ))⁻¹ - ((size : ℝ))⁻¹ := by ring
    rw [hshift]
    linarith

/-- **THE UNGRADED DICHOTOMY**, `floorCount = 1`: one owned atom per active label already
empties the band `(-1/size, 0)`.  At `(6,3)` that band strictly contains the crux window
`[-4/27, 0)`, since `-1/6 < -4/27`. -/
theorem value_eq_neg_inv_size_or_zero_le_of_hasPrivateAtomSystem
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {privateAtomSet : activeIndex → Finset (Fin size)}
    (hprivate : HasPrivateAtomSystem activeSet tightDir privateAtomSet)
    (hnonempty : ∀ activeLabel ∈ activeSet, (privateAtomSet activeLabel).Nonempty) :
    value = -((size : ℝ))⁻¹ ∨ 0 ≤ value := by
  have hfloor : ∀ activeLabel ∈ activeSet, 1 ≤ (privateAtomSet activeLabel).card :=
    fun activeLabel hmem => Finset.card_pos.mpr (hnonempty activeLabel hmem)
  rcases value_eq_neg_inv_size_or_privateFloor_le_of_hasPrivateAtomSystem hdata hprivate hfloor
    with hzero | hbound
  · exact Or.inl hzero
  · refine Or.inr ?_
    rw [show ((1 : ℕ) : ℝ) - 1 = 0 by norm_num, zero_mul] at hbound
    exact hbound

/-- **THE DICHOTOMY IN COMBINATORIAL FORM.**  The hypothesis is a system of distinct
representatives on the active SUBSETS -- each label picks an atom the other labels' subsets
miss -- and mentions no tight direction, no multiplier and no matrix.  This is the form a
family census can discharge by `decide`, and it is what the `(6,3)` class discharges
below consume. -/
theorem value_eq_neg_inv_size_or_zero_le_of_privateAtomSelector
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {privateAtom : activeIndex → Fin size}
    (hout : ∀ ownerLabel ∈ activeSet, ∀ otherLabel ∈ activeSet, otherLabel ≠ ownerLabel →
      privateAtom ownerLabel ∉ activeSubset otherLabel) :
    value = -((size : ℝ))⁻¹ ∨ 0 ≤ value := by
  classical
  refine value_eq_neg_inv_size_or_zero_le_of_hasPrivateAtomSystem hdata
    (privateAtomSet := fun activeLabel => {privateAtom activeLabel})
    (hasPrivateAtomSystem_of_notMem_activeSubset hdata ?_) ?_
  · intro ownerLabel hownerMem atomIndex hatomMem otherLabel hotherMem hne
    rw [Finset.mem_singleton] at hatomMem
    subst hatomMem
    exact hout ownerLabel hownerMem otherLabel hotherMem hne
  · exact fun activeLabel _ => Finset.singleton_nonempty _

/-! ## Pairwise disjoint active subsets -/

/-- **PAIRWISE DISJOINT SUBSETS OWN THEMSELVES.**  If distinct active labels carry disjoint
subsets then every atom of a subset is owned by its label, so the graded floor runs at
`floorCount = rank`.  Only disjointness is used: no covering hypothesis appears anywhere in
this file, which is why nothing here says `partition`. -/
theorem hasPrivateAtomSystem_of_pairwiseDisjoint_activeSubset
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hdisjoint : ∀ firstLabel ∈ activeSet, ∀ secondLabel ∈ activeSet, firstLabel ≠ secondLabel →
      Disjoint (activeSubset firstLabel) (activeSubset secondLabel)) :
    HasPrivateAtomSystem activeSet tightDir activeSubset := by
  intro ownerLabel hownerMem atomIndex hatomMem otherLabel hotherMem hne
  refine hdata.tightDir_support otherLabel hotherMem atomIndex ?_
  have hpair := hdisjoint otherLabel hotherMem ownerLabel hownerMem hne
  intro hmemOther
  exact Finset.disjoint_left.mp hpair hmemOther hatomMem

/-- **THE DISJOINT-SUBSET DICHOTOMY**: `value = -1/size` or `(rank-1)/size <= value`, with
no hypothesis on the weights.  At `(6,3)`: `value = -1/6` or `1/3 <= value`.

Compare `Gtz.zero_le_value_of_isChartTwoBlockFamily`, which gets `0 <= value` from TWO
complementary blocks plus pairwise distinct weights inside each.  The two are
INCOMPARABLE: this conclusion is a disjunction rather than an equality, and this hypothesis
drops distinctness and allows any number of blocks.  The disjunction cannot be collapsed --
`exists_isChartStationaryData_pairwiseDisjoint_value_eq_neg_inv_size` attains its first
branch.  The LEG-side twin is `Gtz.rank_le_value_of_pairwiseDisjoint_activeSubset`, over
`Gtz.IsQuadricStationaryData`; neither implies the other. -/
theorem value_eq_neg_inv_size_or_le_of_pairwiseDisjoint_activeSubset
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hdisjoint : ∀ firstLabel ∈ activeSet, ∀ secondLabel ∈ activeSet, firstLabel ≠ secondLabel →
      Disjoint (activeSubset firstLabel) (activeSubset secondLabel)) :
    value = -((size : ℝ))⁻¹ ∨ ((rank : ℝ) - 1) * ((size : ℝ))⁻¹ ≤ value :=
  value_eq_neg_inv_size_or_privateFloor_le_of_hasPrivateAtomSystem hdata
    (hasPrivateAtomSystem_of_pairwiseDisjoint_activeSubset hdata hdisjoint)
    (fun activeLabel hmem => le_of_eq (hdata.activeSubset_card activeLabel hmem).symm)

/-- Distinct tight directions of disjoint subsets are orthogonal: their supports do not
meet. -/
theorem dotProduct_tightDir_eq_zero_of_pairwiseDisjoint_activeSubset
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hdisjoint : ∀ firstLabel ∈ activeSet, ∀ secondLabel ∈ activeSet, firstLabel ≠ secondLabel →
      Disjoint (activeSubset firstLabel) (activeSubset secondLabel))
    {firstLabel : activeIndex} (hfirstMem : firstLabel ∈ activeSet)
    {secondLabel : activeIndex} (hsecondMem : secondLabel ∈ activeSet)
    (hne : firstLabel ≠ secondLabel) :
    tightDir firstLabel ⬝ᵥ tightDir secondLabel = 0 := by
  classical
  rw [dotProduct]
  refine Finset.sum_eq_zero fun atomIndex _ => ?_
  by_cases hmemFirst : atomIndex ∈ activeSubset firstLabel
  · have hnotSecond : atomIndex ∉ activeSubset secondLabel :=
      fun hcontra => Finset.disjoint_left.mp
        (hdisjoint firstLabel hfirstMem secondLabel hsecondMem hne) hmemFirst hcontra
    rw [hdata.tightDir_support secondLabel hsecondMem atomIndex hnotSecond, mul_zero]
  · rw [hdata.tightDir_support firstLabel hfirstMem atomIndex hmemFirst, zero_mul]

/-- **THE MULTIPLIER IS DETERMINED**: on disjoint subsets every multiplier equals
`rank/size`.  Unit length plus the mass law, one atom at a time.  The shipped
`Gtz.activeWeight_le_rank_div_size_of_isChartStationaryData` gives the same bound as an
INEQUALITY with no hypothesis; here it is an equality. -/
theorem activeWeight_eq_rank_div_size_of_pairwiseDisjoint_activeSubset
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hdisjoint : ∀ firstLabel ∈ activeSet, ∀ secondLabel ∈ activeSet, firstLabel ≠ secondLabel →
      Disjoint (activeSubset firstLabel) (activeSubset secondLabel))
    {ownerLabel : activeIndex} (hmem : ownerLabel ∈ activeSet) :
    activeWeight ownerLabel = (rank : ℝ) * ((size : ℝ))⁻¹ := by
  classical
  have hprivate := hasPrivateAtomSystem_of_pairwiseDisjoint_activeSubset hdata hdisjoint
  have hunit := hdata.tightDir_unit ownerLabel hmem
  have hexpand : activeWeight ownerLabel
      = ∑ atomIndex ∈ activeSubset ownerLabel,
          activeWeight ownerLabel * tightDir ownerLabel atomIndex ^ 2 := by
    have hfull : ∑ atomIndex : Fin size,
          activeWeight ownerLabel * tightDir ownerLabel atomIndex ^ 2
        = activeWeight ownerLabel := by
      rw [← Finset.mul_sum]
      have hsquares : ∑ atomIndex : Fin size, tightDir ownerLabel atomIndex ^ 2 = 1 := by
        rw [← hunit, dotProduct]
        exact Finset.sum_congr rfl fun atomIndex _ => by rw [pow_two]
      rw [hsquares, mul_one]
    have hrestrict : ∑ atomIndex ∈ activeSubset ownerLabel,
          activeWeight ownerLabel * tightDir ownerLabel atomIndex ^ 2
        = ∑ atomIndex : Fin size,
            activeWeight ownerLabel * tightDir ownerLabel atomIndex ^ 2 :=
      Finset.sum_subset (Finset.subset_univ (activeSubset ownerLabel))
        (fun atomIndex _ hnotMem => by
          rw [hdata.tightDir_support ownerLabel hmem atomIndex hnotMem]; ring)
    rw [hrestrict, hfull]
  rw [hexpand,
    Finset.sum_congr rfl fun atomIndex hatomMem =>
      activeWeight_mul_sq_mem_privateAtomSet hdata hprivate hmem hatomMem,
    Finset.sum_const, nsmul_eq_mul, hdata.activeSubset_card ownerLabel hmem]

/-- **THE ASSEMBLY IS A SCALAR MULTIPLE OF AN IDEMPOTENT** on disjoint subsets: the cross
terms die by orthogonality and each diagonal term contributes its multiplier.  Consumes the
shipped `Gtz.atomMatrix_mul_atomMatrix`. -/
theorem chartMultiplierAssembly_mul_self_of_pairwiseDisjoint_activeSubset
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hdisjoint : ∀ firstLabel ∈ activeSet, ∀ secondLabel ∈ activeSet, firstLabel ≠ secondLabel →
      Disjoint (activeSubset firstLabel) (activeSubset secondLabel)) :
    chartMultiplierAssembly activeSet activeWeight tightDir
        * chartMultiplierAssembly activeSet activeWeight tightDir
      = ((rank : ℝ) * ((size : ℝ))⁻¹)
        • chartMultiplierAssembly activeSet activeWeight tightDir := by
  classical
  rw [chartMultiplierAssembly, Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun firstLabel hfirstMem => ?_
  rw [Matrix.mul_sum]
  rw [Finset.sum_eq_single_of_mem firstLabel hfirstMem]
  · rw [Matrix.smul_mul, Matrix.mul_smul, atomMatrix_mul_atomMatrix,
      hdata.tightDir_unit firstLabel hfirstMem, one_smul, smul_smul, smul_smul,
      activeWeight_eq_rank_div_size_of_pairwiseDisjoint_activeSubset hdata hdisjoint hfirstMem]
    rfl
  · intro secondLabel hsecondMem hne
    rw [Matrix.smul_mul, Matrix.mul_smul, atomMatrix_mul_atomMatrix,
      dotProduct_tightDir_eq_zero_of_pairwiseDisjoint_activeSubset hdata hdisjoint hfirstMem
        hsecondMem (fun heq => hne heq.symm), zero_smul, smul_zero, smul_zero]

/-- Some atom carries at least the average weight.  A pigeonhole on
`Gtz.IsChartStationaryData.weight_sum_one`, with no other field used. -/
theorem exists_inv_size_le_weight_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    ∃ atomIndex : Fin size, ((size : ℝ))⁻¹ ≤ weight atomIndex := by
  classical
  by_contra hall
  push Not at hall
  have hstrict : ∑ atomIndex : Fin size, weight atomIndex
      < ∑ _atomIndex : Fin size, ((size : ℝ))⁻¹ := by
    refine Finset.sum_lt_sum_of_nonempty ?_ fun atomIndex _ => hall atomIndex
    exact Finset.univ_nonempty_iff.mpr ⟨⟨0, size_pos_of_isChartStationaryData hdata⟩⟩
  rw [hdata.weight_sum_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt (size_cast_pos_of_isChartStationaryData hdata))]
    at hstrict
  exact absurd hstrict (lt_irrefl 1)

/-! ## The quantization lattice -/

/-- **THE QUANTIZATION LATTICE, AND ITS CAP.**  On disjoint subsets the value is
`(rank * capturedRank - 1)/size` for a natural number `capturedRank` -- the rank of the
projection the chart performs on the assembly's range -- and `rank * capturedRank <= size`.

THE UNIT IS `rank/size`, NOT `1/size`.  The lattice is the `-1/size` shift of `(rank/size) Z`,
which is why the two-block branch's "consecutive sixths" at `(6,3)` are spaced by `1/2` and
not by `1/6`.  The cap comes from the shipped ceiling
`Gtz.value_le_one_sub_weight_of_isChartStationaryData` applied at a heaviest atom. -/
theorem exists_value_eq_of_pairwiseDisjoint_activeSubset
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hdisjoint : ∀ firstLabel ∈ activeSet, ∀ secondLabel ∈ activeSet, firstLabel ≠ secondLabel →
      Disjoint (activeSubset firstLabel) (activeSubset secondLabel)) :
    ∃ capturedRank : ℕ,
      value = ((rank : ℝ) * (capturedRank : ℝ) - 1) * ((size : ℝ))⁻¹
        ∧ (rank : ℝ) * (capturedRank : ℝ) ≤ (size : ℝ) := by
  classical
  set assembly := chartMultiplierAssembly activeSet activeWeight tightDir with hassembly
  have hsizeCast := size_cast_pos_of_isChartStationaryData hdata
  have hrankCast : (0 : ℝ) < (rank : ℝ) :=
    Nat.cast_pos.mpr (rank_pos_of_isChartStationaryData hdata)
  have hsizeNe : (size : ℝ) ≠ 0 := ne_of_gt hsizeCast
  set scale := (size : ℝ) * ((rank : ℝ))⁻¹ with hscale
  have hunitScale : scale * ((rank : ℝ) * ((size : ℝ))⁻¹) = 1 := by
    rw [hscale]; field_simp
  have hsquare :=
    chartMultiplierAssembly_mul_self_of_pairwiseDisjoint_activeSubset hdata hdisjoint
  have hidem : (scale • (projection * assembly)) * (scale • (projection * assembly))
      = scale • (projection * assembly) := by
    have hcommute : assembly * projection = projection * assembly :=
      (hdata.assembly_commutes).symm
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hfold : projection * assembly * (projection * assembly)
        = ((rank : ℝ) * ((size : ℝ))⁻¹) • (projection * assembly) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc assembly projection assembly, hcommute,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, hdata.isIdempotent, Matrix.mul_assoc, hsquare,
        Matrix.mul_smul]
    rw [hfold, smul_smul, mul_assoc, hunitScale, mul_one]
  obtain ⟨capturedRank, htrace⟩ := exists_natCast_trace_of_isIdempotentElem hidem
  rw [Matrix.trace_smul, smul_eq_mul,
    trace_projection_mul_multiplier_of_isChartStationaryData hdata] at htrace
  have hscaled : ((rank : ℝ) * ((size : ℝ))⁻¹) * (scale * (value + ((size : ℝ))⁻¹))
      = ((rank : ℝ) * ((size : ℝ))⁻¹) * (capturedRank : ℝ) := by rw [htrace]
  rw [← mul_assoc, mul_comm ((rank : ℝ) * ((size : ℝ))⁻¹) scale, hunitScale, one_mul] at hscaled
  have hlattice : value = ((rank : ℝ) * (capturedRank : ℝ) - 1) * ((size : ℝ))⁻¹ := by
    have hexpandRight : ((rank : ℝ) * (capturedRank : ℝ) - 1) * ((size : ℝ))⁻¹
        = (rank : ℝ) * ((size : ℝ))⁻¹ * (capturedRank : ℝ) - ((size : ℝ))⁻¹ := by ring
    rw [hexpandRight]
    linarith [hscaled]
  refine ⟨capturedRank, hlattice, ?_⟩
  obtain ⟨atomIndex, hheavy⟩ := exists_inv_size_le_weight_of_isChartStationaryData hdata
  have hceiling := value_le_one_sub_weight_of_isChartStationaryData hdata atomIndex
  rw [hlattice] at hceiling
  have hscaledCeiling :
      ((rank : ℝ) * (capturedRank : ℝ) - 1) ≤ (1 - weight atomIndex) * (size : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hceiling (le_of_lt hsizeCast)
    rwa [mul_assoc, inv_mul_cancel₀ hsizeNe, mul_one] at hmul
  have hweightSize : ((size : ℝ))⁻¹ * (size : ℝ) ≤ weight atomIndex * (size : ℝ) :=
    mul_le_mul_of_nonneg_right hheavy (le_of_lt hsizeCast)
  rw [inv_mul_cancel₀ hsizeNe] at hweightSize
  nlinarith [hscaledCeiling, hweightSize]

/-- **THE `(6,3)` LATTICE**: disjoint active subsets force `value` into `{-1/6, 1/3, 5/6}`,
the root set of the shipped two-block cubic
`108 g^3 - 108 g^2 + 9 g + 5 = (3g-1)(6g-5)(6g+1)`.  Reached by counting, with no
distinctness hypothesis on the weights -- where
`Gtz.value_eq_rank_sub_one_div_size_of_isChartTwoBlockFamily` needs one and returns the
single value `1/3`. -/
theorem value_eq_of_pairwiseDisjoint_activeSubset_sixThree
    {projectionSix : Matrix (Fin 6) (Fin 6) ℝ} {weightSix : Fin 6 → ℝ} {valueSix : ℝ}
    {activeSetSix : Finset activeIndex} {activeSubsetSix : activeIndex → Finset (Fin 6)}
    {activeWeightSix : activeIndex → ℝ} {tightDirSix : activeIndex → (Fin 6 → ℝ)}
    (hdata : IsChartStationaryData 3 projectionSix weightSix valueSix activeSetSix
      activeSubsetSix activeWeightSix tightDirSix)
    (hdisjoint : ∀ firstLabel ∈ activeSetSix, ∀ secondLabel ∈ activeSetSix,
      firstLabel ≠ secondLabel →
        Disjoint (activeSubsetSix firstLabel) (activeSubsetSix secondLabel)) :
    valueSix = -(1 / 6) ∨ valueSix = 1 / 3 ∨ valueSix = 5 / 6 := by
  obtain ⟨capturedRank, hlattice, hbound⟩ :=
    exists_value_eq_of_pairwiseDisjoint_activeSubset hdata hdisjoint
  have hcapture : capturedRank ≤ 2 := by
    by_contra hbig
    push Not at hbig
    have hcast : (3 : ℝ) ≤ (capturedRank : ℝ) := by exact_mod_cast hbig
    norm_num at hbound
    linarith [hbound, hcast]
  interval_cases capturedRank <;> norm_num at hlattice ⊢ <;> simp [hlattice]

/-! ## Discharging `Gtz.EliminatesThreeMemberValue` at `(6,3)` -/

/-- **`Gtz.EliminatesThreeMemberValue` IS A THEOREM AT EVERY FAMILY WITH A PRIVATE SYSTEM OF
DISTINCT REPRESENTATIVES.**  The shipped hypothesis is a citable hole, asserted at two
families on the evidence of an msolve elimination with no cofactor list.  Here it is
discharged for a whole class of families at once: a representative for each member that the
other members miss makes the `floorCount = 1` dichotomy fire, and a negative value is
therefore pinned to `-1/6`, which is a root of `E3` -- indeed the smallest of the seven
consecutive sixths `Gtz.threeMemberEliminant_eq_prod` exhibits.

No Groebner basis, no admissibility, no numerics.  The `IsActiveFamily` and
`HasSimpleActiveSubsets` fields of the shipped hypothesis are what transport the selector
from the family to the labels. -/
theorem eliminatesThreeMemberValue_of_privateAtomSelector
    (family : Finset (Finset (Fin 6))) (privateAtom : Finset (Fin 6) → Fin 6)
    (hnotMem : ∀ firstBlock ∈ family, ∀ secondBlock ∈ family, firstBlock ≠ secondBlock →
      privateAtom firstBlock ∉ secondBlock) :
    EliminatesThreeMemberValue (activeIndex := activeIndex) family := by
  intro chartProjection chartWeight chartValue chartActiveSet chartActiveSubset
    chartActiveWeight chartTightDir hdata hfamily hsimple hnegative
  have hselect : ∀ ownerLabel ∈ chartActiveSet, ∀ otherLabel ∈ chartActiveSet,
      otherLabel ≠ ownerLabel →
        privateAtom (chartActiveSubset ownerLabel) ∉ chartActiveSubset otherLabel := by
    intro ownerLabel hownerMem otherLabel hotherMem hne
    have howner := mem_of_isActiveFamily hfamily hownerMem
    have hother := mem_of_isActiveFamily hfamily hotherMem
    have hdistinct : chartActiveSubset ownerLabel ≠ chartActiveSubset otherLabel := by
      intro hsame
      exact hne (hsimple otherLabel hotherMem ownerLabel hownerMem hsame.symm)
    exact hnotMem _ howner _ hother hdistinct
  rcases value_eq_neg_inv_size_or_zero_le_of_privateAtomSelector hdata hselect with
    hfloor | hnonneg
  · rw [hfloor, threeMemberEliminant]
    norm_num
  · linarith

/-- The private representative of each member of `Gtz.chartTriplePairwiseMeetFamily`:
`{0,1,5} |-> 5`, `{0,2,4} |-> 4`, `{1,2,3} |-> 3`.  Off the family the value is irrelevant
and is fixed at `3`. -/
def pairwiseMeetPrivateAtom (block : Finset (Fin 6)) : Fin 6 :=
  if block = ({0, 1, 5} : Finset (Fin 6)) then 5
  else if block = ({0, 2, 4} : Finset (Fin 6)) then 4 else 3

/-- **THE COMBINATORIAL CHECK**, decided over the subsets of `Fin 6`: distinct members of
the pairwise-meet family miss each other's representatives. -/
theorem pairwiseMeetPrivateAtom_notMem :
    ∀ firstBlock ∈ chartTriplePairwiseMeetFamily,
      ∀ secondBlock ∈ chartTriplePairwiseMeetFamily,
        firstBlock ≠ secondBlock → pairwiseMeetPrivateAtom firstBlock ∉ secondBlock := by
  unfold chartTriplePairwiseMeetFamily pairwiseMeetPrivateAtom
  decide

/-- **THE PAIRWISE-MEET INSTANCE OF `Gtz.EliminatesThreeMemberValue` IS DISCHARGED.** -/
theorem eliminatesThreeMemberValue_chartTriplePairwiseMeetFamily :
    EliminatesThreeMemberValue (activeIndex := activeIndex) chartTriplePairwiseMeetFamily :=
  eliminatesThreeMemberValue_of_privateAtomSelector chartTriplePairwiseMeetFamily
    pairwiseMeetPrivateAtom pairwiseMeetPrivateAtom_notMem

/-- **THE PAIRWISE-MEET CLASS IS CLOSED UNCONDITIONALLY.**  The shipped conditional closure
`Gtz.zero_le_value_of_chartTriplePairwiseMeetFamily_of_eliminates` with its hypothesis
supplied. -/
theorem zero_le_value_of_chartTriplePairwiseMeetFamily
    {projectionSix : Matrix (Fin 6) (Fin 6) ℝ} {weightSix : Fin 6 → ℝ} {valueSix : ℝ}
    {activeSetSix : Finset activeIndex} {activeSubsetSix : activeIndex → Finset (Fin 6)}
    {activeWeightSix : activeIndex → ℝ} {tightDirSix : activeIndex → (Fin 6 → ℝ)}
    (design : WeightedDesign 6 3) (hchart : projectionSix = projectionOfDesign design)
    (hdata : IsChartStationaryData 3 projectionSix weightSix valueSix activeSetSix
      activeSubsetSix activeWeightSix tightDirSix)
    (hargmax : IsChartArgmaxValue 3 projectionSix weightSix valueSix)
    (hfamily : IsActiveFamily activeSetSix activeSubsetSix chartTriplePairwiseMeetFamily)
    (hsimple : HasSimpleActiveSubsets activeSetSix activeSubsetSix) :
    0 ≤ valueSix :=
  zero_le_value_of_chartTriplePairwiseMeetFamily_of_eliminates
    eliminatesThreeMemberValue_chartTriplePairwiseMeetFamily design hchart hdata hargmax hfamily
    hsimple

/-- The private representative of each member of `Gtz.chartTripleStarFamily`:
`{0,1,4} |-> 4`, `{0,1,5} |-> 5`, `{0,2,3} |-> 2`. -/
def starPrivateAtom (block : Finset (Fin 6)) : Fin 6 :=
  if block = ({0, 1, 4} : Finset (Fin 6)) then 4
  else if block = ({0, 1, 5} : Finset (Fin 6)) then 5 else 2

/-- **THE COMBINATORIAL CHECK** for the star class. -/
theorem starPrivateAtom_notMem :
    ∀ firstBlock ∈ chartTripleStarFamily, ∀ secondBlock ∈ chartTripleStarFamily,
      firstBlock ≠ secondBlock → starPrivateAtom firstBlock ∉ secondBlock := by
  unfold chartTripleStarFamily starPrivateAtom
  decide

/-- **THE STAR INSTANCE OF `Gtz.EliminatesThreeMemberValue` IS DISCHARGED**, and it is a
CHART-side statement.  The star class is already dead on the LEG side, where
`Gtz.hasSaturatedAtom_chartTripleStarFamily` feeds `Gtz.one_le_value_of_saturatedAtom`,
whose datum is `Gtz.IsQuadricStationaryData`.  `Gtz.EliminatesThreeMemberValue` quantifies
over `Gtz.IsChartStationaryData` and was undischarged there. -/
theorem eliminatesThreeMemberValue_chartTripleStarFamily :
    EliminatesThreeMemberValue (activeIndex := activeIndex) chartTripleStarFamily :=
  eliminatesThreeMemberValue_of_privateAtomSelector chartTripleStarFamily starPrivateAtom
    starPrivateAtom_notMem

/-- **THE STAR CLASS IS CLOSED ON THE CHART SIDE**, through the shipped generic closure
`Gtz.zero_le_value_of_eliminatesThreeMemberValue`. -/
theorem zero_le_value_of_chartTripleStarFamily
    {projectionSix : Matrix (Fin 6) (Fin 6) ℝ} {weightSix : Fin 6 → ℝ} {valueSix : ℝ}
    {activeSetSix : Finset activeIndex} {activeSubsetSix : activeIndex → Finset (Fin 6)}
    {activeWeightSix : activeIndex → ℝ} {tightDirSix : activeIndex → (Fin 6 → ℝ)}
    (design : WeightedDesign 6 3) (hchart : projectionSix = projectionOfDesign design)
    (hdata : IsChartStationaryData 3 projectionSix weightSix valueSix activeSetSix
      activeSubsetSix activeWeightSix tightDirSix)
    (hargmax : IsChartArgmaxValue 3 projectionSix weightSix valueSix)
    (hfamily : IsActiveFamily activeSetSix activeSubsetSix chartTripleStarFamily)
    (hsimple : HasSimpleActiveSubsets activeSetSix activeSubsetSix) :
    0 ≤ valueSix :=
  zero_le_value_of_eliminatesThreeMemberValue
    eliminatesThreeMemberValue_chartTripleStarFamily design hchart hdata hargmax hfamily hsimple

/-- **THE THIRD SURVIVING CLASS IS OUT OF REACH, AND THAT IS A THEOREM.**  In
`Gtz.chartTripleSharedEdgeFamily = {{0,1,2},{0,4,5},{1,2,3}}` the two members other than
`{0,1,2}` already cover all six atoms, so no representative for `{0,1,2}` can avoid both.
Its instance of `Gtz.EliminatesThreeMemberValue` therefore stays a citable hole, and the
route of this file provably does not close it. -/
theorem not_exists_privateAtomSelector_chartTripleSharedEdgeFamily :
    ¬ ∃ privateAtom : Finset (Fin 6) → Fin 6,
        ∀ firstBlock ∈ chartTripleSharedEdgeFamily,
          ∀ secondBlock ∈ chartTripleSharedEdgeFamily,
            firstBlock ≠ secondBlock → privateAtom firstBlock ∉ secondBlock := by
  rintro ⟨privateAtom, hnotMem⟩
  have hfirst : privateAtom ({0, 1, 2} : Finset (Fin 6)) ∉ ({0, 4, 5} : Finset (Fin 6)) :=
    hnotMem _ (by decide) _ (by decide) (by decide)
  have hsecond : privateAtom ({0, 1, 2} : Finset (Fin 6)) ∉ ({1, 2, 3} : Finset (Fin 6)) :=
    hnotMem _ (by decide) _ (by decide) (by decide)
  revert hfirst hsecond
  generalize privateAtom ({0, 1, 2} : Finset (Fin 6)) = escapeAtom
  revert escapeAtom
  decide

/-! ## The degree cap at general `(size, rank)` -/

/-- The number of `level`-subsets of `Fin size` through a fixed atom is
`C(size-1, level-1)`, at general `(size, level)`.  The `(6,3)` instance
`Gtz.card_powersetCard_three_through_atom` is a `decide`; this is
`Finset.card_filter_powersetCard_subset`. -/
theorem card_filter_powersetCard_mem {sizeIndex : ℕ} (level : ℕ) (atomIndex : Fin sizeIndex)
    (hlevel : 1 ≤ level) :
    Finset.card (((Finset.univ : Finset (Fin sizeIndex)).powersetCard level).filter
        (fun selected => atomIndex ∈ selected)) = (sizeIndex - 1).choose (level - 1) := by
  have hrewrite :
      ((Finset.univ : Finset (Fin sizeIndex)).powersetCard level).filter
          (fun selected => atomIndex ∈ selected)
        = ((Finset.univ : Finset (Fin sizeIndex)).powersetCard level).filter
            (fun selected => ({atomIndex} : Finset (Fin sizeIndex)) ⊆ selected) := by
    refine Finset.filter_congr ?_
    intro selected _
    simp [Finset.singleton_subset_iff]
  rw [hrewrite,
    Finset.card_filter_powersetCard_subset ({atomIndex} : Finset (Fin sizeIndex))
      Finset.univ level (Finset.subset_univ _) (by simpa using hlevel)]
  simp [Finset.card_univ]

/-- **THE DEGREE CAP AT GENERAL `(size, rank)`.**  A constant multiplier of value `level`
has degree `C(size-1, rank-1) * level` at every atom, so any design whose weights are capped
by `rank/size` -- exactly the cap
`Gtz.activeWeight_le_rank_div_size_of_isChartStationaryData` supplies on an active set --
satisfies the bound.  At `(6,3)` this is `Gtz.le_multiplierDegree_constant_sixThree`, whose
generalization was recorded as blocked on the counting lemma above. -/
theorem le_multiplierDegree_constant {sizeIndex rankIndex : ℕ}
    (design : WeightedDesign sizeIndex rankIndex) (level : ℝ) (hlevel : 0 ≤ level)
    (hrank : 1 ≤ rankIndex)
    (hcap : ∀ atomIndex : Fin sizeIndex,
      design.weight atomIndex ≤ (rankIndex : ℝ) / (sizeIndex : ℝ))
    (atomIndex : Fin sizeIndex) :
    (∑ _selected ∈ (Finset.univ : Finset (Fin sizeIndex)).powersetCard rankIndex, level)
        * design.weight atomIndex
      ≤ multiplierDegree rankIndex (fun _ => level) atomIndex := by
  have hsizePos : 0 < sizeIndex := Fin.pos atomIndex
  have hsizeReal : (0 : ℝ) < (sizeIndex : ℝ) := by exact_mod_cast hsizePos
  have hleft :
      (∑ _selected ∈ (Finset.univ : Finset (Fin sizeIndex)).powersetCard rankIndex, level)
        = (sizeIndex.choose rankIndex : ℝ) * level := by
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hright : multiplierDegree rankIndex (fun _ => level) atomIndex
      = ((sizeIndex - 1).choose (rankIndex - 1) : ℝ) * level := by
    rw [multiplierDegree, Finset.sum_const,
      card_filter_powersetCard_mem rankIndex atomIndex hrank, nsmul_eq_mul]
  have habsorb : sizeIndex * (sizeIndex - 1).choose (rankIndex - 1)
      = sizeIndex.choose rankIndex * rankIndex := by
    obtain ⟨sizePred, rfl⟩ : ∃ sizePred, sizeIndex = sizePred + 1 := ⟨sizeIndex - 1, by omega⟩
    obtain ⟨rankPred, rfl⟩ : ∃ rankPred, rankIndex = rankPred + 1 := ⟨rankIndex - 1, by omega⟩
    simpa using Nat.add_one_mul_choose_eq sizePred rankPred
  have habsorbReal : (sizeIndex : ℝ) * ((sizeIndex - 1).choose (rankIndex - 1) : ℝ)
      = (sizeIndex.choose rankIndex : ℝ) * (rankIndex : ℝ) := by
    exact_mod_cast congrArg (fun count : ℕ => (count : ℝ)) habsorb
  rw [hleft, hright]
  have hstep : (sizeIndex.choose rankIndex : ℝ) * level * design.weight atomIndex
      ≤ (sizeIndex.choose rankIndex : ℝ) * level * ((rankIndex : ℝ) / (sizeIndex : ℝ)) := by
    have hnonneg : (0 : ℝ) ≤ (sizeIndex.choose rankIndex : ℝ) * level :=
      mul_nonneg (by positivity) hlevel
    exact mul_le_mul_of_nonneg_left (hcap atomIndex) hnonneg
  refine hstep.trans (le_of_eq ?_)
  field_simp
  linear_combination (-level) * habsorbReal

/-! ## Non-vacuity: both branches attained -/

/-- The shipped octahedron datum owns its atoms: its tight directions are the six coordinate
vectors, so atom `c` is owned by label `c`. -/
theorem hasPrivateAtomSystem_chartOcta :
    HasPrivateAtomSystem (Finset.univ : Finset (Fin 6)) chartOctaTightDir
      (fun atomLabel => {atomLabel}) := by
  intro ownerLabel _ atomIndex hatomMem otherLabel _ hne
  rw [Finset.mem_singleton] at hatomMem
  subst hatomMem
  rw [chartOctaTightDir, Pi.single_apply, if_neg (Ne.symm hne)]

/-- **THE PRIVATE-ATOM BUNDLE IS INHABITED, AT THE OPEN CELL `(6,3)`.**  The shipped
`Gtz.chartOctaProjection_isChartStationaryData` carries a private system with one owned atom
per label, so the graded floor is not a statement about the empty set.  Its value is `1/3`
-- the second branch of the dichotomy. -/
theorem exists_isChartStationaryData_hasPrivateAtomSystem :
    ∃ (projection : Matrix (Fin 6) (Fin 6) ℝ) (weight : Fin 6 → ℝ) (value : ℝ)
      (activeSubset : Fin 6 → Finset (Fin 6)) (activeWeight : Fin 6 → ℝ)
      (tightDir : Fin 6 → (Fin 6 → ℝ)) (privateAtomSet : Fin 6 → Finset (Fin 6)),
      IsChartStationaryData 3 projection weight value (Finset.univ : Finset (Fin 6))
          activeSubset activeWeight tightDir
        ∧ HasPrivateAtomSystem (Finset.univ : Finset (Fin 6)) tightDir privateAtomSet
        ∧ ∀ activeLabel ∈ (Finset.univ : Finset (Fin 6)),
            (privateAtomSet activeLabel).Nonempty :=
  ⟨chartOctaProjection, chartOctaWeight, 1 / 3, chartOctaSubset, chartOctaMultiplierWeight,
    chartOctaTightDir, fun atomLabel => {atomLabel},
    chartOctaProjection_isChartStationaryData, hasPrivateAtomSystem_chartOcta,
    fun activeLabel _ => Finset.singleton_nonempty activeLabel⟩

/-- The shipped uniform two-block family `{0,1}`, `{2,3}` is pairwise disjoint. -/
theorem pairwiseDisjoint_chartTwoBlockUniformSubset :
    ∀ firstLabel ∈ (Finset.univ : Finset (Fin 2)),
      ∀ secondLabel ∈ (Finset.univ : Finset (Fin 2)), firstLabel ≠ secondLabel →
        Disjoint (chartTwoBlockUniformSubset firstLabel)
          (chartTwoBlockUniformSubset secondLabel) := by
  unfold chartTwoBlockUniformSubset
  decide

/-- **THE FIRST BRANCH OF THE DICHOTOMY IS ATTAINED**, so it cannot be deleted.  The shipped
uniform two-block datum `Gtz.chartTwoBlockUniformProjection_isChartStationaryData` has
pairwise disjoint subsets and `value = -1/4 = -1/size` exactly.  It is the lattice point
`capturedRank = 0`.  [It is not ADMISSIBLE -- `Gtz.not_isChartStationaryData_of_value_eq_neg_inv_size`
excludes exactly this value once `Gtz.IsChartArgmaxValue` is attached -- which is why the
`-1/size` branch is where the endgame expects the stratum to sit, and why the dichotomy is
useful rather than merely true.] -/
theorem exists_isChartStationaryData_pairwiseDisjoint_value_eq_neg_inv_size :
    ∃ (projection : Matrix (Fin 4) (Fin 4) ℝ) (weight : Fin 4 → ℝ) (value : ℝ)
      (activeSubset : Fin 2 → Finset (Fin 4)) (activeWeight : Fin 2 → ℝ)
      (tightDir : Fin 2 → (Fin 4 → ℝ)),
      IsChartStationaryData 2 projection weight value (Finset.univ : Finset (Fin 2))
          activeSubset activeWeight tightDir
        ∧ (∀ firstLabel ∈ (Finset.univ : Finset (Fin 2)),
            ∀ secondLabel ∈ (Finset.univ : Finset (Fin 2)), firstLabel ≠ secondLabel →
              Disjoint (activeSubset firstLabel) (activeSubset secondLabel))
        ∧ value = -(((4 : ℕ) : ℝ))⁻¹ :=
  ⟨chartTwoBlockUniformProjection, chartTwoBlockUniformWeight, -(4 : ℝ)⁻¹,
    chartTwoBlockUniformSubset, chartTwoBlockUniformMultiplierWeight,
    chartTwoBlockUniformTightDir, chartTwoBlockUniformProjection_isChartStationaryData,
    pairwiseDisjoint_chartTwoBlockUniformSubset, by norm_num⟩

/-- Uniform weights on four atoms. -/
noncomputable def chartFullRankWeight : Fin 4 → ℝ := fun _ => (4 : ℝ)⁻¹

/-- One active label, carrying every atom.  Pairwise disjointness is then vacuous, which is
the cheapest inhabited instance of the hypothesis. -/
def chartFullRankSubset : Fin 1 → Finset (Fin 4) := fun _ => Finset.univ

/-- The single multiplier is one, as the bundle's `activeWeight_sum_one` demands. -/
noncomputable def chartFullRankMultiplierWeight : Fin 1 → ℝ := fun _ => 1

/-- The all-halves direction: a unit vector on four atoms whose every coordinate square is
`1/4 = (rank/size) / rank`, which is what the constant assembly diagonal forces. -/
noncomputable def chartFullRankTightDir : Fin 1 → (Fin 4 → ℝ) := fun _ _ => (2 : ℝ)⁻¹

/-- The assembly is the constant matrix `1/4`, so its diagonal is `1/size` and it commutes
with the identity chart for free. -/
theorem chartFullRankMultiplierAssembly_eq :
    chartMultiplierAssembly (Finset.univ : Finset (Fin 1)) chartFullRankMultiplierWeight
        chartFullRankTightDir
      = Matrix.of (fun _ _ : Fin 4 => (4 : ℝ)⁻¹) := by
  ext rowIndex colIndex
  rw [chartMultiplierAssembly_apply, Fin.sum_univ_one]
  simp only [chartFullRankMultiplierWeight, chartFullRankTightDir, Matrix.of_apply]
  norm_num

/-- **A RATIONAL `(4,4)` DATUM AT `value = 3/4`.**  The identity chart, uniform weights, one
active label with the all-halves tight direction.  Every field of the bundle is arithmetic;
nothing irrational appears. -/
theorem chartFullRank_isChartStationaryData :
    IsChartStationaryData 4 (1 : Matrix (Fin 4) (Fin 4) ℝ) chartFullRankWeight (3 / 4)
      (Finset.univ : Finset (Fin 1)) chartFullRankSubset chartFullRankMultiplierWeight
      chartFullRankTightDir where
  isSymmetric := Matrix.transpose_one
  isIdempotent := by simp
  hasTraceRank := by simp
  weight_pos := by intro _; norm_num [chartFullRankWeight]
  weight_sum_one := by norm_num [chartFullRankWeight, Fin.sum_univ_four]
  activeWeight_nonneg := by intro _ _; norm_num [chartFullRankMultiplierWeight]
  activeWeight_sum_one := by norm_num [chartFullRankMultiplierWeight, Fin.sum_univ_one]
  activeSubset_card := by intro _ _; simp [chartFullRankSubset]
  tightDir_unit := by
    intro _ _
    simp only [chartFullRankTightDir, dotProduct, Fin.sum_univ_four]
    norm_num
  tightDir_support := by
    intro _ _ atomIndex hnotMem
    simp [chartFullRankSubset] at hnotMem
  tightDir_isTight := by
    intro _ _ atomIndex _
    rw [chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec,
      Matrix.mulVec_diagonal]
    simp only [chartFullRankTightDir, chartFullRankWeight]
    norm_num
  assembly_diagonal := by
    intro atomIndex
    rw [chartFullRankMultiplierAssembly_eq, Matrix.of_apply]
    norm_num
  assembly_commutes := by rw [Matrix.one_mul, Matrix.mul_one]

/-- One active label: pairwise disjointness holds vacuously. -/
theorem chartFullRank_pairwiseDisjoint_activeSubset :
    ∀ firstLabel ∈ (Finset.univ : Finset (Fin 1)),
      ∀ secondLabel ∈ (Finset.univ : Finset (Fin 1)), firstLabel ≠ secondLabel →
        Disjoint (chartFullRankSubset firstLabel) (chartFullRankSubset secondLabel) := by
  unfold chartFullRankSubset
  decide

/-- **THE SECOND BRANCH IS ATTAINED, SO THE BOUND `(rank-1)/size` IS SHARP.**  The `(4,4)`
datum above has pairwise disjoint subsets and `value = 3/4 = (rank-1)/size` exactly.  It is
the lattice point `capturedRank = 1`, where `rank * capturedRank = size` shows the cap of
`exists_value_eq_of_pairwiseDisjoint_activeSubset` is tight as well. -/
theorem exists_isChartStationaryData_pairwiseDisjoint_value_eq_rank_sub_one_div_size :
    ∃ (projection : Matrix (Fin 4) (Fin 4) ℝ) (weight : Fin 4 → ℝ) (value : ℝ)
      (activeSubset : Fin 1 → Finset (Fin 4)) (activeWeight : Fin 1 → ℝ)
      (tightDir : Fin 1 → (Fin 4 → ℝ)),
      IsChartStationaryData 4 projection weight value (Finset.univ : Finset (Fin 1))
          activeSubset activeWeight tightDir
        ∧ (∀ firstLabel ∈ (Finset.univ : Finset (Fin 1)),
            ∀ secondLabel ∈ (Finset.univ : Finset (Fin 1)), firstLabel ≠ secondLabel →
              Disjoint (activeSubset firstLabel) (activeSubset secondLabel))
        ∧ value = (((4 : ℕ) : ℝ) - 1) * (((4 : ℕ) : ℝ))⁻¹ :=
  ⟨1, chartFullRankWeight, 3 / 4, chartFullRankSubset, chartFullRankMultiplierWeight,
    chartFullRankTightDir, chartFullRank_isChartStationaryData,
    chartFullRank_pairwiseDisjoint_activeSubset, by norm_num⟩

end Gtz

import Gtz.Wave.DenseKernelLineDichotomy
import Gtz.Wave.GapRowDictionary
import Gtz.Wave.CarrierPairExtraction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The dense block geometry — the shared-block kills and the carrier corner calculus

Every dense profile of the rank-five and rank-six rungs carries the same
two structures, and this module lands both without a Gram hypothesis.

The first structure is the block eigen system.  A dense basis support has
the cardinality of the rank, thus it equals the block, and the direction
has no zero coordinate on it.  The tight equation then says that the
three-by-three gap block has the direction as an eigenvector at the chart
value.  The determinant of the shifted block vanishes, the three
cofactor identities hold, and the pair minors cross-multiply.  Two basis
slots on ONE block are strongly restricted: if one pairwise cross
determinant vanishes, the left inverse reads a contradiction against the
gap floor.  Three basis slots on one block always die.

The second structure is the carrier corner.  The carried row of an atom
is a left eigenvector of the principal submatrix of the coefficient
matrix that the carriers index, at the shifted weight of the atom.  At a
multiplicity-two atom this is one scalar characteristic equation in four
coefficient entries.  Two atoms with one carrier pair read the corner
trace exactly.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.datumTightSupport_eq_activeSubset_of_card` — the dense support is
  the block.
* `Gtz.exists_support_triple`, `Gtz.block_eigen_row` — **THE BLOCK EIGEN
  SYSTEM.**
* `Gtz.block_cofactor_first`, `Gtz.block_cofactor_second`,
  `Gtz.block_cofactor_third`, `Gtz.block_minor_cross`,
  `Gtz.block_determinant_zero` — **THE COFACTOR CALCULUS.**
* `Gtz.dense_block_shifted_determinant_zero` — the chart form of the
  vanishing determinant.
* `Gtz.leftInverse_read_pair_combination`,
  `Gtz.leftInverse_read_triple_combination` — the coefficient reads.
* `Gtz.false_of_shared_block_cross_zero` — **THE SHARED-BLOCK AXIS
  KILL.**
* `Gtz.false_of_three_shared_block_slots` — **THE BLOCK CAP.**
* `Gtz.carrier_pair_characteristic` — **THE CARRIER CORNER EQUATION.**
* `Gtz.shared_carrier_pair_trace` — the exact corner trace.
* `Gtz.shifted_weight_sum`, `Gtz.shifted_weight_lt_one` — the shifted
  weight arithmetic.
* `Gtz.SixThreeCrux.gap_diagonal_ne_value` — the floor in the form the
  kills consume.
* `Gtz.RankFiveFrame.false_of_shared_support_cross_zero`,
  `Gtz.RankFiveFrame.false_of_three_shared_supports`,
  `Gtz.RankSixFrame.false_of_shared_support_cross_zero`,
  `Gtz.RankSixFrame.false_of_three_shared_supports` — the frame forms.
* `Gtz.RankFiveFrame.exists_carrier_pair_characteristic`,
  `Gtz.RankSixFrame.exists_carrier_pair_characteristic` — the corner
  equation of every double atom.
* `Gtz.RankFiveFrame.shifted_weight_sum`,
  `Gtz.RankSixFrame.shifted_weight_sum` — the six-atom shifted sum.

## Vacuity

The frame statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no crux
exists, thus no frame exists.  The cofactor calculus and the corner
equations are unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the dense support is the block -/

/-- A support at the cardinality of the rank fills the block. -/
theorem datumTightSupport_eq_activeSubset_of_card
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    (hcard : (datumTightSupport tightDir label).card = rank) :
    datumTightSupport tightDir label = activeSubset label := by
  refine Finset.eq_of_subset_of_card_le (datumTightSupport_subset hdata hmem) ?_
  rw [hcard, hdata.activeSubset_card label hmem]

/-- A card-three support names three distinct atoms. -/
theorem exists_support_triple {label : activeIndex}
    (hcard : (datumTightSupport tightDir label).card = 3) :
    ∃ atomA atomB atomC : Fin size, atomA ≠ atomB ∧ atomA ≠ atomC ∧ atomB ≠ atomC
      ∧ datumTightSupport tightDir label = {atomA, atomB, atomC} :=
  Finset.card_eq_three.mp hcard

/-- Off a named support triple the direction vanishes. -/
theorem tightDir_eq_zero_of_support_triple {label : activeIndex}
    {atomA atomB atomC : Fin size}
    (hsupport : datumTightSupport tightDir label = {atomA, atomB, atomC})
    {atomIndex : Fin size} (hA : atomIndex ≠ atomA) (hB : atomIndex ≠ atomB)
    (hC : atomIndex ≠ atomC) : tightDir label atomIndex = 0 := by
  by_contra hne
  have hmemSupport : atomIndex ∈ datumTightSupport tightDir label :=
    mem_datumTightSupport.mpr hne
  rw [hsupport] at hmemSupport
  rcases Finset.mem_insert.mp hmemSupport with heq | hrest
  · exact hA heq
  rcases Finset.mem_insert.mp hrest with heq | hlast
  · exact hB heq
  · exact hC (Finset.mem_singleton.mp hlast)

/-- On a named support triple the direction has no zero coordinate. -/
theorem tightDir_ne_zero_of_support_triple {label : activeIndex}
    {atomA atomB atomC : Fin size}
    (hsupport : datumTightSupport tightDir label = {atomA, atomB, atomC})
    {atomIndex : Fin size}
    (hmem : atomIndex ∈ ({atomA, atomB, atomC} : Finset (Fin size))) :
    tightDir label atomIndex ≠ 0 := by
  refine mem_datumTightSupport.mp ?_
  rw [hsupport]
  exact hmem

/-! ## Layer 2 — the block eigen system -/

/-- **THE BLOCK EIGEN ROW.**  At a label with a named card-three support,
each support row of the gap contracts the direction to the value
multiple. -/
theorem block_eigen_row
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomA atomB atomC : Fin size} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC)
    (hsupport : datumTightSupport tightDir label = {atomA, atomB, atomC})
    {atomRow : Fin size}
    (hrow : atomRow ∈ ({atomA, atomB, atomC} : Finset (Fin size))) :
    chartStationaryGap projection weight atomRow atomA * tightDir label atomA
      + chartStationaryGap projection weight atomRow atomB * tightDir label atomB
      + chartStationaryGap projection weight atomRow atomC * tightDir label atomC
      = value * tightDir label atomRow := by
  refine gap_row_eigen_triple hdata hmem ?_ hAB hAC hBC ?_
  · refine datumTightSupport_subset hdata hmem ?_
    rw [hsupport]
    exact hrow
  · intro atomIndex hA hB hC
    exact tightDir_eq_zero_of_support_triple hsupport hA hB hC

/-! ## Layer 3 — the cofactor calculus -/

/-- The first cofactor identity of a symmetric three-atom eigen system. -/
theorem block_cofactor_first {entryAA entryAB entryAC entryBB entryBC : ℝ}
    {coordA coordB coordC eigen : ℝ}
    (hrowA : entryAA * coordA + entryAB * coordB + entryAC * coordC
      = eigen * coordA)
    (hrowB : entryAB * coordA + entryBB * coordB + entryBC * coordC
      = eigen * coordB) :
    ((entryAA - eigen) * (entryBB - eigen) - entryAB * entryAB) * coordA
      = (entryAB * entryBC - (entryBB - eigen) * entryAC) * coordC := by
  linear_combination (entryBB - eigen) * hrowA - entryAB * hrowB

/-- The second cofactor identity. -/
theorem block_cofactor_second {entryAA entryAB entryAC entryBB entryBC : ℝ}
    {coordA coordB coordC eigen : ℝ}
    (hrowA : entryAA * coordA + entryAB * coordB + entryAC * coordC
      = eigen * coordA)
    (hrowB : entryAB * coordA + entryBB * coordB + entryBC * coordC
      = eigen * coordB) :
    ((entryAA - eigen) * (entryBB - eigen) - entryAB * entryAB) * coordB
      = (entryAB * entryAC - (entryAA - eigen) * entryBC) * coordC := by
  linear_combination (entryAA - eigen) * hrowB - entryAB * hrowA

/-- The third cofactor identity: the same cofactor prices the opposite
pair minor. -/
theorem block_cofactor_third {entryAB entryAC entryBB entryBC entryCC : ℝ}
    {coordA coordB coordC eigen : ℝ}
    (hrowB : entryAB * coordA + entryBB * coordB + entryBC * coordC
      = eigen * coordB)
    (hrowC : entryAC * coordA + entryBC * coordB + entryCC * coordC
      = eigen * coordC) :
    ((entryBB - eigen) * (entryCC - eigen) - entryBC * entryBC) * coordC
      = (entryAB * entryBC - (entryBB - eigen) * entryAC) * coordA := by
  linear_combination (entryBB - eigen) * hrowC - entryBC * hrowB

/-- **THE PAIR MINOR CROSS LAW.**  The two shifted pair minors that share
the middle atom cross-multiply with the squared outer coordinates. -/
theorem block_minor_cross {minorAB minorBC cofactor coordA coordC : ℝ}
    (hfirst : minorAB * coordA = cofactor * coordC)
    (hthird : minorBC * coordC = cofactor * coordA) :
    minorAB * coordA * coordA = minorBC * coordC * coordC := by
  linear_combination coordA * hfirst - coordC * hthird

/-- **THE VANISHING DETERMINANT.**  A symmetric three-atom eigen system
with a nonzero third coordinate has a singular shifted block. -/
theorem block_determinant_zero {entryAA entryAB entryAC entryBB entryBC entryCC : ℝ}
    {coordA coordB coordC eigen : ℝ}
    (hrowA : entryAA * coordA + entryAB * coordB + entryAC * coordC
      = eigen * coordA)
    (hrowB : entryAB * coordA + entryBB * coordB + entryBC * coordC
      = eigen * coordB)
    (hrowC : entryAC * coordA + entryBC * coordB + entryCC * coordC
      = eigen * coordC)
    (hcoordC : coordC ≠ 0) :
    (entryAA - eigen) * ((entryBB - eigen) * (entryCC - eigen) - entryBC * entryBC)
        - entryAB * (entryAB * (entryCC - eigen) - entryAC * entryBC)
        + entryAC * (entryAB * entryBC - (entryBB - eigen) * entryAC) = 0 := by
  have hproduct : ((entryAA - eigen)
        * ((entryBB - eigen) * (entryCC - eigen) - entryBC * entryBC)
        - entryAB * (entryAB * (entryCC - eigen) - entryAC * entryBC)
        + entryAC * (entryAB * entryBC - (entryBB - eigen) * entryAC)) * coordC
      = 0 := by
    linear_combination (entryAB * entryBC - (entryBB - eigen) * entryAC) * hrowA
      + (entryAB * entryAC - (entryAA - eigen) * entryBC) * hrowB
      + ((entryAA - eigen) * (entryBB - eigen) - entryAB * entryAB) * hrowC
  rcases mul_eq_zero.mp hproduct with hcase | hcase
  · exact hcase
  · exact absurd hcase hcoordC

/-- The chart form: the shifted gap block of a dense support is
singular. -/
theorem dense_block_shifted_determinant_zero
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomA atomB atomC : Fin size} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC)
    (hsupport : datumTightSupport tightDir label = {atomA, atomB, atomC}) :
    (chartStationaryGap projection weight atomA atomA - value)
        * ((chartStationaryGap projection weight atomB atomB - value)
            * (chartStationaryGap projection weight atomC atomC - value)
          - chartStationaryGap projection weight atomB atomC
            * chartStationaryGap projection weight atomB atomC)
      - chartStationaryGap projection weight atomA atomB
        * (chartStationaryGap projection weight atomA atomB
            * (chartStationaryGap projection weight atomC atomC - value)
          - chartStationaryGap projection weight atomA atomC
            * chartStationaryGap projection weight atomB atomC)
      + chartStationaryGap projection weight atomA atomC
        * (chartStationaryGap projection weight atomA atomB
            * chartStationaryGap projection weight atomB atomC
          - (chartStationaryGap projection weight atomB atomB - value)
            * chartStationaryGap projection weight atomA atomC) = 0 := by
  have hrowA := block_eigen_row hdata hmem hAB hAC hBC hsupport
    (Finset.mem_insert_self _ _)
  have hrowB := block_eigen_row hdata hmem hAB hAC hBC hsupport
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hrowC := block_eigen_row hdata hmem hAB hAC hBC hsupport
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _)))
  rw [gap_entry_symm hdata atomB atomA] at hrowB
  rw [gap_entry_symm hdata atomC atomA, gap_entry_symm hdata atomC atomB] at hrowC
  exact block_determinant_zero hrowA hrowB hrowC
    (tightDir_ne_zero_of_support_triple hsupport
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))))

/-! ## Layer 4 — the coefficient reads -/

/-- A vanishing two-slot combination has a vanishing first coefficient. -/
theorem leftInverse_read_pair_combination
    (basisLabel : Fin basisCount → activeIndex)
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {slotOne slotTwo : Fin basisCount} (hslot : slotOne ≠ slotTwo)
    {coeffOne coeffTwo : ℝ}
    (hzero : coeffOne • tightDir (basisLabel slotOne)
      + coeffTwo • tightDir (basisLabel slotTwo) = 0) :
    coeffOne = 0 := by
  have hstep := congrArg (fun ambientVec => leftInv *ᵥ ambientVec) hzero
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero] at hstep
  rw [leftInverse_mulVec_tightDir_basisLabel basisLabel leftInv hleft,
    leftInverse_mulVec_tightDir_basisLabel basisLabel leftInv hleft] at hstep
  have hentry := congrFun hstep slotOne
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne hslot, smul_eq_mul, smul_eq_mul, mul_one, mul_zero,
    add_zero] at hentry
  exact hentry

/-- A vanishing three-slot combination has a vanishing third
coefficient. -/
theorem leftInverse_read_triple_combination
    (basisLabel : Fin basisCount → activeIndex)
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {slotOne slotTwo slotThree : Fin basisCount}
    (hOne : slotThree ≠ slotOne) (hTwo : slotThree ≠ slotTwo)
    {coeffOne coeffTwo coeffThree : ℝ}
    (hzero : coeffOne • tightDir (basisLabel slotOne)
        + coeffTwo • tightDir (basisLabel slotTwo)
        + coeffThree • tightDir (basisLabel slotThree) = 0) :
    coeffThree = 0 := by
  have hstep := congrArg (fun ambientVec => leftInv *ᵥ ambientVec) hzero
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero] at hstep
  rw [leftInverse_mulVec_tightDir_basisLabel basisLabel leftInv hleft,
    leftInverse_mulVec_tightDir_basisLabel basisLabel leftInv hleft,
    leftInverse_mulVec_tightDir_basisLabel basisLabel leftInv hleft] at hstep
  have hentry := congrFun hstep slotThree
  rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
    Pi.single_eq_same, Pi.single_eq_of_ne hOne, Pi.single_eq_of_ne hTwo,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one, mul_zero, mul_zero,
    add_zero, zero_add] at hentry
  exact hentry

/-! ## Layer 5 — the shared-block kills -/

/-- **THE SHARED-BLOCK AXIS KILL.**  Two basis slots on one dense block
with a vanishing pairwise cross determinant force a coordinate axis into
the span of the two directions.  The axis reads the gap diagonal as the
value, against the floor. -/
theorem false_of_shared_block_cross_zero
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {slotOne slotTwo : Fin basisCount} (hslot : slotOne ≠ slotTwo)
    (hmemOne : basisLabel slotOne ∈ activeSet)
    (hmemTwo : basisLabel slotTwo ∈ activeSet)
    {atomA atomB atomC : Fin size} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport tightDir (basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport tightDir (basisLabel slotTwo)
      = {atomA, atomB, atomC})
    (hdiag : chartStationaryGap projection weight atomC atomC ≠ value)
    (hcross : tightDir (basisLabel slotOne) atomA
          * tightDir (basisLabel slotTwo) atomB
        - tightDir (basisLabel slotOne) atomB
          * tightDir (basisLabel slotTwo) atomA = 0) :
    False := by
  have hmemC : atomC ∈ ({atomA, atomB, atomC} : Finset (Fin size)) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  have hmemB : atomB ∈ ({atomA, atomB, atomC} : Finset (Fin size)) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hrowOne := block_eigen_row hdata hmemOne hAB hAC hBC hsupportOne hmemC
  have hrowTwo := block_eigen_row hdata hmemTwo hAB hAC hBC hsupportTwo hmemC
  have hshift : chartStationaryGap projection weight atomC atomC - value ≠ 0 :=
    sub_ne_zero.mpr hdiag
  have hproduct : (chartStationaryGap projection weight atomC atomC - value)
      * (tightDir (basisLabel slotTwo) atomB * tightDir (basisLabel slotOne) atomC
        - tightDir (basisLabel slotOne) atomB
          * tightDir (basisLabel slotTwo) atomC) = 0 := by
    linear_combination tightDir (basisLabel slotTwo) atomB * hrowOne
      - tightDir (basisLabel slotOne) atomB * hrowTwo
      - chartStationaryGap projection weight atomC atomA * hcross
  have hthird : tightDir (basisLabel slotTwo) atomB
      * tightDir (basisLabel slotOne) atomC
      - tightDir (basisLabel slotOne) atomB
        * tightDir (basisLabel slotTwo) atomC = 0 := by
    rcases mul_eq_zero.mp hproduct with hcase | hcase
    · exact absurd hcase hshift
    · exact hcase
  have hcombination : tightDir (basisLabel slotTwo) atomB
        • tightDir (basisLabel slotOne)
      + (-(tightDir (basisLabel slotOne) atomB))
        • tightDir (basisLabel slotTwo) = 0 := by
    funext atomIndex
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, neg_mul]
    by_cases hA : atomIndex = atomA
    · rw [hA]
      linear_combination hcross
    by_cases hB : atomIndex = atomB
    · rw [hB]
      ring
    by_cases hC : atomIndex = atomC
    · rw [hC]
      linear_combination hthird
    · rw [tightDir_eq_zero_of_support_triple hsupportOne hA hB hC,
        tightDir_eq_zero_of_support_triple hsupportTwo hA hB hC]
      ring
  have hzeroCoeff := leftInverse_read_pair_combination basisLabel leftInv hleft
    hslot hcombination
  exact tightDir_ne_zero_of_support_triple hsupportTwo hmemB hzeroCoeff

/-- **THE BLOCK CAP.**  Three basis slots never share one dense block:
the third direction is a combination of the first two on two atoms, and
the leftover axis reads the gap diagonal as the value. -/
theorem false_of_three_shared_block_slots
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {slotOne slotTwo slotThree : Fin basisCount}
    (hOneTwo : slotOne ≠ slotTwo) (hThreeOne : slotThree ≠ slotOne)
    (hThreeTwo : slotThree ≠ slotTwo)
    (hmemOne : basisLabel slotOne ∈ activeSet)
    (hmemTwo : basisLabel slotTwo ∈ activeSet)
    (hmemThree : basisLabel slotThree ∈ activeSet)
    {atomA atomB atomC : Fin size} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport tightDir (basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport tightDir (basisLabel slotTwo)
      = {atomA, atomB, atomC})
    (hsupportThree : datumTightSupport tightDir (basisLabel slotThree)
      = {atomA, atomB, atomC})
    (hdiag : chartStationaryGap projection weight atomC atomC ≠ value) :
    False := by
  by_cases hcross : tightDir (basisLabel slotOne) atomA
        * tightDir (basisLabel slotTwo) atomB
      - tightDir (basisLabel slotOne) atomB
        * tightDir (basisLabel slotTwo) atomA = 0
  · exact false_of_shared_block_cross_zero hdata basisLabel leftInv hleft hOneTwo
      hmemOne hmemTwo hAB hAC hBC hsupportOne hsupportTwo hdiag hcross
  · have hmemC : atomC ∈ ({atomA, atomB, atomC} : Finset (Fin size)) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))
    have hrowOne := block_eigen_row hdata hmemOne hAB hAC hBC hsupportOne hmemC
    have hrowTwo := block_eigen_row hdata hmemTwo hAB hAC hBC hsupportTwo hmemC
    have hrowThree := block_eigen_row hdata hmemThree hAB hAC hBC hsupportThree
      hmemC
    set scaleOne : ℝ := tightDir (basisLabel slotThree) atomA
        * tightDir (basisLabel slotTwo) atomB
      - tightDir (basisLabel slotThree) atomB
        * tightDir (basisLabel slotTwo) atomA with hscaleOne
    set scaleTwo : ℝ := tightDir (basisLabel slotOne) atomA
        * tightDir (basisLabel slotThree) atomB
      - tightDir (basisLabel slotOne) atomB
        * tightDir (basisLabel slotThree) atomA with hscaleTwo
    set scaleThree : ℝ := -(tightDir (basisLabel slotOne) atomA
        * tightDir (basisLabel slotTwo) atomB
      - tightDir (basisLabel slotOne) atomB
        * tightDir (basisLabel slotTwo) atomA) with hscaleThree
    have hvanishA : scaleOne * tightDir (basisLabel slotOne) atomA
        + scaleTwo * tightDir (basisLabel slotTwo) atomA
        + scaleThree * tightDir (basisLabel slotThree) atomA = 0 := by
      rw [hscaleOne, hscaleTwo, hscaleThree]
      ring
    have hvanishB : scaleOne * tightDir (basisLabel slotOne) atomB
        + scaleTwo * tightDir (basisLabel slotTwo) atomB
        + scaleThree * tightDir (basisLabel slotThree) atomB = 0 := by
      rw [hscaleOne, hscaleTwo, hscaleThree]
      ring
    have hproduct : (chartStationaryGap projection weight atomC atomC - value)
        * (scaleOne * tightDir (basisLabel slotOne) atomC
          + scaleTwo * tightDir (basisLabel slotTwo) atomC
          + scaleThree * tightDir (basisLabel slotThree) atomC) = 0 := by
      linear_combination scaleOne * hrowOne + scaleTwo * hrowTwo
        + scaleThree * hrowThree
        - chartStationaryGap projection weight atomC atomA * hvanishA
        - chartStationaryGap projection weight atomC atomB * hvanishB
    have hshift : chartStationaryGap projection weight atomC atomC - value ≠ 0 :=
      sub_ne_zero.mpr hdiag
    have hvanishC : scaleOne * tightDir (basisLabel slotOne) atomC
        + scaleTwo * tightDir (basisLabel slotTwo) atomC
        + scaleThree * tightDir (basisLabel slotThree) atomC = 0 := by
      rcases mul_eq_zero.mp hproduct with hcase | hcase
      · exact absurd hcase hshift
      · exact hcase
    have hcombination : scaleOne • tightDir (basisLabel slotOne)
        + scaleTwo • tightDir (basisLabel slotTwo)
        + scaleThree • tightDir (basisLabel slotThree) = 0 := by
      funext atomIndex
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      by_cases hA : atomIndex = atomA
      · rw [hA]
        exact hvanishA
      by_cases hB : atomIndex = atomB
      · rw [hB]
        exact hvanishB
      by_cases hC : atomIndex = atomC
      · rw [hC]
        exact hvanishC
      · rw [tightDir_eq_zero_of_support_triple hsupportOne hA hB hC,
          tightDir_eq_zero_of_support_triple hsupportTwo hA hB hC,
          tightDir_eq_zero_of_support_triple hsupportThree hA hB hC]
        ring
    have hzeroCoeff := leftInverse_read_triple_combination basisLabel leftInv
      hleft hThreeOne hThreeTwo hcombination
    refine hcross ?_
    rw [hscaleThree] at hzeroCoeff
    linarith [hzeroCoeff]

/-! ## Layer 6 — the carrier corner calculus -/

/-- **THE CARRIER CORNER EQUATION.**  At an atom with exactly two
carriers the shifted weight is an eigenvalue of the two-by-two corner of
the coefficient matrix.  The law needs no Gram hypothesis. -/
theorem carrier_pair_characteristic
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {atomIndex : Fin size} {slotOne slotTwo : Fin basisCount}
    (hslot : slotOne ≠ slotTwo)
    (hmemOne : basisLabel slotOne ∈ activeSet)
    (hmemTwo : basisLabel slotTwo ∈ activeSet)
    (hblockOne : atomIndex ∈ activeSubset (basisLabel slotOne))
    (hblockTwo : atomIndex ∈ activeSubset (basisLabel slotTwo))
    (hcoordOne : tightDir (basisLabel slotOne) atomIndex ≠ 0)
    (hcoordTwo : tightDir (basisLabel slotTwo) atomIndex ≠ 0)
    (hvanish : ∀ slotIndex, slotIndex ≠ slotOne → slotIndex ≠ slotTwo →
      tightDir (basisLabel slotIndex) atomIndex = 0) :
    (coeff slotOne slotOne - (value + weight atomIndex))
        * (coeff slotTwo slotTwo - (value + weight atomIndex))
      = coeff slotOne slotTwo * coeff slotTwo slotOne := by
  have hreadOne := carried_row_reading hdata basisLabel hrepresentation hmemOne
    hblockOne
  have hreadTwo := carried_row_reading hdata basisLabel hrepresentation hmemTwo
    hblockTwo
  have hcollapseOne := sum_collapse_two (termOf := fun slotIndex =>
    tightDir (basisLabel slotIndex) atomIndex * coeff slotIndex slotOne) hslot
    (fun slotIndex hOne hTwo => by rw [hvanish slotIndex hOne hTwo, zero_mul])
  have hcollapseTwo := sum_collapse_two (termOf := fun slotIndex =>
    tightDir (basisLabel slotIndex) atomIndex * coeff slotIndex slotTwo) hslot
    (fun slotIndex hOne hTwo => by rw [hvanish slotIndex hOne hTwo, zero_mul])
  rw [hcollapseOne] at hreadOne
  rw [hcollapseTwo] at hreadTwo
  have hproduct : ((coeff slotOne slotOne - (value + weight atomIndex))
        * (coeff slotTwo slotTwo - (value + weight atomIndex))
      - coeff slotOne slotTwo * coeff slotTwo slotOne)
      * (tightDir (basisLabel slotOne) atomIndex
        * tightDir (basisLabel slotTwo) atomIndex) = 0 := by
    linear_combination (coeff slotTwo slotTwo - (value + weight atomIndex))
        * tightDir (basisLabel slotTwo) atomIndex * hreadOne
      - coeff slotTwo slotOne * tightDir (basisLabel slotTwo) atomIndex
        * hreadTwo
  rcases mul_eq_zero.mp hproduct with hcase | hcase
  · linarith [hcase]
  · exact absurd hcase (mul_ne_zero hcoordOne hcoordTwo)

/-- **THE EXACT CORNER TRACE.**  Two atoms with one carrier pair and a
nonzero cross determinant read the corner trace as the sum of the two
shifted weights. -/
theorem shared_carrier_pair_trace
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {atomFirst atomSecond : Fin size} {slotOne slotTwo : Fin basisCount}
    (hslot : slotOne ≠ slotTwo)
    (hmemOne : basisLabel slotOne ∈ activeSet)
    (hmemTwo : basisLabel slotTwo ∈ activeSet)
    (hblockFirstOne : atomFirst ∈ activeSubset (basisLabel slotOne))
    (hblockFirstTwo : atomFirst ∈ activeSubset (basisLabel slotTwo))
    (hblockSecondOne : atomSecond ∈ activeSubset (basisLabel slotOne))
    (hblockSecondTwo : atomSecond ∈ activeSubset (basisLabel slotTwo))
    (hvanishFirst : ∀ slotIndex, slotIndex ≠ slotOne → slotIndex ≠ slotTwo →
      tightDir (basisLabel slotIndex) atomFirst = 0)
    (hvanishSecond : ∀ slotIndex, slotIndex ≠ slotOne → slotIndex ≠ slotTwo →
      tightDir (basisLabel slotIndex) atomSecond = 0)
    (hcross : tightDir (basisLabel slotOne) atomFirst
          * tightDir (basisLabel slotTwo) atomSecond
        - tightDir (basisLabel slotOne) atomSecond
          * tightDir (basisLabel slotTwo) atomFirst ≠ 0) :
    coeff slotOne slotOne + coeff slotTwo slotTwo
      = (value + weight atomFirst) + (value + weight atomSecond) := by
  have hfirstOne := carried_row_reading hdata basisLabel hrepresentation hmemOne
    hblockFirstOne
  have hfirstTwo := carried_row_reading hdata basisLabel hrepresentation hmemTwo
    hblockFirstTwo
  have hsecondOne := carried_row_reading hdata basisLabel hrepresentation hmemOne
    hblockSecondOne
  have hsecondTwo := carried_row_reading hdata basisLabel hrepresentation hmemTwo
    hblockSecondTwo
  rw [sum_collapse_two (termOf := fun slotIndex =>
    tightDir (basisLabel slotIndex) atomFirst * coeff slotIndex slotOne) hslot
    (fun slotIndex hOne hTwo => by
      rw [hvanishFirst slotIndex hOne hTwo, zero_mul])] at hfirstOne
  rw [sum_collapse_two (termOf := fun slotIndex =>
    tightDir (basisLabel slotIndex) atomFirst * coeff slotIndex slotTwo) hslot
    (fun slotIndex hOne hTwo => by
      rw [hvanishFirst slotIndex hOne hTwo, zero_mul])] at hfirstTwo
  rw [sum_collapse_two (termOf := fun slotIndex =>
    tightDir (basisLabel slotIndex) atomSecond * coeff slotIndex slotOne) hslot
    (fun slotIndex hOne hTwo => by
      rw [hvanishSecond slotIndex hOne hTwo, zero_mul])] at hsecondOne
  rw [sum_collapse_two (termOf := fun slotIndex =>
    tightDir (basisLabel slotIndex) atomSecond * coeff slotIndex slotTwo) hslot
    (fun slotIndex hOne hTwo => by
      rw [hvanishSecond slotIndex hOne hTwo, zero_mul])] at hsecondTwo
  refine mul_left_cancel₀ hcross ?_
  linear_combination tightDir (basisLabel slotTwo) atomSecond * hfirstOne
    - tightDir (basisLabel slotTwo) atomFirst * hsecondOne
    + tightDir (basisLabel slotOne) atomFirst * hsecondTwo
    - tightDir (basisLabel slotOne) atomSecond * hfirstTwo

/-- **THE EXACT CORNER DETERMINANT.**  The same pair reads the corner
determinant as the product of the two shifted weights. -/
theorem shared_carrier_pair_determinant
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {atomFirst atomSecond : Fin size} {slotOne slotTwo : Fin basisCount}
    (hslot : slotOne ≠ slotTwo)
    (hmemOne : basisLabel slotOne ∈ activeSet)
    (hmemTwo : basisLabel slotTwo ∈ activeSet)
    (hblockFirstOne : atomFirst ∈ activeSubset (basisLabel slotOne))
    (hblockFirstTwo : atomFirst ∈ activeSubset (basisLabel slotTwo))
    (hblockSecondOne : atomSecond ∈ activeSubset (basisLabel slotOne))
    (hblockSecondTwo : atomSecond ∈ activeSubset (basisLabel slotTwo))
    (hvanishFirst : ∀ slotIndex, slotIndex ≠ slotOne → slotIndex ≠ slotTwo →
      tightDir (basisLabel slotIndex) atomFirst = 0)
    (hvanishSecond : ∀ slotIndex, slotIndex ≠ slotOne → slotIndex ≠ slotTwo →
      tightDir (basisLabel slotIndex) atomSecond = 0)
    (hcross : tightDir (basisLabel slotOne) atomFirst
          * tightDir (basisLabel slotTwo) atomSecond
        - tightDir (basisLabel slotOne) atomSecond
          * tightDir (basisLabel slotTwo) atomFirst ≠ 0) :
    coeff slotOne slotOne * coeff slotTwo slotTwo
        - coeff slotOne slotTwo * coeff slotTwo slotOne
      = (value + weight atomFirst) * (value + weight atomSecond) := by
  have hfirstOne := carried_row_reading hdata basisLabel hrepresentation hmemOne
    hblockFirstOne
  have hfirstTwo := carried_row_reading hdata basisLabel hrepresentation hmemTwo
    hblockFirstTwo
  have hsecondOne := carried_row_reading hdata basisLabel hrepresentation hmemOne
    hblockSecondOne
  have hsecondTwo := carried_row_reading hdata basisLabel hrepresentation hmemTwo
    hblockSecondTwo
  rw [sum_collapse_two (termOf := fun slotIndex =>
    tightDir (basisLabel slotIndex) atomFirst * coeff slotIndex slotOne) hslot
    (fun slotIndex hOne hTwo => by
      rw [hvanishFirst slotIndex hOne hTwo, zero_mul])] at hfirstOne
  rw [sum_collapse_two (termOf := fun slotIndex =>
    tightDir (basisLabel slotIndex) atomFirst * coeff slotIndex slotTwo) hslot
    (fun slotIndex hOne hTwo => by
      rw [hvanishFirst slotIndex hOne hTwo, zero_mul])] at hfirstTwo
  rw [sum_collapse_two (termOf := fun slotIndex =>
    tightDir (basisLabel slotIndex) atomSecond * coeff slotIndex slotOne) hslot
    (fun slotIndex hOne hTwo => by
      rw [hvanishSecond slotIndex hOne hTwo, zero_mul])] at hsecondOne
  rw [sum_collapse_two (termOf := fun slotIndex =>
    tightDir (basisLabel slotIndex) atomSecond * coeff slotIndex slotTwo) hslot
    (fun slotIndex hOne hTwo => by
      rw [hvanishSecond slotIndex hOne hTwo, zero_mul])] at hsecondTwo
  set crossDet : ℝ := tightDir (basisLabel slotOne) atomFirst
      * tightDir (basisLabel slotTwo) atomSecond
    - tightDir (basisLabel slotOne) atomSecond
      * tightDir (basisLabel slotTwo) atomFirst with hcrossDet
  have hdiagOne : coeff slotOne slotOne * crossDet
      = (value + weight atomFirst) * tightDir (basisLabel slotOne) atomFirst
          * tightDir (basisLabel slotTwo) atomSecond
        - (value + weight atomSecond) * tightDir (basisLabel slotOne) atomSecond
          * tightDir (basisLabel slotTwo) atomFirst := by
    rw [hcrossDet]
    linear_combination tightDir (basisLabel slotTwo) atomSecond * hfirstOne
      - tightDir (basisLabel slotTwo) atomFirst * hsecondOne
  have hdiagTwo : coeff slotTwo slotTwo * crossDet
      = (value + weight atomSecond) * tightDir (basisLabel slotOne) atomFirst
          * tightDir (basisLabel slotTwo) atomSecond
        - (value + weight atomFirst) * tightDir (basisLabel slotOne) atomSecond
          * tightDir (basisLabel slotTwo) atomFirst := by
    rw [hcrossDet]
    linear_combination tightDir (basisLabel slotOne) atomFirst * hsecondTwo
      - tightDir (basisLabel slotOne) atomSecond * hfirstTwo
  have hoffOne : coeff slotOne slotTwo * crossDet
      = ((value + weight atomFirst) - (value + weight atomSecond))
        * tightDir (basisLabel slotTwo) atomFirst
        * tightDir (basisLabel slotTwo) atomSecond := by
    rw [hcrossDet]
    linear_combination tightDir (basisLabel slotTwo) atomSecond * hfirstTwo
      - tightDir (basisLabel slotTwo) atomFirst * hsecondTwo
  have hoffTwo : coeff slotTwo slotOne * crossDet
      = ((value + weight atomSecond) - (value + weight atomFirst))
        * tightDir (basisLabel slotOne) atomFirst
        * tightDir (basisLabel slotOne) atomSecond := by
    rw [hcrossDet]
    linear_combination tightDir (basisLabel slotOne) atomFirst * hsecondOne
      - tightDir (basisLabel slotOne) atomSecond * hfirstOne
  have hsquare : crossDet * crossDet ≠ 0 := mul_ne_zero hcross hcross
  refine mul_right_cancel₀ hsquare ?_
  linear_combination (coeff slotTwo slotTwo * crossDet) * hdiagOne
    + ((value + weight atomFirst) * tightDir (basisLabel slotOne) atomFirst
        * tightDir (basisLabel slotTwo) atomSecond
      - (value + weight atomSecond) * tightDir (basisLabel slotOne) atomSecond
        * tightDir (basisLabel slotTwo) atomFirst) * hdiagTwo
    - (coeff slotTwo slotOne * crossDet) * hoffOne
    - (((value + weight atomFirst) - (value + weight atomSecond))
        * tightDir (basisLabel slotTwo) atomFirst
        * tightDir (basisLabel slotTwo) atomSecond) * hoffTwo

/-- A three-term sum collapses to its three surviving terms. -/
theorem sum_collapse_three {termOf : Fin basisCount → ℝ}
    {slotOne slotTwo slotThree : Fin basisCount} (hOneTwo : slotOne ≠ slotTwo)
    (hOneThree : slotOne ≠ slotThree) (hTwoThree : slotTwo ≠ slotThree)
    (hvanish : ∀ slotIndex, slotIndex ≠ slotOne → slotIndex ≠ slotTwo →
      slotIndex ≠ slotThree → termOf slotIndex = 0) :
    ∑ slotIndex, termOf slotIndex
      = termOf slotOne + termOf slotTwo + termOf slotThree := by
  classical
  have hnotOne : slotOne ∉ ({slotTwo, slotThree} : Finset (Fin basisCount)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hrest
    · exact hOneTwo heq
    · exact hOneThree (Finset.mem_singleton.mp hrest)
  have hnotTwo : slotTwo ∉ ({slotThree} : Finset (Fin basisCount)) := fun hmem =>
    hTwoThree (Finset.mem_singleton.mp hmem)
  have hrestrict : ∑ slotIndex, termOf slotIndex
      = ∑ slotIndex ∈ ({slotOne, slotTwo, slotThree} : Finset (Fin basisCount)),
          termOf slotIndex := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro slotIndex _ hnot
    obtain ⟨hOne, hTwo, hThree⟩ := notMem_triple.mp hnot
    exact hvanish slotIndex hOne hTwo hThree
  rw [hrestrict, Finset.sum_insert hnotOne, Finset.sum_insert hnotTwo,
    Finset.sum_singleton, add_assoc]

/-- A three-atom homogeneous system with a nonzero third coordinate has a
singular matrix. -/
theorem three_by_three_determinant_zero_of_kernel
    {entryOneOne entryOneTwo entryOneThree entryTwoOne entryTwoTwo entryTwoThree
      entryThreeOne entryThreeTwo entryThreeThree coordOne coordTwo coordThree : ℝ}
    (hrowOne : entryOneOne * coordOne + entryOneTwo * coordTwo
      + entryOneThree * coordThree = 0)
    (hrowTwo : entryTwoOne * coordOne + entryTwoTwo * coordTwo
      + entryTwoThree * coordThree = 0)
    (hrowThree : entryThreeOne * coordOne + entryThreeTwo * coordTwo
      + entryThreeThree * coordThree = 0)
    (hcoord : coordThree ≠ 0) :
    entryOneOne * (entryTwoTwo * entryThreeThree - entryTwoThree * entryThreeTwo)
        - entryOneTwo
          * (entryTwoOne * entryThreeThree - entryTwoThree * entryThreeOne)
        + entryOneThree
          * (entryTwoOne * entryThreeTwo - entryTwoTwo * entryThreeOne) = 0 := by
  have hproduct : (entryOneOne
        * (entryTwoTwo * entryThreeThree - entryTwoThree * entryThreeTwo)
      - entryOneTwo
        * (entryTwoOne * entryThreeThree - entryTwoThree * entryThreeOne)
      + entryOneThree
        * (entryTwoOne * entryThreeTwo - entryTwoTwo * entryThreeOne))
      * coordThree = 0 := by
    linear_combination
      (entryTwoOne * entryThreeTwo - entryTwoTwo * entryThreeOne) * hrowOne
      - (entryOneOne * entryThreeTwo - entryOneTwo * entryThreeOne) * hrowTwo
      + (entryOneOne * entryTwoTwo - entryOneTwo * entryTwoOne) * hrowThree
  rcases mul_eq_zero.mp hproduct with hcase | hcase
  · exact hcase
  · exact absurd hcase hcoord

/-- A multiplicity-three atom names its three carriers. -/
theorem exists_carrier_triple_of_multiplicity_three
    (basisLabel : Fin basisCount → activeIndex) {atomIndex : Fin size}
    (hmult : basisSupportMultiplicity tightDir basisLabel atomIndex = 3) :
    ∃ slotOne slotTwo slotThree : Fin basisCount, slotOne ≠ slotTwo
      ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
      ∧ tightDir (basisLabel slotOne) atomIndex ≠ 0
      ∧ tightDir (basisLabel slotTwo) atomIndex ≠ 0
      ∧ tightDir (basisLabel slotThree) atomIndex ≠ 0
      ∧ ∀ slotIndex, slotIndex ≠ slotOne → slotIndex ≠ slotTwo →
          slotIndex ≠ slotThree → tightDir (basisLabel slotIndex) atomIndex = 0 := by
  classical
  rw [basisSupportMultiplicity] at hmult
  obtain ⟨slotOne, slotTwo, slotThree, hOneTwo, hOneThree, hTwoThree, hfilter⟩ :=
    Finset.card_eq_three.mp hmult
  have hmemOf : ∀ slotIndex ∈ ({slotOne, slotTwo, slotThree}
      : Finset (Fin basisCount)),
      tightDir (basisLabel slotIndex) atomIndex ≠ 0 := by
    intro slotIndex hmem
    rw [← hfilter] at hmem
    exact mem_datumTightSupport.mp (Finset.mem_filter.mp hmem).2
  refine ⟨slotOne, slotTwo, slotThree, hOneTwo, hOneThree, hTwoThree,
    hmemOf slotOne (Finset.mem_insert_self _ _),
    hmemOf slotTwo (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
    hmemOf slotThree (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))), ?_⟩
  intro slotIndex hOne hTwo hThree
  by_contra hne
  have hmemFilter : slotIndex ∈ Finset.univ.filter fun columnIndex =>
      atomIndex ∈ datumTightSupport tightDir (basisLabel columnIndex) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_datumTightSupport.mpr hne⟩
  rw [hfilter] at hmemFilter
  obtain ⟨hcaseOne, hcaseTwo, hcaseThree⟩ := notMem_triple.mp
    (fun hmem => by
      rcases Finset.mem_insert.mp hmem with heq | hrest
      · exact hOne heq
      rcases Finset.mem_insert.mp hrest with heq | hlast
      · exact hTwo heq
      · exact hThree (Finset.mem_singleton.mp hlast))
  exact hcaseOne (by
    rcases Finset.mem_insert.mp hmemFilter with heq | hrest
    · exact heq
    rcases Finset.mem_insert.mp hrest with heq | hlast
    · exact absurd heq hTwo
    · exact absurd (Finset.mem_singleton.mp hlast) hThree)

/-- **THE TRIPLE CARRIER CORNER.**  At an atom with exactly three
carriers the shifted weight is an eigenvalue of the three-by-three corner
of the coefficient matrix. -/
theorem carrier_triple_characteristic
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {atomIndex : Fin size} {slotOne slotTwo slotThree : Fin basisCount}
    (hOneTwo : slotOne ≠ slotTwo) (hOneThree : slotOne ≠ slotThree)
    (hTwoThree : slotTwo ≠ slotThree)
    (hmemOne : basisLabel slotOne ∈ activeSet)
    (hmemTwo : basisLabel slotTwo ∈ activeSet)
    (hmemThree : basisLabel slotThree ∈ activeSet)
    (hblockOne : atomIndex ∈ activeSubset (basisLabel slotOne))
    (hblockTwo : atomIndex ∈ activeSubset (basisLabel slotTwo))
    (hblockThree : atomIndex ∈ activeSubset (basisLabel slotThree))
    (hcoordThree : tightDir (basisLabel slotThree) atomIndex ≠ 0)
    (hvanish : ∀ slotIndex, slotIndex ≠ slotOne → slotIndex ≠ slotTwo →
      slotIndex ≠ slotThree → tightDir (basisLabel slotIndex) atomIndex = 0) :
    (coeff slotOne slotOne - (value + weight atomIndex))
        * ((coeff slotTwo slotTwo - (value + weight atomIndex))
            * (coeff slotThree slotThree - (value + weight atomIndex))
          - coeff slotTwo slotThree * coeff slotThree slotTwo)
      - coeff slotOne slotTwo
        * (coeff slotTwo slotOne
            * (coeff slotThree slotThree - (value + weight atomIndex))
          - coeff slotTwo slotThree * coeff slotThree slotOne)
      + coeff slotOne slotThree
        * (coeff slotTwo slotOne * coeff slotThree slotTwo
          - (coeff slotTwo slotTwo - (value + weight atomIndex))
            * coeff slotThree slotOne) = 0 := by
  have hreadOne := carried_row_reading hdata basisLabel hrepresentation hmemOne
    hblockOne
  have hreadTwo := carried_row_reading hdata basisLabel hrepresentation hmemTwo
    hblockTwo
  have hreadThree := carried_row_reading hdata basisLabel hrepresentation
    hmemThree hblockThree
  rw [sum_collapse_three (termOf := fun slotIndex =>
    tightDir (basisLabel slotIndex) atomIndex * coeff slotIndex slotOne)
    hOneTwo hOneThree hTwoThree (fun slotIndex hOne hTwo hThree => by
      rw [hvanish slotIndex hOne hTwo hThree, zero_mul])] at hreadOne
  rw [sum_collapse_three (termOf := fun slotIndex =>
    tightDir (basisLabel slotIndex) atomIndex * coeff slotIndex slotTwo)
    hOneTwo hOneThree hTwoThree (fun slotIndex hOne hTwo hThree => by
      rw [hvanish slotIndex hOne hTwo hThree, zero_mul])] at hreadTwo
  rw [sum_collapse_three (termOf := fun slotIndex =>
    tightDir (basisLabel slotIndex) atomIndex * coeff slotIndex slotThree)
    hOneTwo hOneThree hTwoThree (fun slotIndex hOne hTwo hThree => by
      rw [hvanish slotIndex hOne hTwo hThree, zero_mul])] at hreadThree
  have hkernel := three_by_three_determinant_zero_of_kernel
    (entryOneOne := coeff slotOne slotOne - (value + weight atomIndex))
    (entryOneTwo := coeff slotTwo slotOne)
    (entryOneThree := coeff slotThree slotOne)
    (entryTwoOne := coeff slotOne slotTwo)
    (entryTwoTwo := coeff slotTwo slotTwo - (value + weight atomIndex))
    (entryTwoThree := coeff slotThree slotTwo)
    (entryThreeOne := coeff slotOne slotThree)
    (entryThreeTwo := coeff slotTwo slotThree)
    (entryThreeThree := coeff slotThree slotThree - (value + weight atomIndex))
    (coordOne := tightDir (basisLabel slotOne) atomIndex)
    (coordTwo := tightDir (basisLabel slotTwo) atomIndex)
    (coordThree := tightDir (basisLabel slotThree) atomIndex)
    (by linear_combination hreadOne) (by linear_combination hreadTwo)
    (by linear_combination hreadThree) hcoordThree
  linear_combination hkernel

/-! ## Layer 7 — the shifted weight arithmetic -/

/-- The shifted weights sum to the size multiple of the value plus one. -/
theorem shifted_weight_sum
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    ∑ atomIndex : Fin size, (value + weight atomIndex) = size * value + 1 := by
  rw [Finset.sum_add_distrib, hdata.weight_sum_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Each shifted weight is less than one at a negative value. -/
theorem shifted_weight_lt_one
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hvalueNeg : value < 0) (atomIndex : Fin size) :
    value + weight atomIndex < 1 := by
  have hsum := hdata.weight_sum_one
  have hsingle := Finset.single_le_sum (f := weight)
    (fun otherAtom _ => (hdata.weight_pos otherAtom).le) (Finset.mem_univ atomIndex)
  rw [hsum] at hsingle
  linarith

/-! ## Layer 8 — the frame forms -/

/-- The gap floor in the form the shared-block kills consume. -/
theorem SixThreeCrux.gap_diagonal_ne_value (crux : SixThreeCrux)
    (atomIndex : Fin 6) :
    chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomIndex atomIndex
      ≠ chartObjective (chartPointOfDesign crux.design) := by
  have hpos := crux.gap_diagonal_pos_of_allHeavy atomIndex
  have hneg := crux.hasNegativeChartValue
  intro hcontra
  rw [hcontra] at hpos
  linarith

/-- The rank-five form of the shared-block axis kill. -/
theorem RankFiveFrame.false_of_shared_support_cross_zero {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {slotOne slotTwo : Fin 5}
    (hslot : slotOne ≠ slotTwo) {atomA atomB atomC : Fin 6}
    (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC) (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport frame.tightDir (frame.basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport frame.tightDir (frame.basisLabel slotTwo)
      = {atomA, atomB, atomC})
    (hcross : frame.tightDir (frame.basisLabel slotOne) atomA
          * frame.tightDir (frame.basisLabel slotTwo) atomB
        - frame.tightDir (frame.basisLabel slotOne) atomB
          * frame.tightDir (frame.basisLabel slotTwo) atomA = 0) :
    False :=
  false_of_shared_block_cross_zero frame.hdata frame.basisLabel frame.leftInv
    frame.hleft hslot (frame.hmemAll slotOne) (frame.hmemAll slotTwo) hAB hAC hBC
    hsupportOne hsupportTwo (crux.gap_diagonal_ne_value atomC) hcross

/-- The rank-five block cap. -/
theorem RankFiveFrame.false_of_three_shared_supports {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {slotOne slotTwo slotThree : Fin 5}
    (hOneTwo : slotOne ≠ slotTwo) (hThreeOne : slotThree ≠ slotOne)
    (hThreeTwo : slotThree ≠ slotTwo) {atomA atomB atomC : Fin 6}
    (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC) (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport frame.tightDir (frame.basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport frame.tightDir (frame.basisLabel slotTwo)
      = {atomA, atomB, atomC})
    (hsupportThree : datumTightSupport frame.tightDir (frame.basisLabel slotThree)
      = {atomA, atomB, atomC}) :
    False :=
  false_of_three_shared_block_slots frame.hdata frame.basisLabel frame.leftInv
    frame.hleft hOneTwo hThreeOne hThreeTwo (frame.hmemAll slotOne)
    (frame.hmemAll slotTwo) (frame.hmemAll slotThree) hAB hAC hBC hsupportOne
    hsupportTwo hsupportThree (crux.gap_diagonal_ne_value atomC)

/-- The rank-six form of the shared-block axis kill. -/
theorem RankSixFrame.false_of_shared_support_cross_zero {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {slotOne slotTwo : Fin 6}
    (hslot : slotOne ≠ slotTwo) {atomA atomB atomC : Fin 6}
    (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC) (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport frame.tightDir (frame.basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport frame.tightDir (frame.basisLabel slotTwo)
      = {atomA, atomB, atomC})
    (hcross : frame.tightDir (frame.basisLabel slotOne) atomA
          * frame.tightDir (frame.basisLabel slotTwo) atomB
        - frame.tightDir (frame.basisLabel slotOne) atomB
          * frame.tightDir (frame.basisLabel slotTwo) atomA = 0) :
    False :=
  false_of_shared_block_cross_zero frame.hdata frame.basisLabel frame.leftInv
    frame.hleft hslot (frame.hmemAll slotOne) (frame.hmemAll slotTwo) hAB hAC hBC
    hsupportOne hsupportTwo (crux.gap_diagonal_ne_value atomC) hcross

/-- The rank-six block cap. -/
theorem RankSixFrame.false_of_three_shared_supports {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {slotOne slotTwo slotThree : Fin 6}
    (hOneTwo : slotOne ≠ slotTwo) (hThreeOne : slotThree ≠ slotOne)
    (hThreeTwo : slotThree ≠ slotTwo) {atomA atomB atomC : Fin 6}
    (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC) (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport frame.tightDir (frame.basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport frame.tightDir (frame.basisLabel slotTwo)
      = {atomA, atomB, atomC})
    (hsupportThree : datumTightSupport frame.tightDir (frame.basisLabel slotThree)
      = {atomA, atomB, atomC}) :
    False :=
  false_of_three_shared_block_slots frame.hdata frame.basisLabel frame.leftInv
    frame.hleft hOneTwo hThreeOne hThreeTwo (frame.hmemAll slotOne)
    (frame.hmemAll slotTwo) (frame.hmemAll slotThree) hAB hAC hBC hsupportOne
    hsupportTwo hsupportThree (crux.gap_diagonal_ne_value atomC)

/-- **THE RANK-FIVE DOUBLE ATOM.**  Every multiplicity-two atom names its
carrier pair and the characteristic equation of the corner. -/
theorem RankFiveFrame.exists_carrier_pair_characteristic {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {atomIndex : Fin 6}
    (hmult : basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex
      = 2) :
    ∃ slotOne slotTwo : Fin 5, slotOne ≠ slotTwo
      ∧ frame.tightDir (frame.basisLabel slotOne) atomIndex ≠ 0
      ∧ frame.tightDir (frame.basisLabel slotTwo) atomIndex ≠ 0
      ∧ (∀ slotIndex, slotIndex ≠ slotOne → slotIndex ≠ slotTwo →
          frame.tightDir (frame.basisLabel slotIndex) atomIndex = 0)
      ∧ (frame.coeff slotOne slotOne
            - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomIndex))
          * (frame.coeff slotTwo slotTwo
            - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomIndex))
        = frame.coeff slotOne slotTwo * frame.coeff slotTwo slotOne := by
  obtain ⟨slotOne, slotTwo, hslot, hcoordOne, hcoordTwo, hvanish⟩ :=
    exists_carrier_pair_of_multiplicity_two (tightDir := frame.tightDir)
      frame.basisLabel hmult
  refine ⟨slotOne, slotTwo, hslot, hcoordOne, hcoordTwo, hvanish, ?_⟩
  refine carrier_pair_characteristic frame.hdata frame.basisLabel
    frame.hrepresentation hslot (frame.hmemAll slotOne) (frame.hmemAll slotTwo)
    ?_ ?_ hcoordOne hcoordTwo hvanish
  · exact datumTightSupport_subset frame.hdata (frame.hmemAll slotOne)
      (mem_datumTightSupport.mpr hcoordOne)
  · exact datumTightSupport_subset frame.hdata (frame.hmemAll slotTwo)
      (mem_datumTightSupport.mpr hcoordTwo)

/-- **THE RANK-SIX DOUBLE ATOM.**  The same corner equation at the sixth
rank. -/
theorem RankSixFrame.exists_carrier_pair_characteristic {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {atomIndex : Fin 6}
    (hmult : basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex
      = 2) :
    ∃ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo
      ∧ frame.tightDir (frame.basisLabel slotOne) atomIndex ≠ 0
      ∧ frame.tightDir (frame.basisLabel slotTwo) atomIndex ≠ 0
      ∧ (∀ slotIndex, slotIndex ≠ slotOne → slotIndex ≠ slotTwo →
          frame.tightDir (frame.basisLabel slotIndex) atomIndex = 0)
      ∧ (frame.coeff slotOne slotOne
            - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomIndex))
          * (frame.coeff slotTwo slotTwo
            - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomIndex))
        = frame.coeff slotOne slotTwo * frame.coeff slotTwo slotOne := by
  obtain ⟨slotOne, slotTwo, hslot, hcoordOne, hcoordTwo, hvanish⟩ :=
    exists_carrier_pair_of_multiplicity_two (tightDir := frame.tightDir)
      frame.basisLabel hmult
  refine ⟨slotOne, slotTwo, hslot, hcoordOne, hcoordTwo, hvanish, ?_⟩
  refine carrier_pair_characteristic frame.hdata frame.basisLabel
    frame.hrepresentation hslot (frame.hmemAll slotOne) (frame.hmemAll slotTwo)
    ?_ ?_ hcoordOne hcoordTwo hvanish
  · exact datumTightSupport_subset frame.hdata (frame.hmemAll slotOne)
      (mem_datumTightSupport.mpr hcoordOne)
  · exact datumTightSupport_subset frame.hdata (frame.hmemAll slotTwo)
      (mem_datumTightSupport.mpr hcoordTwo)

/-- The rank-five shifted weight sum. -/
theorem RankFiveFrame.shifted_weight_sum {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) :
    ∑ atomIndex : Fin 6, (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
      = 6 * chartObjective (chartPointOfDesign crux.design) + 1 := by
  have hsum := _root_.Gtz.shifted_weight_sum frame.hdata
  rw [hsum]
  norm_num

/-- The rank-six shifted weight sum. -/
theorem RankSixFrame.shifted_weight_sum {crux : SixThreeCrux}
    (frame : RankSixFrame crux) :
    ∑ atomIndex : Fin 6, (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
      = 6 * chartObjective (chartPointOfDesign crux.design) + 1 := by
  have hsum := _root_.Gtz.shifted_weight_sum frame.hdata
  rw [hsum]
  norm_num

end Gtz

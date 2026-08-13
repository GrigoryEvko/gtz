import Gtz.Wave.RankFiveRungAssembly
import Gtz.Wave.SharedPairOuterReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The rank-five closure supply — the shared-block cap and the pair reduction

Two payloads narrow the rank-five closures.  The first payload is THE
SHARED-BLOCK CAP, a structural law at every rank: independent tight
directions that fill the coordinate space of one block price the gap
diagonal of that block at the chart value, and the all-heavy floor
refuses a negative diagonal.  Thus no block carries three basis slots —
at rank four, at rank five, and at rank six.  The cap was a named open
obligation of the campaign memory.

The second payload ports the closure-one reduction to rank five.  The
private-pair kill, the same-pair kill, and the two bridges consume only
rank-generic supply, thus the rank-five closure one narrows to the SAME
residual as the rank-four one: the outer sharer, where some other basis
label carries a nonzero atom outside the pair.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.mulVec_combination` — the matrix action distributes on a
  coefficient combination, at every rectangular shape.
* `Gtz.exists_combination_eq_single_of_supports` — a full independent
  family on an atom set combines to every coordinate single.
* `Gtz.false_of_spanning_tight_directions` — **THE SHARED-BLOCK CAP.**
* `Gtz.RankFiveFrame.false_of_three_slots_share_block` and
  `Gtz.RankFourFrame.false_of_three_slots_share_block` — the frame
  corollaries: no block carries three basis slots.
* `Gtz.RankFiveFrame.false_of_supportTwo_private_pair` — **THE
  PRIVATE-PAIR KILL** at rank five.
* `Gtz.rankFiveSupportTwoClosed_of_shared_pair_kill` — the first bridge.
* `Gtz.RankFiveFrame.false_of_samePair_columns` — **THE SAME-PAIR
  KILL** at rank five.
* `Gtz.rankFiveSupportTwoClosed_of_outer_shared_kill` — **THE REFINED
  BRIDGE.**  Closure one at rank five is the outer sharer only.

## Vacuity

The frame statements are vacuous if `Gtz.GtzWeighted 6 3` holds.  The
combination laws are unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## The combination calculus -/

/-- The matrix action distributes on a coefficient combination. -/
theorem mulVec_combination {rowCount colCount coeffCount : ℕ}
    (form : Matrix (Fin rowCount) (Fin colCount) ℝ)
    (coeffVec : Fin coeffCount → ℝ) (family : Fin coeffCount → Fin colCount → ℝ) :
    form *ᵥ (∑ coeffIndex, coeffVec coeffIndex • family coeffIndex)
      = ∑ coeffIndex, coeffVec coeffIndex • (form *ᵥ family coeffIndex) := by
  rw [← Matrix.mulVecLin_apply, map_sum]
  refine Finset.sum_congr rfl fun coeffIndex _ => ?_
  rw [LinearMap.map_smul, Matrix.mulVecLin_apply]

/-- **THE COORDINATE COMBINATION.**  An independent family whose supports
sit inside an atom set of matching cardinality combines to every
coordinate single of that set: the restricted family is a basis of the
coordinate space. -/
theorem exists_combination_eq_single_of_supports {size directionCount : ℕ}
    (family : Fin directionCount → Fin size → ℝ)
    (hindep : LinearIndependent ℝ family)
    (atoms : Finset (Fin size)) (hcard : atoms.card = directionCount)
    (hpos : 0 < directionCount)
    (hsub : ∀ directionIndex atomIndex, family directionIndex atomIndex ≠ 0 →
      atomIndex ∈ atoms)
    {targetAtom : Fin size} (htarget : targetAtom ∈ atoms) :
    ∃ coeffVec : Fin directionCount → ℝ,
      ∑ directionIndex, coeffVec directionIndex • family directionIndex
        = Pi.single targetAtom 1 := by
  classical
  have hnonempty : Nonempty (Fin directionCount) := ⟨⟨0, hpos⟩⟩
  -- the restricted family on the atom subtype
  have hrestrictedIndep : LinearIndependent ℝ
      (fun (directionIndex : Fin directionCount)
          (atomIndex : {atomIndex // atomIndex ∈ atoms}) =>
        family directionIndex atomIndex.1) := by
    rw [Fintype.linearIndependent_iff] at hindep ⊢
    intro coeffVec hsum
    refine hindep coeffVec ?_
    funext atomIndex
    rw [Finset.sum_apply, Pi.zero_apply]
    by_cases hmemAtom : atomIndex ∈ atoms
    · have hpoint := congrFun hsum ⟨atomIndex, hmemAtom⟩
      rw [Finset.sum_apply, Pi.zero_apply] at hpoint
      simpa using hpoint
    · refine Finset.sum_eq_zero fun directionIndex _ => ?_
      have hzero : family directionIndex atomIndex = 0 := by
        by_contra hnonzero
        exact hmemAtom (hsub directionIndex atomIndex hnonzero)
      rw [Pi.smul_apply, hzero, smul_zero]
  have hcardEq : Fintype.card (Fin directionCount)
      = Module.finrank ℝ ({atomIndex // atomIndex ∈ atoms} → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_fin,
      hcard]
  let spanningBasis := basisOfLinearIndependentOfCardEqFinrank
    hrestrictedIndep hcardEq
  have hcoe : ⇑spanningBasis = fun (directionIndex : Fin directionCount)
      (atomIndex : {atomIndex // atomIndex ∈ atoms}) =>
        family directionIndex atomIndex.1 :=
    coe_basisOfLinearIndependentOfCardEqFinrank hrestrictedIndep hcardEq
  refine ⟨fun directionIndex => spanningBasis.repr
    (Pi.single ⟨targetAtom, htarget⟩ 1) directionIndex, ?_⟩
  have hsum := spanningBasis.sum_repr (Pi.single ⟨targetAtom, htarget⟩ 1)
  simp only [hcoe] at hsum
  funext atomIndex
  by_cases hmemAtom : atomIndex ∈ atoms
  · have hpoint := congrFun hsum ⟨atomIndex, hmemAtom⟩
    rw [Finset.sum_apply] at hpoint
    rw [Finset.sum_apply]
    by_cases heq : atomIndex = targetAtom
    · subst heq
      rw [Pi.single_eq_same] at hpoint
      rw [Pi.single_eq_same]
      exact hpoint
    · have hneSub : (⟨atomIndex, hmemAtom⟩ : {x // x ∈ atoms})
          ≠ ⟨targetAtom, htarget⟩ :=
        fun hcontra => heq (congrArg Subtype.val hcontra)
      rw [Pi.single_eq_of_ne hneSub] at hpoint
      rw [Pi.single_eq_of_ne heq]
      exact hpoint
  · rw [Finset.sum_apply]
    have hneTarget : atomIndex ≠ targetAtom := by
      intro hcontra
      rw [hcontra] at hmemAtom
      exact hmemAtom htarget
    rw [Pi.single_eq_of_ne hneTarget]
    refine Finset.sum_eq_zero fun directionIndex _ => ?_
    have hzero : family directionIndex atomIndex = 0 := by
      by_contra hnonzero
      exact hmemAtom (hsub directionIndex atomIndex hnonzero)
    rw [Pi.smul_apply, hzero, smul_zero]

/-! ## The shared-block cap -/

/-- **THE SHARED-BLOCK CAP.**  Independent tight directions that fill an
atom set price the gap diagonal there at the chart value: the tight rows
act on the coordinate single as the value times the single.  A positive
gap floor with a negative value is a contradiction.  The cap is generic
in the rank and in the number of directions. -/
theorem false_of_spanning_tight_directions
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {directionCount : ℕ} (hpos : 0 < directionCount)
    (labels : Fin directionCount → activeIndex)
    (hmem : ∀ directionIndex, labels directionIndex ∈ activeSet)
    (hindep : LinearIndependent ℝ
      (fun directionIndex => tightDir (labels directionIndex)))
    {atoms : Finset (Fin size)} (hcard : atoms.card = directionCount)
    (hsub : ∀ directionIndex atomIndex,
      tightDir (labels directionIndex) atomIndex ≠ 0 → atomIndex ∈ atoms)
    (hblock : ∀ directionIndex, atoms ⊆ activeSubset (labels directionIndex))
    {floorAtom : Fin size} (hfloorMem : floorAtom ∈ atoms)
    (hfloor : 0 < chartStationaryGap projection weight floorAtom floorAtom)
    (hvalueNeg : value < 0) : False := by
  classical
  obtain ⟨coeffVec, hcombination⟩ := exists_combination_eq_single_of_supports
    (fun directionIndex => tightDir (labels directionIndex)) hindep atoms hcard
    hpos hsub hfloorMem
  have hrows : ∀ directionIndex,
      (chartStationaryGap projection weight
          *ᵥ tightDir (labels directionIndex)) floorAtom
        = value * tightDir (labels directionIndex) floorAtom :=
    fun directionIndex => hdata.tightDir_isTight _ (hmem directionIndex)
      floorAtom (hblock directionIndex hfloorMem)
  have happly : (chartStationaryGap projection weight *ᵥ (∑ directionIndex,
        coeffVec directionIndex • tightDir (labels directionIndex))) floorAtom
      = (chartStationaryGap projection weight
          *ᵥ (Pi.single floorAtom 1 : Fin size → ℝ)) floorAtom := by
    rw [hcombination]
  rw [mulVec_combination, Finset.sum_apply] at happly
  have hleft : ∑ directionIndex, (coeffVec directionIndex
        • (chartStationaryGap projection weight
          *ᵥ tightDir (labels directionIndex))) floorAtom
      = value := by
    have hcollapse : ∑ directionIndex, (coeffVec directionIndex
          • (chartStationaryGap projection weight
            *ᵥ tightDir (labels directionIndex))) floorAtom
        = value * ∑ directionIndex, (coeffVec directionIndex
            • tightDir (labels directionIndex)) floorAtom := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun directionIndex _ => ?_
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        hrows directionIndex]
      ring
    have hpoint := congrFun hcombination floorAtom
    rw [Finset.sum_apply] at hpoint
    rw [hcollapse, hpoint, Pi.single_eq_same, mul_one]
  rw [hleft] at happly
  have hsingleRead : (chartStationaryGap projection weight
      *ᵥ (Pi.single floorAtom 1 : Fin size → ℝ)) floorAtom
      = chartStationaryGap projection weight floorAtom floorAtom := by
    rw [Matrix.mulVec_single]
    exact mul_one _
  rw [hsingleRead] at happly
  rw [← happly] at hfloor
  linarith

/-- **THE RANK-FIVE BLOCK CAP.**  No block of a rank-five frame carries
three basis slots: three independent directions would fill the block's
coordinate space and price the gap diagonal at the negative value. -/
theorem RankFiveFrame.false_of_three_slots_share_block {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {slotOne slotTwo slotThree : Fin 5}
    (h12 : slotOne ≠ slotTwo) (h13 : slotOne ≠ slotThree)
    (h23 : slotTwo ≠ slotThree)
    (hblockTwo : frame.activeSubset (frame.basisLabel slotTwo)
      = frame.activeSubset (frame.basisLabel slotOne))
    (hblockThree : frame.activeSubset (frame.basisLabel slotThree)
      = frame.activeSubset (frame.basisLabel slotOne)) : False := by
  classical
  have hcard : (frame.activeSubset (frame.basisLabel slotOne)).card = 3 :=
    frame.hdata.activeSubset_card _ (frame.hmemAll slotOne)
  have hinjTriple : Function.Injective ![slotOne, slotTwo, slotThree] := by
    intro firstIndex secondIndex hcollide
    fin_cases firstIndex <;> fin_cases secondIndex
    · rfl
    · exact absurd hcollide h12
    · exact absurd hcollide h13
    · exact absurd hcollide.symm h12
    · rfl
    · exact absurd hcollide h23
    · exact absurd hcollide.symm h13
    · exact absurd hcollide.symm h23
    · rfl
  have hblockAll : ∀ tripleIndex : Fin 3,
      frame.activeSubset (frame.basisLabel (![slotOne, slotTwo, slotThree]
        tripleIndex)) = frame.activeSubset (frame.basisLabel slotOne) := by
    intro tripleIndex
    fin_cases tripleIndex
    · rfl
    · exact hblockTwo
    · exact hblockThree
  obtain ⟨floorAtom, hfloorMem⟩ : ∃ floorAtom,
      floorAtom ∈ frame.activeSubset (frame.basisLabel slotOne) :=
    Finset.card_pos.mp (by omega)
  refine false_of_spanning_tight_directions frame.hdata (by norm_num)
    (fun tripleIndex => frame.basisLabel (![slotOne, slotTwo, slotThree]
      tripleIndex))
    (fun tripleIndex => frame.hmemAll _)
    (frame.hindep.comp ![slotOne, slotTwo, slotThree] hinjTriple)
    hcard ?_ ?_ hfloorMem
    (crux.gap_diagonal_pos_of_allHeavy floorAtom) frame.hvalueNeg
  · intro tripleIndex atomIndex hnonzero
    have hmemBlock : atomIndex ∈ frame.activeSubset (frame.basisLabel
        (![slotOne, slotTwo, slotThree] tripleIndex)) := by
      by_contra hout
      exact hnonzero (frame.hdata.tightDir_support _ (frame.hmemAll _)
        atomIndex hout)
    rwa [hblockAll tripleIndex] at hmemBlock
  · intro tripleIndex
    rw [hblockAll tripleIndex]

/-- **THE RANK-FOUR BLOCK CAP.**  No block of a rank-four frame carries
three basis slots.  The same cap, at the first rung. -/
theorem RankFourFrame.false_of_three_slots_share_block {crux : SixThreeCrux}
    (frame : RankFourFrame crux) {slotOne slotTwo slotThree : Fin 4}
    (h12 : slotOne ≠ slotTwo) (h13 : slotOne ≠ slotThree)
    (h23 : slotTwo ≠ slotThree)
    (hblockTwo : frame.activeSubset (frame.basisLabel slotTwo)
      = frame.activeSubset (frame.basisLabel slotOne))
    (hblockThree : frame.activeSubset (frame.basisLabel slotThree)
      = frame.activeSubset (frame.basisLabel slotOne)) : False := by
  classical
  have hcard : (frame.activeSubset (frame.basisLabel slotOne)).card = 3 :=
    frame.hdata.activeSubset_card _ (frame.hmemAll slotOne)
  have hindepAll : LinearIndependent ℝ
      (fun columnIndex => frame.tightDir (frame.basisLabel columnIndex)) :=
    linearIndependent_tightDir_of_leftInverse frame.basisLabel frame.leftInv
      frame.hleft
  have hinjTriple : Function.Injective ![slotOne, slotTwo, slotThree] := by
    intro firstIndex secondIndex hcollide
    fin_cases firstIndex <;> fin_cases secondIndex
    · rfl
    · exact absurd hcollide h12
    · exact absurd hcollide h13
    · exact absurd hcollide.symm h12
    · rfl
    · exact absurd hcollide h23
    · exact absurd hcollide.symm h13
    · exact absurd hcollide.symm h23
    · rfl
  have hblockAll : ∀ tripleIndex : Fin 3,
      frame.activeSubset (frame.basisLabel (![slotOne, slotTwo, slotThree]
        tripleIndex)) = frame.activeSubset (frame.basisLabel slotOne) := by
    intro tripleIndex
    fin_cases tripleIndex
    · rfl
    · exact hblockTwo
    · exact hblockThree
  obtain ⟨floorAtom, hfloorMem⟩ : ∃ floorAtom,
      floorAtom ∈ frame.activeSubset (frame.basisLabel slotOne) :=
    Finset.card_pos.mp (by omega)
  refine false_of_spanning_tight_directions frame.hdata (by norm_num)
    (fun tripleIndex => frame.basisLabel (![slotOne, slotTwo, slotThree]
      tripleIndex))
    (fun tripleIndex => frame.hmemAll _)
    (hindepAll.comp ![slotOne, slotTwo, slotThree] hinjTriple)
    hcard ?_ ?_ hfloorMem
    (crux.gap_diagonal_pos_of_allHeavy floorAtom) frame.hvalueNeg
  · intro tripleIndex atomIndex hnonzero
    have hmemBlock : atomIndex ∈ frame.activeSubset (frame.basisLabel
        (![slotOne, slotTwo, slotThree] tripleIndex)) := by
      by_contra hout
      exact hnonzero (frame.hdata.tightDir_support _ (frame.hmemAll _)
        atomIndex hout)
    rwa [hblockAll tripleIndex] at hmemBlock
  · intro tripleIndex
    rw [hblockAll tripleIndex]

/-! ## The rank-five private-pair kill -/

/-- **THE PRIVATE-PAIR KILL.**  A basis direction on a two-atom support
that no other basis label touches dies at every rank-five frame.  The
pair-kernel collapse aligns the capture on the pair, the squeeze zeroes
the two shifted weights, and the vanishing projected direction makes the
two design atoms parallel. -/
theorem RankFiveFrame.false_of_supportTwo_private_pair {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) (columnIndex : Fin 5)
    {atomU atomV : Fin 6} (hUV : atomU ≠ atomV)
    (hneU : frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0)
    (hneV : frame.tightDir (frame.basisLabel columnIndex) atomV ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0)
    (hprivU : ∀ otherIndex, otherIndex ≠ columnIndex →
      frame.tightDir (frame.basisLabel otherIndex) atomU = 0)
    (hprivV : ∀ otherIndex, otherIndex ≠ columnIndex →
      frame.tightDir (frame.basisLabel otherIndex) atomV = 0) :
    False := by
  classical
  have hdata := frame.hdata
  have hmem := frame.hmemAll columnIndex
  have hvalueNeg := frame.hvalueNeg
  set pairDir := frame.tightDir (frame.basisLabel columnIndex) with hdirDef
  have hbasisKernel : (tightBasisColumns frame.tightDir frame.basisLabel)ᵀ
      *ᵥ pairKernelVec (pairDir atomU) (pairDir atomV) atomU atomV = 0 := by
    apply basis_transpose_mulVec_pairKernelVec hUV
    intro slotIndex
    by_cases hslot : slotIndex = columnIndex
    · subst hslot
      ring
    · rw [hprivU slotIndex hslot, hprivV slotIndex hslot]
      ring
  have hassemblyKernel : chartMultiplierAssembly frame.activeSet frame.reducedWeight
      frame.tightDir *ᵥ pairKernelVec (pairDir atomU) (pairDir atomV) atomU atomV
      = 0 :=
    assembly_mulVec_of_basis_transpose_zero frame.hHform hbasisKernel
  have hcaptureKernel : ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
      *ᵥ pairKernelVec (pairDir atomU) (pairDir atomV) atomU atomV = 0 := by
    rw [← Matrix.mulVec_mulVec, hassemblyKernel, Matrix.mulVec_zero]
  have halignU : ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomU atomU * pairDir atomV
      - ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomU atomV * pairDir atomU = 0 := by
    have hentry := congrFun hcaptureKernel atomU
    rwa [mulVec_pairKernelVec_apply ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) hUV (pairDir atomU)
      (pairDir atomV) atomU, Pi.zero_apply] at hentry
  have halignV : ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomV atomU * pairDir atomV
      - ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomV atomV * pairDir atomU = 0 := by
    have hentry := congrFun hcaptureKernel atomV
    rwa [mulVec_pairKernelVec_apply ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) hUV (pairDir atomU)
      (pairDir atomV) atomV, Pi.zero_apply] at hentry
  have hunit : pairDir atomU ^ 2 + pairDir atomV ^ 2 = 1 :=
    pair_support_unit_read hdata hmem hUV hsupp
  have hquadRead : pairDir ⬝ᵥ (((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) *ᵥ pairDir)
      = ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomU atomU + ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomV atomV := by
    rw [dotProduct_mulVec_of_pair_support ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) hUV hsupp]
    linear_combination (-(pairDir atomV)) * halignU + (pairDir atomU) * halignV
      + (((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomU atomU + ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomV atomV) * hunit
  have hdiagU := diagonal_projection_mul_multiplier_of_isChartStationaryData
    hdata atomU
  have hdiagV := diagonal_projection_mul_multiplier_of_isChartStationaryData
    hdata atomV
  have hrayleigh := capture_quadratic_le_of_isChartStationaryData hdata pairDir
  have henergy : pairDir ⬝ᵥ ((chartPointOfDesign crux.design).chart *ᵥ pairDir)
      = chartObjective (chartPointOfDesign crux.design)
        + ((chartPointOfDesign crux.design).weight atomU * pairDir atomU ^ 2
          + (chartPointOfDesign crux.design).weight atomV * pairDir atomV ^ 2) := by
    have hread := tight_energy_read hdata hmem
    rw [hread, pair_support_energy_read hUV hsupp]
  have hfloorU := capture_diagonal_nonneg_of_isChartStationaryData hdata atomU
  have hfloorV := capture_diagonal_nonneg_of_isChartStationaryData hdata atomV
  have htraceFloor := capture_trace_nonneg_of_isChartStationaryData hdata
  have hinv : (0 : ℝ) < (((6 : ℕ) : ℝ))⁻¹ := by norm_num
  have hsqU : (0 : ℝ) < pairDir atomU ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hneU))
  have hsqV : (0 : ℝ) < pairDir atomV ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hneV))
  have hbothZero : chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomU = 0
      ∧ chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomV = 0 := by
    rcases le_total ((chartPointOfDesign crux.design).weight atomU)
      ((chartPointOfDesign crux.design).weight atomV) with horder | horder
    · exact support_two_capture_squeeze hvalueNeg hinv htraceFloor hfloorU
        hfloorV hsqU.le hsqV hunit henergy
        (by rw [hquadRead, hdiagU, hdiagV]; ring) hrayleigh horder
    · have hswap := support_two_capture_squeeze hvalueNeg hinv htraceFloor
        hfloorV hfloorU hsqV.le hsqU (by linarith [hunit])
        (by rw [henergy]; ring)
        (by rw [hquadRead, hdiagU, hdiagV]; ring) hrayleigh horder
      exact ⟨hswap.2, hswap.1⟩
  have henergyZero : pairDir ⬝ᵥ ((chartPointOfDesign crux.design).chart *ᵥ pairDir)
      = 0 := by
    rw [henergy]
    nlinarith [hbothZero.1, hbothZero.2, hunit]
  have hprojZero : (chartPointOfDesign crux.design).chart *ᵥ pairDir = 0 :=
    projection_mulVec_eq_zero_of_energy_eq_zero hdata henergyZero
  have hdirForm : pairDir
      = pairKernelVec (-(pairDir atomV)) (pairDir atomU) atomU atomV := by
    funext atomIndex
    by_cases hU : atomIndex = atomU
    · subst hU
      rw [pairKernelVec_apply_one]
    by_cases hV : atomIndex = atomV
    · subst hV
      rw [pairKernelVec_apply_two hUV, neg_neg]
    · rw [hsupp atomIndex hU hV, pairKernelVec_apply_off hU hV]
  have hkernel : (chartPointOfDesign crux.design).chart
      *ᵥ pairKernelVec (-(pairDir atomV)) (pairDir atomU) atomU atomV = 0 := by
    rw [← hdirForm]
    exact hprojZero
  exact crux.false_of_projection_kernel_pair hUV hneU hkernel

/-- **THE FIRST BRIDGE.**  The rank-five support-two closure follows from
the shared-pair kill: the pair is private and dies here, or some other
basis label carries a pair atom. -/
theorem rankFiveSupportTwoClosed_of_shared_pair_kill
    (killShared : ∀ (crux : SixThreeCrux) (frame : RankFiveFrame crux)
      (columnIndex otherIndex : Fin 5) (atomU atomV : Fin 6),
      (datumTightSupport frame.tightDir (frame.basisLabel columnIndex)).card = 2 →
      atomU ≠ atomV →
      frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0 →
      frame.tightDir (frame.basisLabel columnIndex) atomV ≠ 0 →
      (∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
        frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0) →
      otherIndex ≠ columnIndex →
      (frame.tightDir (frame.basisLabel otherIndex) atomU ≠ 0
        ∨ frame.tightDir (frame.basisLabel otherIndex) atomV ≠ 0) →
      False) :
    RankFiveSupportTwoClosed := by
  intro crux frame columnIndex hcard
  obtain ⟨atomU, atomV, hUV, hneU, hneV, hsupp⟩ :=
    exists_pair_of_support_card_two hcard
  by_cases hshared : ∃ otherIndex, otherIndex ≠ columnIndex ∧
      (frame.tightDir (frame.basisLabel otherIndex) atomU ≠ 0
        ∨ frame.tightDir (frame.basisLabel otherIndex) atomV ≠ 0)
  · obtain ⟨otherIndex, hne, hcarry⟩ := hshared
    exact killShared crux frame columnIndex otherIndex atomU atomV hcard hUV
      hneU hneV hsupp hne hcarry
  · push Not at hshared
    exact frame.false_of_supportTwo_private_pair columnIndex hUV hneU hneV hsupp
      (fun otherIndex hne => (hshared otherIndex hne).1)
      (fun otherIndex hne => (hshared otherIndex hne).2)

/-! ## The rank-five same-pair kill -/

/-- **THE SAME-PAIR KILL.**  Two distinct basis columns supported inside
one pair of atoms are impossible at a rank-five frame.  A zero column
breaks the unit norm.  A singleton column dies at the floor.  Two genuine
pair columns are independent through the left inverse, thus the two-atom
gap block is the value times the identity, and the floor kills the
diagonal. -/
theorem RankFiveFrame.false_of_samePair_columns {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {colA colB : Fin 5} (hne : colB ≠ colA)
    {atomU atomV : Fin 6} (hUV : atomU ≠ atomV)
    (hAU : frame.tightDir (frame.basisLabel colA) atomU ≠ 0)
    (hAV : frame.tightDir (frame.basisLabel colA) atomV ≠ 0)
    (hAsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel colA) atomIndex = 0)
    (hBsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel colB) atomIndex = 0) : False := by
  by_cases hBU : frame.tightDir (frame.basisLabel colB) atomU = 0
  · by_cases hBV : frame.tightDir (frame.basisLabel colB) atomV = 0
    · have hzero : ∀ atomIndex, frame.tightDir (frame.basisLabel colB) atomIndex = 0 := by
        intro atomIndex
        by_cases hU : atomIndex = atomU
        · rw [hU]; exact hBU
        by_cases hV : atomIndex = atomV
        · rw [hV]; exact hBV
        · exact hBsupp atomIndex hU hV
      have hunit := frame.hdata.tightDir_unit _ (frame.hmemAll colB)
      have hsum : frame.tightDir (frame.basisLabel colB)
          ⬝ᵥ frame.tightDir (frame.basisLabel colB) = 0 := by
        show (∑ atomIndex : Fin 6, _ * _) = 0
        refine Finset.sum_eq_zero fun atomIndex _ => ?_
        rw [hzero atomIndex, mul_zero]
      rw [hsum] at hunit
      exact zero_ne_one hunit
    · refine false_of_singleton_tight_direction frame.hdata (frame.hmemAll colB)
        hBV (fun atomIndex hV => ?_)
        (crux.gap_diagonal_pos_of_allHeavy atomV) frame.hvalueNeg
      by_cases hU : atomIndex = atomU
      · rw [hU]; exact hBU
      · exact hBsupp atomIndex hU hV
  · by_cases hBV : frame.tightDir (frame.basisLabel colB) atomV = 0
    · refine false_of_singleton_tight_direction frame.hdata (frame.hmemAll colB)
        hBU (fun atomIndex hU => ?_)
        (crux.gap_diagonal_pos_of_allHeavy atomU) frame.hvalueNeg
      by_cases hV : atomIndex = atomV
      · rw [hV]; exact hBV
      · exact hBsupp atomIndex hU hV
    · have hmemAU : atomU ∈ frame.activeSubset (frame.basisLabel colA) := by
        by_contra hout
        exact hAU (frame.hdata.tightDir_support _ (frame.hmemAll colA) atomU hout)
      have hmemBU : atomU ∈ frame.activeSubset (frame.basisLabel colB) := by
        by_contra hout
        exact hBU (frame.hdata.tightDir_support _ (frame.hmemAll colB) atomU hout)
      have hrowAU := frame.hdata.tightDir_isTight _ (frame.hmemAll colA) atomU hmemAU
      have hrowBU := frame.hdata.tightDir_isTight _ (frame.hmemAll colB) atomU hmemBU
      rw [mulVec_apply_of_pair_support _ hUV hAsupp atomU] at hrowAU
      rw [mulVec_apply_of_pair_support _ hUV hBsupp atomU] at hrowBU
      by_cases hD : frame.tightDir (frame.basisLabel colA) atomU
            * frame.tightDir (frame.basisLabel colB) atomV
          - frame.tightDir (frame.basisLabel colA) atomV
            * frame.tightDir (frame.basisLabel colB) atomU = 0
      · have hratio : frame.tightDir (frame.basisLabel colB)
            = (frame.tightDir (frame.basisLabel colB) atomU
                / frame.tightDir (frame.basisLabel colA) atomU)
              • frame.tightDir (frame.basisLabel colA) := by
          funext atomIndex
          by_cases hU : atomIndex = atomU
          · subst hU
            rw [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hAU]
          by_cases hV : atomIndex = atomV
          · subst hV
            rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div,
              eq_div_iff hAU]
            linear_combination hD
          · rw [hBsupp atomIndex hU hV, Pi.smul_apply, smul_eq_mul,
              hAsupp atomIndex hU hV, mul_zero]
        have hentryB : (frame.leftInv
            * tightBasisColumns frame.tightDir frame.basisLabel) colB colB = 1 := by
          rw [frame.hleft, Matrix.one_apply_eq]
        have hentryA : (frame.leftInv
            * tightBasisColumns frame.tightDir frame.basisLabel) colB colA = 0 := by
          rw [frame.hleft]
          exact Matrix.one_apply_ne hne
        have hexpB : (frame.leftInv
              * tightBasisColumns frame.tightDir frame.basisLabel) colB colB
            = ∑ atomIndex : Fin 6, frame.leftInv colB atomIndex
                * frame.tightDir (frame.basisLabel colB) atomIndex := rfl
        have hexpA : (frame.leftInv
              * tightBasisColumns frame.tightDir frame.basisLabel) colB colA
            = ∑ atomIndex : Fin 6, frame.leftInv colB atomIndex
                * frame.tightDir (frame.basisLabel colA) atomIndex := rfl
        rw [hexpB] at hentryB
        rw [hexpA] at hentryA
        have hscaled : ∑ atomIndex : Fin 6, frame.leftInv colB atomIndex
              * frame.tightDir (frame.basisLabel colB) atomIndex
            = (frame.tightDir (frame.basisLabel colB) atomU
                / frame.tightDir (frame.basisLabel colA) atomU)
              * ∑ atomIndex : Fin 6, frame.leftInv colB atomIndex
                  * frame.tightDir (frame.basisLabel colA) atomIndex := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun atomIndex _ => ?_
          rw [congrFun hratio atomIndex, Pi.smul_apply, smul_eq_mul]
          ring
        rw [hscaled, hentryA, mul_zero] at hentryB
        exact zero_ne_one hentryB
      · have helim : (chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomU atomU
              - chartObjective (chartPointOfDesign crux.design))
            * (frame.tightDir (frame.basisLabel colA) atomU
                * frame.tightDir (frame.basisLabel colB) atomV
              - frame.tightDir (frame.basisLabel colA) atomV
                * frame.tightDir (frame.basisLabel colB) atomU) = 0 := by
          linear_combination frame.tightDir (frame.basisLabel colB) atomV * hrowAU
            - frame.tightDir (frame.basisLabel colA) atomV * hrowBU
        rcases mul_eq_zero.mp helim with hzero | hzero
        · have hgap := sub_eq_zero.mp hzero
          have hfloor := crux.gap_diagonal_pos_of_allHeavy atomU
          rw [hgap] at hfloor
          exact absurd frame.hvalueNeg (by linarith)
        · exact hD hzero

/-- **THE REFINED BRIDGE.**  The rank-five support-two closure follows
from one residual: the outer sharer kill, where some other basis label
carries a nonzero atom outside the pair.  The inner sharers die here. -/
theorem rankFiveSupportTwoClosed_of_outer_shared_kill
    (killOuter : ∀ (crux : SixThreeCrux) (frame : RankFiveFrame crux)
      (columnIndex otherIndex : Fin 5) (atomU atomV atomT : Fin 6),
      (datumTightSupport frame.tightDir (frame.basisLabel columnIndex)).card = 2 →
      atomU ≠ atomV →
      frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0 →
      frame.tightDir (frame.basisLabel columnIndex) atomV ≠ 0 →
      (∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
        frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0) →
      otherIndex ≠ columnIndex →
      atomT ≠ atomU → atomT ≠ atomV →
      frame.tightDir (frame.basisLabel otherIndex) atomT ≠ 0 →
      False) :
    RankFiveSupportTwoClosed := by
  refine rankFiveSupportTwoClosed_of_shared_pair_kill ?_
  intro crux frame columnIndex otherIndex atomU atomV hcard hUV hneU hneV hsupp
    hneCol _hcarry
  by_cases houter : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel otherIndex) atomIndex = 0
  · exact frame.false_of_samePair_columns hneCol hUV hneU hneV hsupp houter
  · push Not at houter
    obtain ⟨atomT, hTU, hTV, hneT⟩ := houter
    exact killOuter crux frame columnIndex otherIndex atomU atomV atomT hcard
      hUV hneU hneV hsupp hneCol hTU hTV hneT

end Gtz

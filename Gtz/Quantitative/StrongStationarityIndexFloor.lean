import Gtz.Quantitative.ChartArgmaxIndexFloorTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The strong-stationarity index floor

Strong chart stationarity quantifies over EVERY tight-direction selection, so a
selection built from block least-eigenvectors can be fed in and the matching
multiplier comes back.  The compatibility hypothesis dissolves rather than gets
proved, and a block whose least eigenvalue has multiplicity above one stops
mattering.  That mechanism is what carries the unconditional floor below.

## Which results are unconditional and which are not

UNCONDITIONAL on `SixThreeCrux` alone:

* `SixThreeCrux.four_le_card_chartArgmaxFamily_strong` -- at least FOUR active
  blocks.  This raises the shipped floor of three.
* `SixThreeCrux.exists_argmax_supportTwo_coordinateSingles_mem_finiteRowSpan` --
  a tight-vector family, a balanced multiplier, and an active block whose tight
  support has at least two labels, each of whose coordinate singles lies in the
  finite row span.
* `SixThreeCrux.exists_multiplier_assembly_totalEigenSquareRow` -- the balanced
  multiplier itself.

CONDITIONAL ONLY ON THE ACTIVE COUNT BEING EXACTLY FOUR:

* `SixThreeCrux.not_forall_exists_fullSupport_activeEigenvector_of_card_eq_four`
* `SixThreeCrux.exists_active_coordinate_zero_on_tightEigenspace_of_card_eq_four`
  -- some active block carries a coordinate that vanishes on its WHOLE tight
  eigenspace, not merely on one chosen eigenvector.

CONDITIONAL ON SUPPLIED TIGHT-EIGENVECTOR DATA, and therefore substrate rather
than result:

* `SixThreeCrux.two_le_card_totalTightSupport` -- support at least two, given a
  unit eigenvector family.
* `SixThreeCrux.five_le_card_chartArgmaxFamily_of_fullSupport` -- full support
  at every card-three subset.
* `SixThreeCrux.five_le_card_chartArgmaxFamily_of_activeFullSupport` -- the same
  conclusion from full support at the ACTIVE blocks only, plus a balanced
  multiplier.  Strictly the weaker hypothesis of the two.
* `SixThreeCrux.false_of_flatPair_of_activeFullSupport` -- active full support
  together with a flat pair separated at one pivot coordinate.  Its conclusion
  is `False`, so it is a CONDITIONAL REFUTATION of that configuration; it is not
  a proof of `False` and it does not close the cell.

## What is not settled here

The satisfiability of the supplied-data hypotheses is NOT established in this
module.  In particular nothing here exhibits a tight-eigenvector family with
active full support, and nothing here exhibits a flat pair.  Every statement
above is about `SixThreeCrux`, which is conjecturally empty: if GTZ holds, they
are all vacuous.  They earn their place by contracting the counterexample normal
form, not by inhabiting it.
-/

namespace Gtz

open Matrix

/-- Spread a chosen block eigenvector to the ambient six coordinates.  The junk branch is
never used on a member of the `(6,3)` argmax family. -/
noncomputable def ambientTightSelection
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (selected : Finset (Fin 6)) : Fin 6 → ℝ :=
  if hcard : selected.card = 3 then
    selectionInjection (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
  else 0

/-- A block eigenvector at an argmax block, spread to ambient coordinates, is one of the
tight directions quantified over by strong chart stationarity. -/
theorem isChartTightDirection_ambientTightSelection
    (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    {selected : Finset (Fin 6)}
    (hmember : selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design)) :
    IsChartTightDirection (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) selected
      (ambientTightSelection tightVec selected) := by
  have hcard : selected.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp hmember).1
  have hobjectiveLe :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp hmember).2
  have hblockLe : chartBlockValue 3
      (((chartPointOfDesign crux.design).chart,
          (chartPointOfDesign crux.design).weight) :
          (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected
        ≤ chartObjective (chartPointOfDesign crux.design) :=
    Finset.le_sup'
      (f := fun candidate => chartBlockValue 3
        (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) candidate)
      ((mem_chartCandidates_iff 6 3 selected).mpr hcard)
  have hvalue : chartBlockValue 3
      (((chartPointOfDesign crux.design).chart,
          (chartPointOfDesign crux.design).weight) :
          (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected
        = chartObjective (chartPointOfDesign crux.design) :=
    le_antisymm hblockLe hobjectiveLe
  rw [ambientTightSelection, dif_pos hcard]
  refine ⟨?_, ?_, ?_⟩
  · have hdict := dotProduct_selectionInjection_mulVec
      (1 : Matrix (Fin 6) (Fin 6) ℝ) (selected.orderEmbOfFin hcard) (tightVec selected)
    rw [Matrix.submatrix_one _ (selected.orderEmbOfFin hcard).injective,
      Matrix.one_mulVec, Matrix.one_mulVec] at hdict
    rw [hdict]
    exact hunit selected hcard
  · intro atomIndex hnotMember
    refine selectionInjection_mulVec_eq_zero_of_notMem _ _ fun selectedIndex heq =>
      hnotMember ?_
    have hrange : selected.orderEmbOfFin hcard selectedIndex
        ∈ Set.range (selected.orderEmbOfFin hcard) := ⟨selectedIndex, rfl⟩
    rw [Finset.range_orderEmbOfFin selected hcard] at hrange
    exact heq ▸ hrange
  · intro atomIndex hmemberSelected
    obtain ⟨selectedIndex, rfl⟩ :
        ∃ selectedIndex, selected.orderEmbOfFin hcard selectedIndex = atomIndex := by
      have hrange : atomIndex ∈ Set.range (selected.orderEmbOfFin hcard) := by
        rw [Finset.range_orderEmbOfFin selected hcard]
        exact hmemberSelected
      exact hrange
    rw [show chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          = chartPointGap (chartPointOfDesign crux.design) from rfl,
      mulVec_selectionInjection_apply, hEigen selected hcard, hvalue,
      selectionInjection_mulVec_apply (selected.orderEmbOfFin hcard).injective]
    simp

/-- **THE STRONG-STATIONARITY COMPATIBILITY WELD.**  The five-block index floor needs no
separate compatibility assumption, even at a multiple least eigenvalue.  Strong
stationarity balances every choice of active tight direction, so choose precisely the
ambient spreads of the block eigenvectors used by the second-order layer. -/
theorem SixThreeCrux.five_le_card_chartArgmaxFamily_of_fullSupport
    (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (hfullSupport : ∀ (selected : Finset (Fin 6)) (blockIndex : Fin 3),
      tightVec selected blockIndex ≠ 0) :
    5 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card := by
  let selection : Finset (Fin 6) → (Fin 6 → ℝ) := ambientTightSelection tightVec
  have hselection : ∀ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      IsChartTightDirection (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) selected (selection selected) := by
    intro selected hmember
    exact isChartTightDirection_ambientTightSelection crux tightVec hunit hEigen hmember
  obtain ⟨multiplier, hdata⟩ :=
    exists_multiplier_isChartStationaryData_of_isChartStrongStationaryData
      crux.isChartStrongStationaryData selection hselection
  refine crux.five_le_card_chartArgmaxFamily_of_blockRestriction tightVec hunit hEigen
    hfullSupport multiplier selection hdata ?_
  intro selected hmember hcard
  funext blockIndex
  dsimp only [selection]
  rw [ambientTightSelection, dif_pos hcard,
    selectionInjection_mulVec_apply (selected.orderEmbOfFin hcard).injective]

/-- Strong stationarity supplies the constant assembly diagonal for the very block
eigenvectors used by the second-order argument. -/
theorem SixThreeCrux.exists_multiplier_assembly_totalEigenSquareRow
    (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected) :
    ∃ multiplier : Finset (Fin 6) → ℝ, ∀ atomIndex : Fin 6,
      ∑ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
        multiplier selected * totalEigenSquareRow tightVec selected atomIndex
          = (((6 : ℕ) : ℝ))⁻¹ := by
  let selection : Finset (Fin 6) → (Fin 6 → ℝ) := ambientTightSelection tightVec
  have hselection : ∀ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      IsChartTightDirection (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) selected (selection selected) := by
    intro selected hmember
    exact isChartTightDirection_ambientTightSelection crux tightVec hunit hEigen hmember
  obtain ⟨multiplier, hdata⟩ :=
    exists_multiplier_isChartStationaryData_of_isChartStrongStationaryData
      crux.isChartStrongStationaryData selection hselection
  refine ⟨multiplier, fun atomIndex =>
    assemblyDiagonal_of_isChartStationaryData_of_rowEq hdata
      (totalEigenSquareRow tightVec) ?_ atomIndex⟩
  intro selected hmember atomIndex
  have hcard : selected.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp hmember).1
  have hrestriction : tightVec selected = fun blockIndex =>
      selection selected (selected.orderEmbOfFin hcard blockIndex) := by
    funext blockIndex
    dsimp only [selection]
    rw [ambientTightSelection, dif_pos hcard,
      selectionInjection_mulVec_apply (selected.orderEmbOfFin hcard).injective]
  rw [totalEigenSquareRow_of_card tightVec hcard, hrestriction]
  exact eigenSquareRow_eq_mul_self_of_support hcard (selection selected)
    (hdata.tightDir_support selected hmember) atomIndex

/-- A negative eigenvector of a matrix with positive diagonal has at least two nonzero
coordinates. -/
theorem exists_two_ne_zero_of_unit_eigen_of_neg_of_pos_diagonal
    {n : ℕ} (form : Matrix (Fin n) (Fin n) ℝ) (vec : Fin n → ℝ) (value : ℝ)
    (hunit : vec ⬝ᵥ vec = 1) (hEigen : form *ᵥ vec = value • vec)
    (hvalue : value < 0) (hdiag : ∀ coordinate, 0 < form coordinate coordinate) :
    ∃ first second : Fin n, first ≠ second ∧ vec first ≠ 0 ∧ vec second ≠ 0 := by
  by_contra hnone
  have hexists : ∃ coordinate, vec coordinate ≠ 0 := by
    by_contra hall
    have hallZero : ∀ coordinate, vec coordinate = 0 := by
      intro coordinate
      by_contra hne
      exact hall ⟨coordinate, hne⟩
    have hzero : vec = 0 := funext hallZero
    simp [hzero, dotProduct] at hunit
  obtain ⟨pivot, hpivot⟩ := hexists
  have hzero : ∀ other, other ≠ pivot → vec other = 0 := by
    intro other hne
    by_contra hother
    exact hnone ⟨pivot, other, hne.symm, hpivot, hother⟩
  have hcoordinate := congrFun hEigen pivot
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hcoordinate
  have hsum : ∑ other, form pivot other * vec other = form pivot pivot * vec pivot := by
    rw [Finset.sum_eq_single pivot]
    · intro other _ hne
      rw [hzero other hne, mul_zero]
    · simp
  rw [hsum] at hcoordinate
  rcases lt_or_gt_of_ne hpivot with hpivotNeg | hpivotPos
  · have : form pivot pivot = value := by nlinarith
    nlinarith [hdiag pivot]
  · have : form pivot pivot = value := by nlinarith
    nlinarith [hdiag pivot]

/-- Every card-three chart block has a unit least eigenvector, chosen simultaneously. -/
theorem exists_unit_chartBlockEigenvectorFamily (point : ChartPoint 6 3) :
    ∃ tightVec : Finset (Fin 6) → (Fin 3 → ℝ),
      (∀ selected : Finset (Fin 6), selected.card = 3 →
        tightVec selected ⬝ᵥ tightVec selected = 1)
      ∧ (∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
        (chartPointGap point).submatrix
            (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
          = chartBlockValue 3 ((point.chart, point.weight) :
              (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected) := by
  classical
  have hexists : ∀ selected : Finset (Fin 6), ∃ vec : Fin 3 → ℝ,
      ∀ hcard : selected.card = 3,
        vec ⬝ᵥ vec = 1 ∧
        (chartPointGap point).submatrix
            (selected.orderEmbOfFin hcard)
            (selected.orderEmbOfFin hcard) *ᵥ vec
          = chartBlockValue 3 ((point.chart, point.weight) :
              (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • vec := by
    intro selected
    by_cases hcard : selected.card = 3
    · obtain ⟨vec, hunit, hEigen⟩ := exists_unit_eigenvector_lambdaMinMat
        ((chartPointGap point).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard))
        (isHermitian_chartPointGap_submatrix point selected hcard)
      refine ⟨vec, fun hcard' => ⟨hunit, ?_⟩⟩
      rw [chartBlockValue_chartConfig point hcard']
      funext coordinate
      exact hEigen coordinate
    · exact ⟨0, fun hfalse => (hcard hfalse).elim⟩
  choose tightVec hspec using hexists
  exact ⟨tightVec, fun selected hcard => (hspec selected hcard).1,
    fun selected hcard => (hspec selected hcard).2⟩

/-- **UNCONDITIONAL FOUR-BLOCK FLOOR AT A CRUX.**  A crux has negative chart value and
strictly positive chart-gap diagonal.  Therefore every least eigenvector has support at
least two; strong stationarity supplies its matching assembly, and the support-two rung
fires. -/
theorem SixThreeCrux.four_le_card_chartArgmaxFamily_strong (crux : SixThreeCrux) :
    4 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card := by
  obtain ⟨tightVec, hunit, hEigen⟩ :=
    exists_unit_chartBlockEigenvectorFamily (chartPointOfDesign crux.design)
  have hsupport : ∀ selected : Finset (Fin 6), selected.card = 3 →
      2 ≤ (totalTightSupport tightVec selected).card := by
    intro selected hcard
    let block := (chartPointGap (chartPointOfDesign crux.design)).submatrix
      (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)
    let value := chartBlockValue 3
      (((chartPointOfDesign crux.design).chart,
          (chartPointOfDesign crux.design).weight) :
          (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected
    have hvalueLe : value ≤ chartObjective (chartPointOfDesign crux.design) :=
      Finset.le_sup'
        (f := fun candidate => chartBlockValue 3
          (((chartPointOfDesign crux.design).chart,
              (chartPointOfDesign crux.design).weight) :
              (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) candidate)
        ((mem_chartCandidates_iff 6 3 selected).mpr hcard)
    have hvalueNeg : value < 0 := lt_of_le_of_lt hvalueLe crux.hasNegativeChartValue
    have hdiag : ∀ coordinate, 0 < block coordinate coordinate := by
      intro coordinate
      simp only [block, Matrix.submatrix_apply, chartPointGap, chartPointOfDesign,
        Matrix.sub_apply, Matrix.diagonal_apply_eq]
      rw [projectionOfDesign_diagonal]
      have hweight := crux.design.weight_pos (selected.orderEmbOfFin hcard coordinate)
      have hexcess := allHeavy_heavyExcess_pos crux.isAllHeavy
        (selected.orderEmbOfFin hcard coordinate)
      rw [heavyExcess] at hexcess
      nlinarith
    obtain ⟨first, second, hne, hfirst, hsecond⟩ :=
      exists_two_ne_zero_of_unit_eigen_of_neg_of_pos_diagonal block (tightVec selected) value
        (hunit selected hcard) (hEigen selected hcard) hvalueNeg hdiag
    exact two_le_card_totalTightSupport tightVec hcard hne hfirst hsecond
  obtain ⟨multiplier, hassembly⟩ :=
    crux.exists_multiplier_assembly_totalEigenSquareRow tightVec hunit hEigen
  exact crux.four_le_card_chartArgmaxFamily_of_supportTwo tightVec hunit hEigen hsupport
    multiplier hassembly

/-! ## The exact four-block residual -/

/-- Full coordinate support on a card-three block makes the ambient tight support equal
to the whole block. -/
theorem totalTightSupport_eq_self_of_fullSupport
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    (hfull : ∀ blockIndex : Fin 3, tightVec selected blockIndex ≠ 0) :
    totalTightSupport tightVec selected = selected := by
  classical
  apply Finset.Subset.antisymm (totalTightSupport_subset tightVec hcard)
  intro atomIndex hmember
  have hrange : atomIndex ∈ Set.range (selected.orderEmbOfFin hcard) := by
    rw [Finset.range_orderEmbOfFin selected hcard]
    exact hmember
  obtain ⟨blockIndex, rfl⟩ := hrange
  exact mem_totalTightSupport tightVec hcard (hfull blockIndex)

/-- The flat-pair contradiction only needs full support at active blocks.  The older
interface asks for it at every finite subset, although the proof's covering block and
separator block both come from the argmax family. -/
theorem SixThreeCrux.false_of_flatPair_of_activeFullSupport
    (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (hfull : ∀ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      ∀ blockIndex : Fin 3, tightVec selected blockIndex ≠ 0)
    {first second : Fin 6 → ℝ} {pivot : Fin 6}
    (hfirstMem : first ∈ flatSumZeroSubmodule
      (chartArgmaxFamily (chartPointOfDesign crux.design)) (totalEigenSquareRow tightVec))
    (hsecondMem : second ∈ flatSumZeroSubmodule
      (chartArgmaxFamily (chartPointOfDesign crux.design)) (totalEigenSquareRow tightVec))
    (hsecondNe : second ≠ 0)
    (hpivotFirst : first pivot ≠ 0) (hpivotSecond : second pivot = 0) :
    False := by
  classical
  set family := chartArgmaxFamily (chartPointOfDesign crux.design) with hfamily
  set flatSpace := flatSumZeroSubmodule family (totalEigenSquareRow tightVec) with hflatSpace
  obtain ⟨baseBlock, hbaseMem, hleSupport⟩ :=
    crux.exists_argmax_le_vanishingSubmodule_totalTightSupport tightVec hunit hEigen
  have hmemberCard : ∀ block ∈ family, block.card = 3 := fun block hmem =>
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) block).mp hmem).1
  have hbaseCard : baseBlock.card = 3 := hmemberCard baseBlock hbaseMem
  have hbaseSupport : totalTightSupport tightVec baseBlock = baseBlock :=
    totalTightSupport_eq_self_of_fullSupport tightVec hbaseCard (hfull baseBlock hbaseMem)
  have hle : flatSpace ≤ vanishingSubmodule baseBlock := by
    intro direction hdirection atomIndex hmem
    exact hleSupport hdirection atomIndex (hbaseSupport.symm ▸ hmem)
  have hcomplCard : baseBlockᶜ.card = 3 := by
    rw [Finset.card_compl, hbaseCard, Fintype.card_fin]
  have hthree : 3 ≤ family.card := crux.three_le_card_chartArgmaxFamily
  have hpairCard : ({baseBlock, baseBlockᶜ} : Finset (Finset (Fin 6))).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    rw [Finset.card_singleton]
  have hleftover : (family \ ({baseBlock, baseBlockᶜ} : Finset (Finset (Fin 6)))).Nonempty := by
    refine Finset.card_pos.mp ?_
    have hbound := Finset.le_card_sdiff
      ({baseBlock, baseBlockᶜ} : Finset (Finset (Fin 6))) family
    omega
  obtain ⟨partner, hpartnerSdiff⟩ := hleftover
  rw [Finset.mem_sdiff] at hpartnerSdiff
  obtain ⟨hpartnerMem, hpartnerNot⟩ := hpartnerSdiff
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpartnerNot
  obtain ⟨hpartnerNeBase, hpartnerNeCompl⟩ := hpartnerNot
  have hpartnerCard : partner.card = 3 := hmemberCard partner hpartnerMem
  set partnerRow := totalEigenSquareRow tightVec partner with hpartnerRow
  have hpartnerRowEq : partnerRow = eigenSquareRow partner hpartnerCard (tightVec partner) :=
    totalEigenSquareRow_of_card tightVec hpartnerCard
  have hnotSubBase : ¬ partner ⊆ baseBlock := fun hsub =>
    hpartnerNeBase (Finset.eq_of_subset_of_card_le hsub (by omega))
  obtain ⟨positiveAtom, hpositiveMem, hpositiveNotBase⟩ := Finset.not_subset.mp hnotSubBase
  have hnotSubPartner : ¬ baseBlockᶜ ⊆ partner := fun hsub =>
    hpartnerNeCompl (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  obtain ⟨zeroAtom, hzeroCompl, hzeroNotPartner⟩ := Finset.not_subset.mp hnotSubPartner
  have hpositiveCompl : positiveAtom ∈ baseBlockᶜ := Finset.mem_compl.mpr hpositiveNotBase
  have hpositiveValue : 0 < partnerRow positiveAtom := by
    rw [hpartnerRowEq]
    exact eigenSquareRow_pos_of_mem hpartnerCard (hfull partner hpartnerMem) hpositiveMem
  have hzeroValue : partnerRow zeroAtom = 0 := by
    rw [hpartnerRowEq]
    exact eigenSquareRow_eq_zero_of_notMem hpartnerCard (tightVec partner) hzeroNotPartner
  have hrowDistinct : partnerRow positiveAtom ≠ partnerRow zeroAtom := by
    rw [hzeroValue]
    exact ne_of_gt hpositiveValue
  have hatomsDistinct : positiveAtom ≠ zeroAtom := fun hcollide =>
    hrowDistinct (by rw [hcollide])
  have hatomPairCard : ({positiveAtom, zeroAtom} : Finset (Fin 6)).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    rw [Finset.card_singleton]
  have hthirdNonempty :
      (baseBlockᶜ \ ({positiveAtom, zeroAtom} : Finset (Fin 6))).Nonempty := by
    refine Finset.card_pos.mp ?_
    have hbound := Finset.le_card_sdiff
      ({positiveAtom, zeroAtom} : Finset (Fin 6)) baseBlockᶜ
    omega
  obtain ⟨thirdAtom, hthirdSdiff⟩ := hthirdNonempty
  rw [Finset.mem_sdiff] at hthirdSdiff
  obtain ⟨hthirdCompl, hthirdNot⟩ := hthirdSdiff
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hthirdNot
  obtain ⟨hthirdNePositive, hthirdNeZeroAtom⟩ := hthirdNot
  have hcomplTriple : baseBlockᶜ = {positiveAtom, zeroAtom, thirdAtom} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro atomIndex hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact hpositiveCompl
      · exact hzeroCompl
      · exact hthirdCompl
    · have hcardTriple :
          ({positiveAtom, zeroAtom, thirdAtom} : Finset (Fin 6)).card = 3 := by
        rw [Finset.card_insert_of_notMem
            (by simp [hatomsDistinct, Ne.symm hthirdNePositive]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hthirdNeZeroAtom]),
          Finset.card_singleton]
      omega
  have hkill : ∀ direction : Fin 6 → ℝ, direction ∈ flatSpace →
      direction thirdAtom = 0 → direction = 0 := by
    intro direction hmem hthirdZero
    obtain ⟨hflat, hsum⟩ := id hmem
    exact eq_zero_of_vanishing_of_sumZero_of_rowFlat hcomplTriple hatomsDistinct
      (Ne.symm hthirdNePositive) (Ne.symm hthirdNeZeroAtom) hrowDistinct
      (hle hmem) hthirdZero hsum (hflat partner hpartnerMem)
  have hcombinationMem :
      second thirdAtom • first - first thirdAtom • second ∈ flatSpace :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hfirstMem)
      (Submodule.smul_mem _ _ hsecondMem)
  have hcombinationThird :
      (second thirdAtom • first - first thirdAtom • second) thirdAtom = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcombinationZero : second thirdAtom • first - first thirdAtom • second = 0 :=
    hkill _ hcombinationMem hcombinationThird
  have hatPivot : second thirdAtom * first pivot = 0 := by
    have hentry := congrFun hcombinationZero pivot
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hpivotSecond,
      mul_zero, sub_zero] at hentry
    exact hentry
  have hsecondThirdZero : second thirdAtom = 0 :=
    (mul_eq_zero.mp hatPivot).resolve_right hpivotFirst
  exact hsecondNe (hkill second hsecondMem hsecondThirdZero)

/-- Five active blocks already follow when full support is known only at active blocks.
This is the interface needed for a strong-stationarity choice: inactive eigenvectors are
still required for the finite-gap part of the second-order argument, but their coordinate
support is irrelevant. -/
theorem SixThreeCrux.five_le_card_chartArgmaxFamily_of_activeFullSupport
    (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (hfull : ∀ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      ∀ blockIndex : Fin 3, tightVec selected blockIndex ≠ 0)
    (multiplier : Finset (Fin 6) → ℝ)
    (hassembly : ∀ atomIndex : Fin 6,
      ∑ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
        multiplier selected * totalEigenSquareRow tightVec selected atomIndex
          = (((6 : ℕ) : ℝ))⁻¹) :
    5 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card := by
  classical
  set family := chartArgmaxFamily (chartPointOfDesign crux.design) with hfamily
  by_contra hcontra
  obtain ⟨first, second, pivot, hfirstNe, hsecondNe, hfirstFlat, hsecondFlat,
      hpivotFirst, hpivotSecond⟩ :=
    exists_flatPair_of_card_add_one_lt
      (fun label : Fin family.card =>
        totalEigenSquareRow tightVec (family.equivFin.symm label : Finset (Fin 6)))
      (by omega)
  have hrowOf : ∀ direction : Fin 6 → ℝ,
      (∀ label : Fin family.card,
        totalEigenSquareRow tightVec (family.equivFin.symm label : Finset (Fin 6))
          ⬝ᵥ direction = 0) →
      ∀ selected ∈ family, totalEigenSquareRow tightVec selected ⬝ᵥ direction = 0 := by
    intro direction hflat selected hmem
    have hlabel := hflat (family.equivFin ⟨selected, hmem⟩)
    rwa [Equiv.symm_apply_apply] at hlabel
  have hsumOf : ∀ direction : Fin 6 → ℝ,
      (∀ selected ∈ family, totalEigenSquareRow tightVec selected ⬝ᵥ direction = 0) →
      ∑ atomIndex, direction atomIndex = 0 := fun direction hflat =>
    sum_eq_zero_of_flat_of_assemblyDiagonal (by norm_num) family
      (totalEigenSquareRow tightVec) multiplier hassembly hflat
  exact crux.false_of_flatPair_of_activeFullSupport tightVec hunit hEigen hfull
    ⟨hrowOf first hfirstFlat, hsumOf first (hrowOf first hfirstFlat)⟩
    ⟨hrowOf second hsecondFlat, hsumOf second (hrowOf second hsecondFlat)⟩
    hsecondNe hpivotFirst hpivotSecond

/-- **THE FOUR-BLOCK RESIDUAL HAS A FORCED SUPPORT LOSS.**  If exactly four triples are
active, it is impossible to choose a full-support unit least eigenvector at every active
block.  This uses strong stationarity after making precisely those choices; hence it also
covers multiple least eigenvalues and does not assume a preselected weak stationary
bundle is compatible with the second-order vectors. -/
theorem SixThreeCrux.not_forall_exists_fullSupport_activeEigenvector_of_card_eq_four
    (crux : SixThreeCrux)
    (hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4) :
    ¬ ∀ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      ∃ (hcard : selected.card = 3) (vec : Fin 3 → ℝ),
        vec ⬝ᵥ vec = 1
          ∧ (chartPointGap (chartPointOfDesign crux.design)).submatrix
              (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ vec
            = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
                (chartPointOfDesign crux.design).weight) :
                (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • vec
          ∧ ∀ blockIndex : Fin 3, vec blockIndex ≠ 0 := by
  classical
  intro hallFull
  choose activeCard activeVec hactive using hallFull
  obtain ⟨fallback, hfallbackUnit, hfallbackEigen⟩ :=
    exists_unit_chartBlockEigenvectorFamily (chartPointOfDesign crux.design)
  let tightVec : Finset (Fin 6) → (Fin 3 → ℝ) := fun selected =>
    if hmember : selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design) then
      activeVec selected hmember
    else fallback selected
  have hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1 := by
    intro selected hcard
    by_cases hmember : selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
    · have htight : tightVec selected = activeVec selected hmember := by
        unfold tightVec
        split
        · rename_i hproof
          cases Subsingleton.elim hproof hmember
          rfl
        · rename_i hnot
          exact (hnot hmember).elim
      rw [htight]
      exact (hactive selected hmember).1
    · have htight : tightVec selected = fallback selected := by
        simp only [tightVec, dif_neg hmember]
      rw [htight]
      exact hfallbackUnit selected hcard
  have hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected := by
    intro selected hcard
    by_cases hmember : selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
    · have htight : tightVec selected = activeVec selected hmember := by
        unfold tightVec
        split
        · rename_i hproof
          cases Subsingleton.elim hproof hmember
          rfl
        · rename_i hnot
          exact (hnot hmember).elim
      rw [htight]
      have hproof : hcard = activeCard selected hmember := Subsingleton.elim _ _
      cases hproof
      exact (hactive selected hmember).2.1
    · have htight : tightVec selected = fallback selected := by
        simp only [tightVec, dif_neg hmember]
      rw [htight]
      exact hfallbackEigen selected hcard
  have hfull : ∀ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      ∀ blockIndex : Fin 3, tightVec selected blockIndex ≠ 0 := by
    intro selected hmember blockIndex
    have htight : tightVec selected = activeVec selected hmember := by
      unfold tightVec
      split
      · rename_i hproof
        cases Subsingleton.elim hproof hmember
        rfl
      · rename_i hnot
        exact (hnot hmember).elim
    rw [htight]
    exact (hactive selected hmember).2.2 blockIndex
  obtain ⟨multiplier, hassembly⟩ :=
    crux.exists_multiplier_assembly_totalEigenSquareRow tightVec hunit hEigen
  have hfive := crux.five_le_card_chartArgmaxFamily_of_activeFullSupport
    tightVec hunit hEigen hfull multiplier hassembly
  omega

/-- If an eigenspace contains no full-support unit vector, then one coordinate vanishes on
the entire eigenspace.  This is the linear-subspace content hidden behind the apparent
pointwise support failure: an eigenspace cannot be covered by finitely many coordinate
hyperplanes unless it is contained in one of them. -/
theorem exists_coordinate_forall_eq_zero_of_no_fullSupport_unit_eigenvector
    {n : ℕ} (hn : 0 < n) (form : Matrix (Fin n) (Fin n) ℝ) (value : ℝ)
    (hnoFull : ¬ ∃ vec : Fin n → ℝ,
      vec ⬝ᵥ vec = 1 ∧ form *ᵥ vec = value • vec ∧ ∀ coordinate, vec coordinate ≠ 0) :
    ∃ coordinate : Fin n, ∀ vec : Fin n → ℝ,
      form *ᵥ vec = value • vec → vec coordinate = 0 := by
  classical
  let eigenSpace : Submodule ℝ (Fin n → ℝ) :=
    LinearMap.ker (form - value • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVecLin
  let coordinatePlane : Fin n → Submodule ℝ (Fin n → ℝ) := fun coordinate =>
    { carrier := {vec | vec coordinate = 0}
      zero_mem' := rfl
      add_mem' := by
        intro first second hfirst hsecond
        change (first + second) coordinate = 0
        change first coordinate = 0 at hfirst
        change second coordinate = 0 at hsecond
        simp only [Pi.add_apply]
        rw [hfirst, hsecond, add_zero]
      smul_mem' := by
        intro scale vec hvec
        change (scale • vec) coordinate = 0
        change vec coordinate = 0 at hvec
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hvec, mul_zero] }
  have hmemEigen : ∀ vec : Fin n → ℝ,
      vec ∈ eigenSpace ↔ form *ᵥ vec = value • vec := by
    intro vec
    rw [show vec ∈ eigenSpace ↔
        (form - value • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVecLin vec = 0 from Iff.rfl,
      Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    constructor
    · intro hzero
      apply sub_eq_zero.mp
      simpa only [Pi.smul_apply, smul_eq_mul] using hzero
    · intro heq
      apply sub_eq_zero.mpr
      simpa only [Pi.smul_apply, smul_eq_mul] using heq
  have hcover : ∀ vec ∈ eigenSpace, ∃ coordinate, vec ∈ coordinatePlane coordinate := by
    intro vec hvec
    by_contra hnoCoordinate
    push Not at hnoCoordinate
    have hfull : ∀ coordinate, vec coordinate ≠ 0 := by
      intro coordinate hzero
      exact hnoCoordinate coordinate hzero
    have hvecNe : vec ≠ 0 := by
      intro hzero
      have := hfull ⟨0, hn⟩
      rw [hzero, Pi.zero_apply] at this
      exact this rfl
    have hnonneg : 0 ≤ vec ⬝ᵥ vec := by
      rw [dotProduct_self_eq_sum_sq]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hpositive : 0 < vec ⬝ᵥ vec := by
      refine lt_of_le_of_ne hnonneg fun hvanish => hvecNe ?_
      have hsquares : ∑ coordinate : Fin n, vec coordinate ^ 2 = 0 := by
        rw [← dotProduct_self_eq_sum_sq, ← hvanish]
      funext coordinate
      have hentry := (Finset.sum_eq_zero_iff_of_nonneg
        (fun other _ => sq_nonneg (vec other))).mp hsquares coordinate
        (Finset.mem_univ coordinate)
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hentry
    let scale := (Real.sqrt (vec ⬝ᵥ vec))⁻¹
    have hrootPos : 0 < Real.sqrt (vec ⬝ᵥ vec) := Real.sqrt_pos.mpr hpositive
    have hscalePos : 0 < scale := inv_pos.mpr hrootPos
    have hunit : (scale • vec) ⬝ᵥ (scale • vec) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        ← mul_inv, ← pow_two, Real.sq_sqrt hnonneg]
      exact inv_mul_cancel₀ (ne_of_gt hpositive)
    have hEigen : form *ᵥ vec = value • vec := (hmemEigen vec).mp hvec
    have hscaledEigen : form *ᵥ (scale • vec) = value • (scale • vec) := by
      rw [Matrix.mulVec_smul, hEigen]
      simp only [smul_smul]
      rw [mul_comm]
    have hscaledFull : ∀ coordinate, (scale • vec) coordinate ≠ 0 := by
      intro coordinate
      simp only [Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero]
      exact not_or_intro (ne_of_gt hscalePos) (hfull coordinate)
    exact hnoFull ⟨scale • vec, hunit, hscaledEigen, hscaledFull⟩
  obtain ⟨coordinate, hcontained⟩ :=
    exists_le_of_forall_exists_mem eigenSpace coordinatePlane hcover
  refine ⟨coordinate, fun vec hEigen => ?_⟩
  exact hcontained ((hmemEigen vec).mpr hEigen)

/-- **GEOMETRIC FORM OF THE FOUR-BLOCK RESIDUAL.**  At exactly four active triples, one
active block has a least eigenspace contained in a coordinate plane.  This conclusion is
independent of any choice of eigenvector. -/
theorem SixThreeCrux.exists_active_coordinate_zero_on_tightEigenspace_of_card_eq_four
    (crux : SixThreeCrux)
    (hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4) :
    ∃ (selected : Finset (Fin 6)),
      selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design) ∧
      ∃ (hcard : selected.card = 3) (coordinate : Fin 3),
        ∀ vec : Fin 3 → ℝ,
          (chartPointGap (chartPointOfDesign crux.design)).submatrix
              (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ vec
            = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
                (chartPointOfDesign crux.design).weight) :
                (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • vec →
          vec coordinate = 0 := by
  classical
  have hno := crux.not_forall_exists_fullSupport_activeEigenvector_of_card_eq_four hfour
  push Not at hno
  obtain ⟨selected, hmember, hbad⟩ := hno
  have hcard : selected.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp hmember).1
  let form := (chartPointGap (chartPointOfDesign crux.design)).submatrix
    (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)
  let value := chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
      (chartPointOfDesign crux.design).weight) :
      (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected
  have hnoFull : ¬ ∃ vec : Fin 3 → ℝ,
      vec ⬝ᵥ vec = 1 ∧ form *ᵥ vec = value • vec ∧ ∀ coordinate, vec coordinate ≠ 0 := by
    rintro ⟨vec, hunit, hEigen, hfull⟩
    obtain ⟨coordinate, hzero⟩ := hbad hcard vec hunit hEigen
    exact hfull coordinate hzero
  obtain ⟨coordinate, hcoordinate⟩ :=
    exists_coordinate_forall_eq_zero_of_no_fullSupport_unit_eigenvector (by norm_num) form value
      hnoFull
  exact ⟨selected, hmember, hcard, coordinate, hcoordinate⟩

/-! ## The second-order containment, dualized into a row-span condition -/

/-- The standard dot-product bilinear form on a finite real coordinate space is
nondegenerate.  Keeping this algebraic avoids changing the ambient function type to an
`EuclideanSpace`. -/
theorem dotProductBilin_nondegenerate {size : ℕ} :
    (dotProductBilin ℝ ℝ : LinearMap.BilinForm ℝ (Fin size → ℝ)).Nondegenerate := by
  constructor
  · intro left hleft
    funext coordinate
    have hzero := hleft (Pi.single coordinate (1 : ℝ))
    simpa [dotProductBilin_apply_apply, dotProduct_single] using hzero
  · intro right hright
    funext coordinate
    have hzero := hright (Pi.single coordinate (1 : ℝ))
    simpa [dotProductBilin_apply_apply, single_dotProduct] using hzero

/-- The standard dot-product bilinear form is reflexive. -/
theorem dotProductBilin_isRefl {size : ℕ} :
    (dotProductBilin ℝ ℝ : LinearMap.BilinForm ℝ (Fin size → ℝ)).IsRefl := by
  intro left right hzero
  rw [dotProductBilin_apply_apply] at hzero
  rw [dotProductBilin_apply_apply, dotProduct_comm]
  exact hzero

/-- The span of a finite family of row vectors, indexed without introducing a junk row
outside the family. -/
noncomputable def finiteRowSpan {size : ℕ}
    (family : Finset (Finset (Fin size)))
    (row : Finset (Fin size) → (Fin size → ℝ)) : Submodule ℝ (Fin size → ℝ) :=
  Submodule.span ℝ (Set.range fun selected : {selected // selected ∈ family} ↦ row selected.1)

/-- **SECOND ORDER AS A ROW-SPAN CONDITION.**  The assembly diagonal makes the simplex
sum constraint redundant among the common row annihilators.  If second order says every
such direction vanishes on `block`, duality therefore puts each coordinate axis of
`block` in the span of the rows. -/
theorem coordinateSingle_mem_finiteRowSpan_of_flat_le_vanishing {size : ℕ}
    (hsize : 0 < size)
    (family : Finset (Finset (Fin size)))
    (row : Finset (Fin size) → (Fin size → ℝ))
    (multiplier : Finset (Fin size) → ℝ)
    (hassembly : ∀ atomIndex : Fin size,
      ∑ selected ∈ family, multiplier selected * row selected atomIndex = ((size : ℝ))⁻¹)
    (block : Finset (Fin size))
    (hflatLe : flatSumZeroSubmodule family row ≤ vanishingSubmodule block)
    {atomIndex : Fin size} (hatom : atomIndex ∈ block) :
    Pi.single atomIndex (1 : ℝ) ∈ finiteRowSpan family row := by
  let B : LinearMap.BilinForm ℝ (Fin size → ℝ) := dotProductBilin ℝ ℝ
  let spanRows := finiteRowSpan family row
  change Pi.single atomIndex (1 : ℝ) ∈ spanRows
  rw [← B.orthogonal_orthogonal dotProductBilin_nondegenerate dotProductBilin_isRefl spanRows]
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro direction hdirection
  have hflat : ∀ selected ∈ family, row selected ⬝ᵥ direction = 0 := by
    intro selected hselected
    exact hdirection (row selected)
      (Submodule.subset_span ⟨⟨selected, hselected⟩, rfl⟩)
  have hsum : ∑ coordinate, direction coordinate = 0 :=
    sum_eq_zero_of_flat_of_assemblyDiagonal hsize family row multiplier hassembly hflat
  have hvanish : direction ∈ vanishingSubmodule block :=
    hflatLe (⟨hflat, hsum⟩ : direction ∈ flatSumZeroSubmodule family row)
  have hcoordinate : direction atomIndex = 0 := hvanish atomIndex hatom
  simp [B, dotProductBilin_apply_apply, dotProduct_single, hcoordinate]

/-- Every card-three least eigenvector at a crux has at least two nonzero coordinates.
This is true for inactive blocks as well: every block value is bounded above by the
negative chart objective. -/
theorem SixThreeCrux.two_le_card_totalTightSupport
    (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    2 ≤ (totalTightSupport tightVec selected).card := by
  let block := (chartPointGap (chartPointOfDesign crux.design)).submatrix
    (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)
  let value := chartBlockValue 3
    (((chartPointOfDesign crux.design).chart,
        (chartPointOfDesign crux.design).weight) :
        (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected
  have hvalueLe : value ≤ chartObjective (chartPointOfDesign crux.design) :=
    Finset.le_sup'
      (f := fun candidate => chartBlockValue 3
        (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) candidate)
      ((mem_chartCandidates_iff 6 3 selected).mpr hcard)
  have hvalueNeg : value < 0 := lt_of_le_of_lt hvalueLe crux.hasNegativeChartValue
  have hdiag : ∀ coordinate, 0 < block coordinate coordinate := by
    intro coordinate
    simp only [block, Matrix.submatrix_apply, chartPointGap, chartPointOfDesign,
      Matrix.sub_apply, Matrix.diagonal_apply_eq]
    rw [projectionOfDesign_diagonal]
    have hweight := crux.design.weight_pos (selected.orderEmbOfFin hcard coordinate)
    have hexcess := allHeavy_heavyExcess_pos crux.isAllHeavy
      (selected.orderEmbOfFin hcard coordinate)
    rw [heavyExcess] at hexcess
    nlinarith
  obtain ⟨first, second, hne, hfirst, hsecond⟩ :=
    exists_two_ne_zero_of_unit_eigen_of_neg_of_pos_diagonal block (tightVec selected) value
      (hunit selected hcard) (hEigen selected hcard) hvalueNeg hdiag
  exact Gtz.two_le_card_totalTightSupport tightVec hcard hne hfirst hsecond

/-- **THE CRUX SECOND-ORDER ROW-SPAN WITNESS.**  A hypothetical crux supplies one active
block with at least two supported atoms such that every corresponding coordinate axis is
in the span of all active squared tight-eigenvector rows.  This combines strong
stationarity (the assembly diagonal) with chart second order (the flat-space
containment); neither ingredient alone implies the conclusion. -/
theorem SixThreeCrux.exists_argmax_supportTwo_coordinateSingles_mem_finiteRowSpan
    (crux : SixThreeCrux) :
    ∃ (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
      (multiplier : Finset (Fin 6) → ℝ)
      (block : Finset (Fin 6)),
      (∀ selected : Finset (Fin 6), selected.card = 3 →
        tightVec selected ⬝ᵥ tightVec selected = 1)
      ∧ (∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
        (chartPointGap (chartPointOfDesign crux.design)).submatrix
            (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
          = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
              (chartPointOfDesign crux.design).weight) :
              (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
      ∧ (∀ atomIndex : Fin 6,
        ∑ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
          multiplier selected * totalEigenSquareRow tightVec selected atomIndex
            = (((6 : ℕ) : ℝ))⁻¹)
      ∧ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
      ∧ 2 ≤ (totalTightSupport tightVec block).card
      ∧ ∀ atomIndex ∈ totalTightSupport tightVec block,
        Pi.single atomIndex (1 : ℝ) ∈ finiteRowSpan
          (chartArgmaxFamily (chartPointOfDesign crux.design))
          (totalEigenSquareRow tightVec) := by
  classical
  obtain ⟨tightVec, hunit, hEigen⟩ :=
    exists_unit_chartBlockEigenvectorFamily (chartPointOfDesign crux.design)
  obtain ⟨multiplier, hassembly⟩ :=
    crux.exists_multiplier_assembly_totalEigenSquareRow tightVec hunit hEigen
  obtain ⟨block, hblock, hflatLe⟩ :=
    crux.exists_argmax_le_vanishingSubmodule_totalTightSupport tightVec hunit hEigen
  refine ⟨tightVec, multiplier, block, hunit, hEigen, hassembly, hblock,
    crux.two_le_card_totalTightSupport tightVec hunit hEigen block ?_, ?_⟩
  · exact ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) block).mp hblock).1
  · intro atomIndex hatom
    exact coordinateSingle_mem_finiteRowSpan_of_flat_le_vanishing (by norm_num)
      (chartArgmaxFamily (chartPointOfDesign crux.design)) (totalEigenSquareRow tightVec)
      multiplier hassembly (totalTightSupport tightVec block) hflatLe hatom

end Gtz

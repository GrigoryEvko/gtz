import Gtz.Wave.GtzEFourRowSpan
import Gtz.Wave.SharedEdgeSpectralSeparation
import Gtz.Wave.GlobalZeroLeakFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset
open scoped BigOperators

/-- Restricting a unit ambient vector supported on a three-set preserves its
norm. -/
theorem dotProduct_blockRestriction_eq_one_of_unit_of_zero_off
    (block : Finset (Fin 6)) (hblockCard : block.card = 3)
    (vector : Fin 6 → ℝ) (hunit : vector ⬝ᵥ vector = 1)
    (hzero : ∀ atomIndex, atomIndex ∉ block → vector atomIndex = 0) :
    (fun blockIndex => vector (block.orderEmbOfFin hblockCard blockIndex)) ⬝ᵥ
      (fun blockIndex => vector (block.orderEmbOfFin hblockCard blockIndex)) = 1 := by
  rw [dotProduct]
  rw [dotProduct] at hunit
  have hsplit := sum_univ_eq_sum_block_add_sum_compl block
    (fun atomIndex => vector atomIndex * vector atomIndex)
  have hcomplementZero : (∑ atomIndex ∈ blockᶜ,
      vector atomIndex * vector atomIndex) = 0 := by
    exact Finset.sum_eq_zero fun atomIndex hatom => by
      rw [hzero atomIndex (Finset.mem_compl.mp hatom), zero_mul]
  rw [hsplit, hcomplementZero, add_zero] at hunit
  calc
    ∑ blockIndex : Fin 3,
        vector (block.orderEmbOfFin hblockCard blockIndex)
          * vector (block.orderEmbOfFin hblockCard blockIndex)
      = ∑ atomIndex ∈ block, vector atomIndex * vector atomIndex :=
          sum_orderEmbOfFin_eq_sum block hblockCard
            (fun atomIndex => vector atomIndex * vector atomIndex)
    _ = 1 := hunit

/-- A zero restricted cross-block image is exactly zero projection leak into
the other triple for an ambient vector supported on the complementary triple. -/
theorem projection_mulVec_eq_zero_on_block_of_cross_mulVec_eq_zero
    (projection : Matrix (Fin 6) (Fin 6) ℝ)
    (block : Finset (Fin 6)) (hblockCard : block.card = 3)
    (hcomplementCard : blockᶜ.card = 3) (vector : Fin 6 → ℝ)
    (hzeroOnBlock : ∀ atomIndex ∈ block, vector atomIndex = 0)
    (hcrossZero :
      (projection.submatrix (block.orderEmbOfFin hblockCard)
          (blockᶜ.orderEmbOfFin hcomplementCard)) *ᵥ
        (fun complementIndex =>
          vector (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) = 0) :
    ∀ atomIndex ∈ block, (projection *ᵥ vector) atomIndex = 0 := by
  classical
  intro atomIndex hatom
  let blockIndex : Fin 3 :=
    (block.orderIsoOfFin hblockCard).symm ⟨atomIndex, hatom⟩
  have hblockPick : block.orderEmbOfFin hblockCard blockIndex = atomIndex := by
    change ((block.orderIsoOfFin hblockCard) blockIndex).1 = atomIndex
    simp only [blockIndex, OrderIso.apply_symm_apply]
  have hcrossEntry := congrFun hcrossZero blockIndex
  change (∑ complementIndex : Fin 3,
      projection (block.orderEmbOfFin hblockCard blockIndex)
          (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)
        * vector (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) = 0
    at hcrossEntry
  rw [hblockPick] at hcrossEntry
  have hblockZero :
      (∑ otherIndex ∈ block,
        projection atomIndex otherIndex * vector otherIndex) = 0 := by
    exact Finset.sum_eq_zero fun otherIndex hother => by
      rw [hzeroOnBlock otherIndex hother, mul_zero]
  rw [Matrix.mulVec, dotProduct,
    sum_univ_eq_sum_block_add_sum_compl block,
    hblockZero, zero_add]
  rw [← sum_orderEmbOfFin_eq_sum blockᶜ hcomplementCard]
  exact hcrossEntry

/-- By symmetry, a zero transpose-cross image is zero projection leak out of
the selected triple for an ambient vector supported on that triple. -/
theorem projection_mulVec_eq_zero_off_block_of_transposeCross_mulVec_eq_zero
    (projection : Matrix (Fin 6) (Fin 6) ℝ)
    (block : Finset (Fin 6)) (hblockCard : block.card = 3)
    (hcomplementCard : blockᶜ.card = 3) (vector : Fin 6 → ℝ)
    (hsymmetric : projectionᵀ = projection)
    (hzeroOffBlock : ∀ atomIndex, atomIndex ∉ block → vector atomIndex = 0)
    (hcrossZero :
      (projection.submatrix (block.orderEmbOfFin hblockCard)
          (blockᶜ.orderEmbOfFin hcomplementCard)).transpose *ᵥ
        (fun blockIndex => vector (block.orderEmbOfFin hblockCard blockIndex)) = 0) :
    ∀ atomIndex, atomIndex ∉ block → (projection *ᵥ vector) atomIndex = 0 := by
  classical
  intro atomIndex hatom
  have hcomplementMem : atomIndex ∈ blockᶜ := Finset.mem_compl.mpr hatom
  let complementIndex : Fin 3 :=
    (blockᶜ.orderIsoOfFin hcomplementCard).symm ⟨atomIndex, hcomplementMem⟩
  have hcomplementPick :
      blockᶜ.orderEmbOfFin hcomplementCard complementIndex = atomIndex := by
    change ((blockᶜ.orderIsoOfFin hcomplementCard) complementIndex).1 = atomIndex
    simp only [complementIndex, OrderIso.apply_symm_apply]
  have hcrossEntry := congrFun hcrossZero complementIndex
  change (∑ blockIndex : Fin 3,
      projection (block.orderEmbOfFin hblockCard blockIndex)
          (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)
        * vector (block.orderEmbOfFin hblockCard blockIndex)) = 0 at hcrossEntry
  rw [hcomplementPick] at hcrossEntry
  have htransposeEntry : ∀ inside outside,
      projection inside outside = projection outside inside := by
    intro inside outside
    have hentry := congrFun (congrFun hsymmetric outside) inside
    simpa only [Matrix.transpose_apply] using hentry
  have hcomplementZero :
      (∑ otherIndex ∈ blockᶜ,
        projection atomIndex otherIndex * vector otherIndex) = 0 := by
    exact Finset.sum_eq_zero fun otherIndex hother => by
      rw [hzeroOffBlock otherIndex (Finset.mem_compl.mp hother), mul_zero]
  rw [Matrix.mulVec, dotProduct,
    sum_univ_eq_sum_block_add_sum_compl block,
    hcomplementZero, add_zero]
  rw [← sum_orderEmbOfFin_eq_sum block hblockCard]
  calc
    ∑ blockIndex : Fin 3,
        projection atomIndex (block.orderEmbOfFin hblockCard blockIndex)
          * vector (block.orderEmbOfFin hblockCard blockIndex)
      = ∑ blockIndex : Fin 3,
          projection (block.orderEmbOfFin hblockCard blockIndex) atomIndex
            * vector (block.orderEmbOfFin hblockCard blockIndex) := by
              apply Finset.sum_congr rfl
              intro blockIndex _
              rw [htransposeEntry]
    _ = 0 := hcrossEntry

/-- Local block tightness becomes a global zero-leak equation as soon as the
projection has no leak outside the selected support. -/
theorem shiftedGap_mulVec_eq_zero_of_isChartTightDirection_of_no_projectionLeak
    {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}
    {weight tightVec : Fin size → ℝ} {value : ℝ}
    {selected : Finset (Fin size)}
    (htight : IsChartTightDirection projection weight value selected tightVec)
    (hnoLeak : ∀ atomIndex, atomIndex ∉ selected →
      (projection *ᵥ tightVec) atomIndex = 0) :
    (chartStationaryGap projection weight
      - value • (1 : Matrix (Fin size) (Fin size) ℝ)) *ᵥ tightVec = 0 := by
  funext atomIndex
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  by_cases hmem : atomIndex ∈ selected
  · exact sub_eq_zero.mpr (htight.isTight atomIndex hmem)
  · have hsupport := htight.hasSupport atomIndex hmem
    rw [chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply,
      Matrix.mulVec_diagonal, hnoLeak atomIndex hmem, hsupport,
      mul_zero, sub_zero]
    ring

/-- Once global zero leak has pinned every nonzero coordinate to the stationary
floor, the projection annihilates the tight vector itself. -/
theorem projection_mulVec_eq_zero_of_shiftedGap_zero_of_floor_on_nonzero
    {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}
    {weight tightVec : Fin size → ℝ} {value : ℝ}
    (hzero : (chartStationaryGap projection weight
      - value • (1 : Matrix (Fin size) (Fin size) ℝ)) *ᵥ tightVec = 0)
    (hfloor : ∀ atomIndex, tightVec atomIndex ≠ 0 →
      value + weight atomIndex = 0) :
    projection *ᵥ tightVec = 0 := by
  funext atomIndex
  change (projection *ᵥ tightVec) atomIndex = 0
  have hentry := congrFun hzero atomIndex
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.sub_apply, Pi.smul_apply, chartStationaryGap, Matrix.sub_mulVec,
    Pi.sub_apply, Matrix.mulVec_diagonal, Pi.zero_apply, smul_eq_mul] at hentry
  by_cases hnonzero : tightVec atomIndex = 0
  · simpa only [hnonzero, mul_zero, sub_zero] using hentry
  · have hpinned := hfloor atomIndex hnonzero
    have hscaleZero :
        weight atomIndex * tightVec atomIndex
          + value * tightVec atomIndex = 0 := by
      rw [← add_mul, add_comm (weight atomIndex) value, hpinned, zero_mul]
    linarith

/-- **THE SHARED-EDGE RANK-TWO EXIT, in ambient chart coordinates.**  Once the
positive-support reduction identifies the selected-side assembly as one
positive full atom plus one positive pair atom, spectral separation kills both
cross leaks.  The two active directions are then globally zero-leak, pin all
six weights to the stationary floor, and violate the strict value floor. -/
theorem SixThreeCrux.false_of_sharedEdge_rankTwo_blockData
    (crux : SixThreeCrux) {activeIndex : Type*}
    (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin 6))
    (activeWeight : activeIndex → ℝ)
    (tightDir : activeIndex → (Fin 6 → ℝ))
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (block : Finset (Fin 6)) (hblockCard : block.card = 3)
    (hcomplementCard : blockᶜ.card = 3)
    (full complement : Fin 6 → ℝ) (pair : Fin 3 → ℝ)
    (fullWeight pairWeight : ℝ)
    (htightFull : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block full)
    (htightComplement : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) blockᶜ complement)
    (hfullUnit :
      (fun blockIndex => full (block.orderEmbOfFin hblockCard blockIndex)) ⬝ᵥ
        (fun blockIndex => full (block.orderEmbOfFin hblockCard blockIndex)) = 1)
    (hpairUnit : pair ⬝ᵥ pair = 1)
    (hcomplementUnit :
      (fun complementIndex =>
          complement (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) ⬝ᵥ
        (fun complementIndex =>
          complement (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) = 1)
    (missing : Fin 3)
    (hfullMissing :
      full (block.orderEmbOfFin hblockCard missing) ≠ 0)
    (hpairMissing : pair missing = 0)
    (hfullWeight : 0 < fullWeight) (hpairWeight : 0 < pairWeight)
    (hweightSum : fullWeight + pairWeight = 1 / 2)
    (hfullNonzero : ∀ atomIndex ∈ block, full atomIndex ≠ 0)
    (hcomplementNonzero : ∀ atomIndex, atomIndex ∉ block → complement atomIndex ≠ 0)
    (hassemblyLeft :
      (chartMultiplierAssembly activeSet activeWeight tightDir).submatrix
          (block.orderEmbOfFin hblockCard) (block.orderEmbOfFin hblockCard)
        = fullWeight • atomMatrix
            (fun blockIndex => full (block.orderEmbOfFin hblockCard blockIndex))
          + pairWeight • atomMatrix pair)
    (hassemblyCross : ∀ (inside : Fin 6), inside ∈ block →
      ∀ (outside : Fin 6), outside ∉ block →
        chartMultiplierAssembly activeSet activeWeight tightDir inside outside = 0
          ∧ chartMultiplierAssembly activeSet activeWeight tightDir outside inside = 0)
    (hassemblyComplement : ∀ (first : Fin 6), first ∉ block →
      ∀ (second : Fin 6), second ∉ block →
        chartMultiplierAssembly activeSet activeWeight tightDir first second =
          (1 / 2) * complement first * complement second) :
    False := by
  classical
  let projection := (chartPointOfDesign crux.design).chart
  let assembly := chartMultiplierAssembly activeSet activeWeight tightDir
  let cross := projection.submatrix (block.orderEmbOfFin hblockCard)
    (blockᶜ.orderEmbOfFin hcomplementCard)
  let fullRestricted : Fin 3 → ℝ :=
    fun blockIndex => full (block.orderEmbOfFin hblockCard blockIndex)
  let complementRestricted : Fin 3 → ℝ :=
    fun complementIndex =>
      complement (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)
  have hintertwines :
      (fullWeight • atomMatrix fullRestricted + pairWeight • atomMatrix pair) * cross
        = cross * ((1 / 2 : ℝ) • atomMatrix complementRestricted) := by
    have hlocalized := submatrix_intertwines_half_atomMatrix_of_commutes_of_blockSplit
      projection assembly block hblockCard hcomplementCard complement
      hdata.assembly_commutes hassemblyCross hassemblyComplement
    change
      (assembly.submatrix (block.orderEmbOfFin hblockCard)
          (block.orderEmbOfFin hblockCard)) * cross
        = cross * ((1 / 2 : ℝ) • atomMatrix complementRestricted) at hlocalized
    rw [hassemblyLeft] at hlocalized
    exact hlocalized
  obtain ⟨hcrossComplement, hcrossFull⟩ :=
    sharedEdge_cross_kills_complement_and_full_missingCoordinate
      fullRestricted pair complementRestricted missing cross fullWeight pairWeight
      hfullUnit hpairUnit hcomplementUnit hfullMissing hpairMissing
      hfullWeight hpairWeight hweightSum hintertwines
  have hcomplementProjectionOnBlock : ∀ atomIndex ∈ block,
      (projection *ᵥ complement) atomIndex = 0 := by
    apply projection_mulVec_eq_zero_on_block_of_cross_mulVec_eq_zero
      projection block hblockCard hcomplementCard complement
    · intro atomIndex hmem
      exact htightComplement.hasSupport atomIndex (by
        simp only [Finset.mem_compl, not_not]
        exact hmem)
    · exact hcrossComplement
  have hcomplementProjectionOff : ∀ atomIndex, atomIndex ∉ blockᶜ →
      (projection *ᵥ complement) atomIndex = 0 := by
    intro atomIndex hnotMem
    apply hcomplementProjectionOnBlock atomIndex
    simpa only [Finset.mem_compl, not_not] using hnotMem
  have hcomplementZeroLeak :=
    shiftedGap_mulVec_eq_zero_of_isChartTightDirection_of_projection_zero_off
      htightComplement hcomplementProjectionOff
  have hfullProjectionOff : ∀ atomIndex, atomIndex ∉ block →
      (projection *ᵥ full) atomIndex = 0 := by
    apply projection_mulVec_eq_zero_off_block_of_transposeCross_mulVec_eq_zero
      projection block hblockCard hcomplementCard full hdata.isSymmetric
    · exact htightFull.hasSupport
    · exact hcrossFull
  have hfullZeroLeak :=
    shiftedGap_mulVec_eq_zero_of_isChartTightDirection_of_projection_zero_off
      htightFull hfullProjectionOff
  have hpinnedComplement : ∀ atomIndex, atomIndex ∉ block →
      crux.design.weight atomIndex =
        -chartObjective (chartPointOfDesign crux.design) := by
    intro atomIndex hnotMem
    exact crux.weight_eq_neg_chartObjective_of_globalTight_nonzero
      htightComplement hcomplementZeroLeak (hcomplementNonzero atomIndex hnotMem)
  have hpinnedFull : ∀ atomIndex ∈ block,
      crux.design.weight atomIndex =
        -chartObjective (chartPointOfDesign crux.design) := by
    intro atomIndex hmem
    exact crux.weight_eq_neg_chartObjective_of_globalTight_nonzero
      htightFull hfullZeroLeak (hfullNonzero atomIndex hmem)
  have hpinnedAll : ∀ atomIndex : Fin 6,
      crux.design.weight atomIndex =
        -chartObjective (chartPointOfDesign crux.design) := by
    intro atomIndex
    by_cases hmem : atomIndex ∈ block
    · exact hpinnedFull atomIndex hmem
    · exact hpinnedComplement atomIndex hmem
  have hweightSumOne := crux.design.weight_sum_one
  rw [Fin.sum_univ_six, hpinnedAll 0, hpinnedAll 1, hpinnedAll 2,
    hpinnedAll 3, hpinnedAll 4, hpinnedAll 5] at hweightSumOne
  have hstrict := neg_inv_size_lt_value_of_isChartStationaryData
    crux.design rfl crux.isChartArgmaxValue hdata
  norm_num at hstrict
  linarith

/-- **THE POSITIVE-SUPPORT SHARED-EDGE REDUCTION.**  This is the direct
consumer of the three-member chain classification.  The positive support is
exactly `{B, Bᶜ, D}`; the `D` row has no coordinates off `B`; and one coordinate
of `B \ D` is missing from that row.  All matrix identities and multiplier
relations required by `false_of_sharedEdge_rankTwo_blockData` are derived here. -/
theorem SixThreeCrux.false_of_positiveSupport_sharedEdgeChain
    (crux : SixThreeCrux)
    (activeSet : Finset (Finset (Fin 6)))
    (multiplier : Finset (Fin 6) → ℝ)
    (selection : Finset (Fin 6) → (Fin 6 → ℝ))
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) activeSet
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier selection)
    (block mixed : Finset (Fin 6))
    (hblockCard : block.card = 3) (hcomplementCard : blockᶜ.card = 3)
    (hfamily : activeSet = {block, blockᶜ, mixed})
    (hblockNeComplement : block ≠ blockᶜ)
    (hmixedNeBlock : mixed ≠ block)
    (hmixedNeComplement : mixed ≠ blockᶜ)
    (hpositive : ∀ selected ∈ activeSet, 0 < multiplier selected)
    (hcomplementMultiplier : multiplier blockᶜ = 1 / 2)
    (hfullNonzero : ∀ atomIndex ∈ block, selection block atomIndex ≠ 0)
    (hcomplementNonzero : ∀ atomIndex, atomIndex ∉ block →
      selection blockᶜ atomIndex ≠ 0)
    (hmixedZeroOffBlock : ∀ atomIndex, atomIndex ∉ block →
      selection mixed atomIndex = 0)
    (missing : Fin 3)
    (hmissingNotMixed : block.orderEmbOfFin hblockCard missing ∉ mixed) :
    False := by
  classical
  have hblockMem : block ∈ activeSet := by
    rw [hfamily]
    simp
  have hcomplementMem : blockᶜ ∈ activeSet := by
    rw [hfamily]
    simp
  have hmixedMem : mixed ∈ activeSet := by
    rw [hfamily]
    simp
  let full := selection block
  let complement := selection blockᶜ
  let pair : Fin 3 → ℝ :=
    fun blockIndex => selection mixed (block.orderEmbOfFin hblockCard blockIndex)
  let fullWeight := multiplier block
  let pairWeight := multiplier mixed
  have htightFull : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block full := by
    exact
      { isUnit := hdata.tightDir_unit block hblockMem
        hasSupport := hdata.tightDir_support block hblockMem
        isTight := hdata.tightDir_isTight block hblockMem }
  have htightComplement : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) blockᶜ complement := by
    exact
      { isUnit := hdata.tightDir_unit blockᶜ hcomplementMem
        hasSupport := hdata.tightDir_support blockᶜ hcomplementMem
        isTight := hdata.tightDir_isTight blockᶜ hcomplementMem }
  have hfullZeroOff : ∀ atomIndex, atomIndex ∉ block → full atomIndex = 0 :=
    htightFull.hasSupport
  have hcomplementZeroOn : ∀ atomIndex ∈ block,
      complement atomIndex = 0 := by
    intro atomIndex hmem
    exact htightComplement.hasSupport atomIndex (by
      simp only [Finset.mem_compl, not_not]
      exact hmem)
  have hfullUnit :
      (fun blockIndex => full (block.orderEmbOfFin hblockCard blockIndex)) ⬝ᵥ
        (fun blockIndex => full (block.orderEmbOfFin hblockCard blockIndex)) = 1 :=
    dotProduct_blockRestriction_eq_one_of_unit_of_zero_off
      block hblockCard full htightFull.isUnit hfullZeroOff
  have hpairUnit : pair ⬝ᵥ pair = 1 := by
    exact dotProduct_blockRestriction_eq_one_of_unit_of_zero_off
      block hblockCard (selection mixed)
        (hdata.tightDir_unit mixed hmixedMem) hmixedZeroOffBlock
  have hcomplementUnit :
      (fun complementIndex =>
          complement (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) ⬝ᵥ
        (fun complementIndex =>
          complement (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) = 1 :=
    dotProduct_complementRestriction_eq_one_of_unit_of_zero_on_block
      block hcomplementCard complement htightComplement.isUnit hcomplementZeroOn
  have hfullMissing :
      full (block.orderEmbOfFin hblockCard missing) ≠ 0 :=
    hfullNonzero _ (Finset.orderEmbOfFin_mem block hblockCard missing)
  have hpairMissing : pair missing = 0 := by
    exact hdata.tightDir_support mixed hmixedMem _ hmissingNotMixed
  have hfullWeight : 0 < fullWeight := hpositive block hblockMem
  have hpairWeight : 0 < pairWeight := hpositive mixed hmixedMem
  have hblockNotRest :
      block ∉ ({blockᶜ, mixed} : Finset (Finset (Fin 6))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hblockNeComplement, Ne.symm hmixedNeBlock⟩
  have hcomplementNotMixed : blockᶜ ∉ ({mixed} : Finset (Finset (Fin 6))) := by
    simpa only [Finset.mem_singleton] using Ne.symm hmixedNeComplement
  have hweightSum : fullWeight + pairWeight = 1 / 2 := by
    have hsum := hdata.activeWeight_sum_one
    rw [hfamily] at hsum
    rw [Finset.sum_insert hblockNotRest,
      Finset.sum_insert hcomplementNotMixed, Finset.sum_singleton] at hsum
    dsimp [fullWeight, pairWeight]
    rw [hcomplementMultiplier] at hsum
    linarith
  have hassemblyLeft :
      (chartMultiplierAssembly activeSet multiplier selection).submatrix
          (block.orderEmbOfFin hblockCard) (block.orderEmbOfFin hblockCard)
        = fullWeight • atomMatrix
            (fun blockIndex => full (block.orderEmbOfFin hblockCard blockIndex))
          + pairWeight • atomMatrix pair := by
    ext firstIndex secondIndex
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
      atomMatrix, Matrix.vecMulVec_apply]
    rw [chartMultiplierAssembly_apply, hfamily,
      Finset.sum_insert hblockNotRest,
      Finset.sum_insert hcomplementNotMixed, Finset.sum_singleton]
    have hfirstMem := Finset.orderEmbOfFin_mem block hblockCard firstIndex
    have hsecondMem := Finset.orderEmbOfFin_mem block hblockCard secondIndex
    have hfirstZero := hcomplementZeroOn _ hfirstMem
    have hsecondZero := hcomplementZeroOn _ hsecondMem
    dsimp [fullWeight, pairWeight, full, pair]
    change selection blockᶜ (block.orderEmbOfFin hblockCard firstIndex) = 0 at hfirstZero
    change selection blockᶜ (block.orderEmbOfFin hblockCard secondIndex) = 0 at hsecondZero
    rw [hfirstZero, hsecondZero]
    ring
  have hassemblyCross : ∀ (inside : Fin 6), inside ∈ block →
      ∀ (outside : Fin 6), outside ∉ block →
        chartMultiplierAssembly activeSet multiplier selection inside outside = 0
          ∧ chartMultiplierAssembly activeSet multiplier selection outside inside = 0 := by
    intro inside hinside outside houtside
    have hfullOutside := hfullZeroOff outside houtside
    have hcomplementInside := hcomplementZeroOn inside hinside
    have hmixedOutside := hmixedZeroOffBlock outside houtside
    change selection block outside = 0 at hfullOutside
    change selection blockᶜ inside = 0 at hcomplementInside
    constructor <;> rw [chartMultiplierAssembly_apply, hfamily,
      Finset.sum_insert hblockNotRest,
      Finset.sum_insert hcomplementNotMixed, Finset.sum_singleton] <;>
      rw [hfullOutside, hcomplementInside, hmixedOutside] <;> ring
  have hassemblyComplement : ∀ (first : Fin 6), first ∉ block →
      ∀ (second : Fin 6), second ∉ block →
        chartMultiplierAssembly activeSet multiplier selection first second =
          (1 / 2) * complement first * complement second := by
    intro first hfirst second hsecond
    have hfullFirst := hfullZeroOff first hfirst
    have hfullSecond := hfullZeroOff second hsecond
    have hmixedFirst := hmixedZeroOffBlock first hfirst
    have hmixedSecond := hmixedZeroOffBlock second hsecond
    change selection block first = 0 at hfullFirst
    change selection block second = 0 at hfullSecond
    rw [chartMultiplierAssembly_apply, hfamily,
      Finset.sum_insert hblockNotRest,
      Finset.sum_insert hcomplementNotMixed, Finset.sum_singleton]
    rw [hfullFirst, hfullSecond, hmixedFirst, hmixedSecond,
      hcomplementMultiplier]
    ring
  exact crux.false_of_sharedEdge_rankTwo_blockData activeSet id multiplier selection
    hdata block hblockCard hcomplementCard full complement pair fullWeight pairWeight
    htightFull htightComplement hfullUnit hpairUnit hcomplementUnit missing
    hfullMissing hpairMissing hfullWeight hpairWeight hweightSum hfullNonzero
    hcomplementNonzero hassemblyLeft hassemblyCross hassemblyComplement


end Gtz

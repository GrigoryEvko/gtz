import Gtz.Wave.OuterCaptureKernelLine
import Gtz.Wave.AssemblyRankCapstone
import Gtz.Reduction.ChartAttainmentWeld

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The argmax block floor — the value is the bottom of every active block

A crux minimises the chart objective, and the objective is the maximum
over the triples of the least block eigenvalue.  Thus EVERY member of
the argmax family carries the value as the BOTTOM of its block: the
block gap dominates the value on every supported probe.  This module
names that law `Gtz.BlockFloor`, derives it for every argmax member,
and threads it through the rank spine.

**THE CONSEQUENCE FOR THE CAMPAIGN.**  The rank-four residue
`Gtz.RankFourChartNullBasisNullClosed` quantifies over every stationary
datum, thus its prover could not use the floor.  The floored residue
`Gtz.RankFourChartNullBasisNullFlooredClosed` hands the prover the floor
at every active block, and the spine still closes: the canonical datum
of a crux lives at the argmax family, where the floor is a theorem.
**The cell is now ONE floored residue plus the six upper closures.**

The floor pays immediately, in three currencies:

* **The dual domination.**  At a floored block of positive shifted
  weights the three atoms are independent, and the block dominates
  every direction of the atom space: `|e|² ≤ Σ_C (g_y ⬝ e)²/s_y`.
* **The chart-fixed liveness.**  A chart-fixed direction is alive on
  every floored block: its normal is a direction of the atom space and
  the dual domination prices it.  Thus the capture line of a rank-four
  frame meets every floored basis block.
* **The chart-null confinement.**  A chart-null direction cannot live
  inside one floored block: the floor forces three boundary atoms and
  the boundary law refuses two.

Independently of the floor, the co-singleton field kills every
chart-fixed direction of singleton support: five atoms orthogonal to
one nonzero normal refuse strict co-singleton domination.  Thus the
capture line of a rank-four frame is alive at two atoms at least.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.le_lambdaMinMat_iff_forall` — the threshold Rayleigh dictionary.
* `Gtz.BlockFloor` with
  `Gtz.SixThreeCrux.blockFloor_of_mem_chartArgmaxFamily` — **THE FLOOR
  AT EVERY ARGMAX MEMBER.**
* `Gtz.BlockFloor.shifted_le`, `Gtz.SixThreeCrux.blockFloor_embedded`,
  `Gtz.SixThreeCrux.blockFloor_atoms_independent`,
  `Gtz.SixThreeCrux.blockColumns_det_ne_zero`,
  `Gtz.SixThreeCrux.blockFloor_dual_form`,
  `Gtz.SixThreeCrux.blockFloor_chart_entry_le` — **THE BLOCK DOMINATION
  CALCULUS.**
* `Gtz.SixThreeCrux.false_of_orthogonal_off_singleton`,
  `Gtz.SixThreeCrux.false_of_chart_fixed_singleton`,
  `Gtz.SixThreeCrux.exists_second_live_of_chart_fixed`,
  `Gtz.RankFourFrame.exists_capture_line_two_live` — **THE CO-SINGLETON
  KILLS.**
* `Gtz.SixThreeCrux.chart_fixed_live_on_floored_block`,
  `Gtz.RankFourFrame.exists_capture_line_live_on_blocks` — **THE
  LIVENESS LAWS.**
* `Gtz.SixThreeCrux.chart_null_shifted_block_le`,
  `Gtz.RankFourFrame.false_of_chart_null_subset_floored_block`,
  `Gtz.RankFiveFrame.false_of_chart_null_subset_floored_block`,
  `Gtz.RankSixFrame.false_of_chart_null_subset_floored_block` — **THE
  CONFINEMENT KILLS.**
* `Gtz.RankFourChartNullBasisNullFlooredClosed`,
  `Gtz.SixThreeCrux.exists_rankFourFrame_floored`,
  `Gtz.IsSixThreeAssemblyRankExcludedFloored`,
  `Gtz.isSixThreeAssemblyRankExcludedFloored_four_of_chartNullBasisNullFloored`,
  `Gtz.gtzWeighted_six_three_of_forall_isSixThreeAssemblyRankExcludedFloored`,
  `Gtz.gtzWeighted_six_three_of_flooredResidue_of_upperClosures`,
  `Gtz.gtzWeightedAll_three_of_flooredResidue_of_upperClosures` — **THE
  FLOORED SPINE.**

## Vacuity

The matrix layers are unconditional.  Every crux-quantified statement is
vacuous if `Gtz.GtzWeighted 6 3` holds: no crux exists.
-/

namespace Gtz

open Matrix

/-! ## Layer 0 — the transfer calculus -/

section TransferCalculus

/-- The quadratic form of a design chart is the energy of the blended
atom: the chart is the square of the scaled atom rows. -/
theorem dotProduct_projectionOfDesign_mulVec_self {size rank : ℕ}
    (design : WeightedDesign size rank) (probe : Fin size → ℝ) :
    probe ⬝ᵥ (projectionOfDesign design *ᵥ probe)
      = ((scaledAtomRows design)ᵀ *ᵥ probe) ⬝ᵥ ((scaledAtomRows design)ᵀ *ᵥ probe) := by
  rw [projectionOfDesign, ← Matrix.mulVec_mulVec]
  exact (dotProduct_mulVec_transpose (scaledAtomRows design) probe
    ((scaledAtomRows design)ᵀ *ᵥ probe)).symm

/-- A sum over a finset moves through the ordered embedding of a
card-`k` finset. -/
theorem sum_finset_eq_sum_orderEmbOfFin {α : Type*} [LinearOrder α]
    {block : Finset α} {count : ℕ} (hcard : block.card = count) (value : α → ℝ) :
    ∑ member ∈ block, value member
      = ∑ index : Fin count, value (block.orderEmbOfFin hcard index) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ block hcard]
  rw [Finset.sum_map]
  rfl

/-- A supported sum over the universe is the sum over the support. -/
theorem sum_univ_eq_sum_block {size : ℕ} {block : Finset (Fin size)}
    {value : Fin size → ℝ} (hvanish : ∀ atomIndex ∉ block, value atomIndex = 0) :
    ∑ atomIndex : Fin size, value atomIndex = ∑ atomIndex ∈ block, value atomIndex :=
  (Finset.sum_subset (Finset.subset_univ block)
    fun atomIndex _ hnot => hvanish atomIndex hnot).symm

/-- **THE THRESHOLD RAYLEIGH DICTIONARY.**  A threshold sits below the
least Rayleigh value exactly when the threshold form sits below the
quadratic form at every probe. -/
theorem le_lambdaMinMat_iff_forall {blockRank : ℕ} [Nonempty (Fin blockRank)]
    (threshold : ℝ) (block : Matrix (Fin blockRank) (Fin blockRank) ℝ) :
    threshold ≤ lambdaMinMat block
      ↔ ∀ probe : EuclideanSpace ℝ (Fin blockRank),
          threshold * (probe ⬝ᵥ probe) ≤ probe ⬝ᵥ block *ᵥ probe := by
  rw [lambdaMinMat, lambdaMinCLM, le_ciInf_iff (rayleigh_bddBelow _)]
  constructor
  · intro hrayleigh probe
    rcases eq_or_ne probe 0 with rfl | hnonzero
    · simp
    · have hquotient := hrayleigh ⟨probe, hnonzero⟩
      rw [rayleigh_toEuclideanCLM_eq] at hquotient
      have hpositive : 0 < ‖probe‖ ^ 2 := by positivity
      rwa [le_div_iff₀ hpositive, euclid_norm_sq_eq_dotProduct] at hquotient
  · rintro hform ⟨probe, hnonzero⟩
    rw [rayleigh_toEuclideanCLM_eq]
    have hpositive : 0 < ‖probe‖ ^ 2 := by positivity
    rw [le_div_iff₀ hpositive, euclid_norm_sq_eq_dotProduct]
    exact hform probe

end TransferCalculus

/-! ## Layer 1 — the block floor and its argmax supply -/

section BlockFloorLayer

/-- **THE BLOCK FLOOR.**  The chart gap of the point dominates the value
form on every probe supported inside the block.  At an argmax member
this is a theorem; at a general stationary block it is a hypothesis. -/
def BlockFloor {size : ℕ} (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (value : ℝ) (block : Finset (Fin size)) : Prop :=
  ∀ probe : Fin size → ℝ, (∀ atomIndex ∉ block, probe atomIndex = 0) →
    value * (probe ⬝ᵥ probe)
      ≤ probe ⬝ᵥ (chartStationaryGap projection weight *ᵥ probe)

variable {size : ℕ}

/-- The gap form splits into the chart form minus the weighted energy. -/
theorem dotProduct_chartStationaryGap_mulVec_self
    (projection : Matrix (Fin size) (Fin size) ℝ) (weight : Fin size → ℝ)
    (probe : Fin size → ℝ) :
    probe ⬝ᵥ (chartStationaryGap projection weight *ᵥ probe)
      = probe ⬝ᵥ (projection *ᵥ probe)
        - ∑ atomIndex, weight atomIndex * probe atomIndex ^ 2 := by
  rw [chartStationaryGap, Matrix.sub_mulVec, dotProduct_sub]
  congr 1
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun atomIndex _ => by ring

/-- **THE SHIFTED READING OF THE FLOOR.**  The shifted-weight energy of
a supported probe sits below its chart form. -/
theorem BlockFloor.shifted_le {projection : Matrix (Fin size) (Fin size) ℝ}
    {weight : Fin size → ℝ} {value : ℝ} {block : Finset (Fin size)}
    (hfloor : BlockFloor projection weight value block)
    {probe : Fin size → ℝ} (hsupport : ∀ atomIndex ∉ block, probe atomIndex = 0) :
    ∑ atomIndex ∈ block, (value + weight atomIndex) * probe atomIndex ^ 2
      ≤ probe ⬝ᵥ (projection *ᵥ probe) := by
  have hkey := hfloor probe hsupport
  rw [dotProduct_chartStationaryGap_mulVec_self] at hkey
  have hdot : probe ⬝ᵥ probe = ∑ atomIndex ∈ block, probe atomIndex ^ 2 := by
    rw [dotProduct]
    rw [sum_univ_eq_sum_block (block := block)
      (value := fun atomIndex => probe atomIndex * probe atomIndex)
      (fun atomIndex hnot => by simp [hsupport atomIndex hnot])]
    exact Finset.sum_congr rfl fun atomIndex _ => by ring
  have hweight : ∑ atomIndex, weight atomIndex * probe atomIndex ^ 2
      = ∑ atomIndex ∈ block, weight atomIndex * probe atomIndex ^ 2 :=
    sum_univ_eq_sum_block fun atomIndex hnot => by simp [hsupport atomIndex hnot]
  have hsplit : ∑ atomIndex ∈ block, (value + weight atomIndex) * probe atomIndex ^ 2
      = value * (∑ atomIndex ∈ block, probe atomIndex ^ 2)
        + ∑ atomIndex ∈ block, weight atomIndex * probe atomIndex ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun atomIndex _ => by ring
  rw [hsplit]
  rw [hdot] at hkey
  linarith [hkey, hweight]

/-- **THE FLOOR AT EVERY ARGMAX MEMBER.**  Membership in the argmax
family puts the value at or below the least block eigenvalue, and the
threshold dictionary reads that as the floor. -/
theorem SixThreeCrux.blockFloor_of_mem_chartArgmaxFamily (crux : SixThreeCrux)
    {block : Finset (Fin 6)}
    (hmem : block ∈ chartArgmaxFamily (chartPointOfDesign crux.design)) :
    BlockFloor (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block := by
  classical
  obtain ⟨hcard, hvalue⟩ :=
    (mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) block).mp hmem
  rw [chartBlockValue, dif_pos hcard] at hvalue
  intro probe hsupport
  have hkey := (le_lambdaMinMat_iff_forall _ _).mp hvalue
    (WithLp.toLp 2 fun index => probe (block.orderEmbOfFin hcard index))
  have hgap : chartGapRaw (((chartPointOfDesign crux.design).chart,
        (chartPointOfDesign crux.design).weight) :
          (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ))
      = chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight := rfl
  have hkey' : chartObjective (chartPointOfDesign crux.design)
        * ((fun index => probe (block.orderEmbOfFin hcard index))
          ⬝ᵥ fun index => probe (block.orderEmbOfFin hcard index))
      ≤ (fun index => probe (block.orderEmbOfFin hcard index))
          ⬝ᵥ ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight).submatrix
                (block.orderEmbOfFin hcard) (block.orderEmbOfFin hcard)
            *ᵥ fun index => probe (block.orderEmbOfFin hcard index)) := by
    rw [← hgap]
    exact hkey
  have hleft : ((fun index => probe (block.orderEmbOfFin hcard index))
        ⬝ᵥ fun index => probe (block.orderEmbOfFin hcard index))
      = probe ⬝ᵥ probe := by
    simp only [dotProduct]
    rw [← sum_finset_eq_sum_orderEmbOfFin hcard fun atomIndex =>
      probe atomIndex * probe atomIndex]
    exact (sum_univ_eq_sum_block fun atomIndex hnot => by
      simp [hsupport atomIndex hnot]).symm
  have hinner : ∀ atomIndex : Fin 6,
      (∑ index : Fin 3, chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomIndex
            (block.orderEmbOfFin hcard index)
          * probe (block.orderEmbOfFin hcard index))
        = ∑ colIndex : Fin 6, chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomIndex colIndex
            * probe colIndex := by
    intro atomIndex
    rw [← sum_finset_eq_sum_orderEmbOfFin hcard fun colIndex =>
      chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomIndex colIndex * probe colIndex]
    exact (sum_univ_eq_sum_block fun colIndex hnot => by
      simp [hsupport colIndex hnot]).symm
  have hright : ((fun index => probe (block.orderEmbOfFin hcard index))
        ⬝ᵥ ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight).submatrix
              (block.orderEmbOfFin hcard) (block.orderEmbOfFin hcard)
          *ᵥ fun index => probe (block.orderEmbOfFin hcard index)))
      = probe ⬝ᵥ (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight *ᵥ probe) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply]
    rw [← sum_finset_eq_sum_orderEmbOfFin hcard fun atomIndex =>
      probe atomIndex * ∑ index : Fin 3,
        chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomIndex
            (block.orderEmbOfFin hcard index)
          * probe (block.orderEmbOfFin hcard index)]
    rw [show (∑ atomIndex ∈ block, probe atomIndex * ∑ index : Fin 3,
        chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomIndex
            (block.orderEmbOfFin hcard index)
          * probe (block.orderEmbOfFin hcard index))
      = ∑ atomIndex ∈ block, probe atomIndex * ∑ colIndex : Fin 6,
          chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomIndex colIndex * probe colIndex
      from Finset.sum_congr rfl fun atomIndex _ => by rw [hinner atomIndex]]
    exact (sum_univ_eq_sum_block fun atomIndex hnot => by
      simp [hsupport atomIndex hnot]).symm
  rw [hleft, hright] at hkey'
  exact hkey'

/-- The canonical datum of a crux is floored: its active set is the
argmax family and its blocks are its labels. -/
theorem SixThreeCrux.blockFloor_of_canonical (crux : SixThreeCrux)
    {block : Finset (Fin 6)}
    (hmem : block ∈ chartArgmaxFamily (chartPointOfDesign crux.design)) :
    BlockFloor (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (id block) :=
  crux.blockFloor_of_mem_chartArgmaxFamily hmem

end BlockFloorLayer

/-! ## Layer 2 — the co-singleton kills -/

section CoSingleton

/-- The quadratic form of a subset sum is the total squared reading. -/
theorem dotProduct_subsetSum_mulVec_self {sizeCount rank : ℕ}
    (design : WeightedDesign sizeCount rank) (selected : Finset (Fin sizeCount))
    (probe : Fin rank → ℝ) :
    probe ⬝ᵥ (subsetSum design selected *ᵥ probe)
      = ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ probe) ^ 2 := by
  classical
  induction selected using Finset.induction_on with
  | empty => simp [subsetSum]
  | insert atomIndex rest hnot hrec =>
      rw [subsetSum, Finset.sum_insert hnot, Matrix.add_mulVec, dotProduct_add,
        Finset.sum_insert hnot, ← subsetSum, hrec, dotProduct_atomMatrix_mulVec_self]

/-- **FIVE ORTHOGONAL ATOMS DIE.**  A nonzero normal orthogonal to every
atom off one label refuses the strict co-singleton domination: the
co-singleton form at the normal is minus its energy. -/
theorem SixThreeCrux.false_of_orthogonal_off_singleton (crux : SixThreeCrux)
    {normalVec : Fin 3 → ℝ} (hne : normalVec ≠ 0) {liveAtom : Fin 6}
    (horth : ∀ atomIndex, atomIndex ≠ liveAtom →
      crux.design.atom atomIndex ⬝ᵥ normalVec = 0) : False := by
  classical
  have hposDef := crux.hasStrictlyDominatingCoSingletons liveAtom
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 (x := normalVec) hne
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    dotProduct_subsetSum_mulVec_self] at hform
  have hzero : ∑ atomIndex ∈ ({liveAtom}ᶜ : Finset (Fin 6)),
      (crux.design.atom atomIndex ⬝ᵥ normalVec) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun atomIndex hmem => ?_
    rw [horth atomIndex (by simpa using hmem)]
    ring
  rw [hzero] at hform
  have henergy : 0 ≤ normalVec ⬝ᵥ normalVec :=
    Finset.sum_nonneg fun coord _ => mul_self_nonneg _
  linarith

/-- **A CHART-FIXED SINGLETON DIES.**  A chart-fixed direction of
singleton support hands the coplanarity reading a normal orthogonal to
the five other atoms, and the co-singleton field refuses it. -/
theorem SixThreeCrux.false_of_chart_fixed_singleton (crux : SixThreeCrux)
    {fixedVec : Fin 6 → ℝ} (hne : fixedVec ≠ 0) {liveAtom : Fin 6}
    (hsupport : ∀ atomIndex, atomIndex ≠ liveAtom → fixedVec atomIndex = 0)
    (hfix : (chartPointOfDesign crux.design).chart *ᵥ fixedVec = fixedVec) : False := by
  obtain ⟨normalVec, hnormalNe, hnormal⟩ := crux.exists_orthogonal_of_chart_fixed hne hfix
  exact crux.false_of_orthogonal_off_singleton hnormalNe
    fun atomIndex hindex => hnormal atomIndex (hsupport atomIndex hindex)

/-- **A CHART-FIXED DIRECTION IS ALIVE AT TWO ATOMS.** -/
theorem SixThreeCrux.exists_second_live_of_chart_fixed (crux : SixThreeCrux)
    {fixedVec : Fin 6 → ℝ} (hne : fixedVec ≠ 0)
    (hfix : (chartPointOfDesign crux.design).chart *ᵥ fixedVec = fixedVec) :
    ∃ atomOne atomTwo : Fin 6, atomOne ≠ atomTwo
      ∧ fixedVec atomOne ≠ 0 ∧ fixedVec atomTwo ≠ 0 := by
  classical
  obtain ⟨liveAtom, hlive⟩ := Function.ne_iff.mp hne
  by_cases hsecond : ∃ other : Fin 6, other ≠ liveAtom ∧ fixedVec other ≠ 0
  · obtain ⟨other, hneq, hother⟩ := hsecond
    exact ⟨other, liveAtom, hneq, hother, hlive⟩
  · push Not at hsecond
    exact absurd (crux.false_of_chart_fixed_singleton hne (liveAtom := liveAtom)
      (fun atomIndex hindex => hsecond atomIndex hindex) hfix) not_false

/-- **THE CAPTURE LINE IS ALIVE AT TWO ATOMS.**  The residue line of a
rank-four frame is chart-fixed and nonzero, thus the co-singleton kill
gives it a second live atom. -/
theorem RankFourFrame.exists_capture_line_two_live {crux : SixThreeCrux}
    (frame : RankFourFrame crux) :
    ∃ lineVec : Fin 6 → ℝ, lineVec ≠ 0
      ∧ frame.lineResidue *ᵥ lineVec = lineVec
      ∧ (∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) ⬝ᵥ lineVec = 0)
      ∧ (chartPointOfDesign crux.design).chart *ᵥ lineVec = lineVec
      ∧ ∃ atomOne atomTwo : Fin 6, atomOne ≠ atomTwo
          ∧ lineVec atomOne ≠ 0 ∧ lineVec atomTwo ≠ 0 := by
  obtain ⟨lineVec, hne, hfixResidue, hbasis, hfixChart⟩ := frame.exists_capture_line
  exact ⟨lineVec, hne, hfixResidue, hbasis, hfixChart,
    crux.exists_second_live_of_chart_fixed hne hfixChart⟩

end CoSingleton

/-! ## Layer 3 — the embedded block calculus -/

section EmbeddedBlock

/-- The lift of a block coefficient vector to the atom space. -/
noncomputable def blockLift {count size : ℕ} (emb : Fin count → Fin size)
    (coeffVec : Fin count → ℝ) : Fin size → ℝ :=
  fun atomIndex => ∑ index, if atomIndex = emb index then coeffVec index else 0

/-- The lift vanishes off the range of the embedding. -/
theorem blockLift_off {count size : ℕ} {emb : Fin count → Fin size}
    {block : Finset (Fin size)} (hmem : ∀ index, emb index ∈ block)
    (coeffVec : Fin count → ℝ) {atomIndex : Fin size} (hnot : atomIndex ∉ block) :
    blockLift emb coeffVec atomIndex = 0 := by
  refine Finset.sum_eq_zero fun index _ => ?_
  rw [if_neg]
  intro hcontra
  exact hnot (hcontra ▸ hmem index)

/-- The lift reads the coefficient at the embedded index. -/
theorem blockLift_apply {count size : ℕ} {emb : Fin count → Fin size}
    (hinj : Function.Injective emb) (coeffVec : Fin count → ℝ) (index : Fin count) :
    blockLift emb coeffVec (emb index) = coeffVec index := by
  classical
  rw [blockLift, Finset.sum_eq_single index
    (fun other _ hne => if_neg fun hcontra => hne (hinj hcontra).symm)
    (fun hcontra => absurd (Finset.mem_univ index) hcontra)]
  rw [if_pos rfl]

/-- The three scaled block atoms as the columns of one square matrix. -/
noncomputable def blockColumns (design : WeightedDesign 6 3)
    {block : Finset (Fin 6)} (hcard : block.card = 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun coord index => scaledAtomRows design (block.orderEmbOfFin hcard index) coord

variable {crux : SixThreeCrux} {block : Finset (Fin 6)}

/-- The lifted probe blends to the block columns. -/
theorem transpose_scaledAtomRows_mulVec_blockLift (hcard : block.card = 3)
    (coeffVec : Fin 3 → ℝ) :
    (scaledAtomRows crux.design)ᵀ *ᵥ blockLift (block.orderEmbOfFin hcard) coeffVec
      = blockColumns crux.design hcard *ᵥ coeffVec := by
  funext coord
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, blockColumns,
    Matrix.of_apply]
  rw [sum_univ_eq_sum_block (block := block) (value := fun atomIndex =>
      scaledAtomRows crux.design atomIndex coord
        * blockLift (block.orderEmbOfFin hcard) coeffVec atomIndex)
    (fun atomIndex hnot => by
      rw [blockLift_off (fun index => Finset.orderEmbOfFin_mem block hcard index)
        coeffVec hnot, mul_zero]),
    sum_finset_eq_sum_orderEmbOfFin hcard]
  exact Finset.sum_congr rfl fun index _ => by
    rw [blockLift_apply (block.orderEmbOfFin hcard).injective coeffVec index]

/-- **THE EMBEDDED FLOOR.**  The floor of a block reads on block
coefficients: the shifted energy of a coefficient vector sits below the
energy of its atom blend. -/
theorem SixThreeCrux.blockFloor_embedded (crux : SixThreeCrux) (hcard : block.card = 3)
    (hfloor : BlockFloor (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block)
    (coeffVec : Fin 3 → ℝ) :
    ∑ index, (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight (block.orderEmbOfFin hcard index))
          * coeffVec index ^ 2
      ≤ (blockColumns crux.design hcard *ᵥ coeffVec)
          ⬝ᵥ (blockColumns crux.design hcard *ᵥ coeffVec) := by
  have hshift := hfloor.shifted_le (probe := blockLift (block.orderEmbOfFin hcard) coeffVec)
    fun atomIndex hnot =>
      blockLift_off (fun index => Finset.orderEmbOfFin_mem block hcard index) coeffVec hnot
  have hchart : blockLift (block.orderEmbOfFin hcard) coeffVec
        ⬝ᵥ ((chartPointOfDesign crux.design).chart
          *ᵥ blockLift (block.orderEmbOfFin hcard) coeffVec)
      = (blockColumns crux.design hcard *ᵥ coeffVec)
          ⬝ᵥ (blockColumns crux.design hcard *ᵥ coeffVec) := by
    rw [show (chartPointOfDesign crux.design).chart = projectionOfDesign crux.design
        from rfl,
      dotProduct_projectionOfDesign_mulVec_self,
      transpose_scaledAtomRows_mulVec_blockLift hcard]
  have hmass : ∑ atomIndex ∈ block,
        (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
            * blockLift (block.orderEmbOfFin hcard) coeffVec atomIndex ^ 2
      = ∑ index, (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight (block.orderEmbOfFin hcard index))
            * coeffVec index ^ 2 := by
    rw [sum_finset_eq_sum_orderEmbOfFin hcard]
    exact Finset.sum_congr rfl fun index _ => by
      rw [blockLift_apply (block.orderEmbOfFin hcard).injective coeffVec index]
  rw [hchart, hmass] at hshift
  exact hshift

/-- **THE FLOORED BLOCK ATOMS ARE INDEPENDENT.**  A vanishing blend of
positive shifted weights collapses its coefficients. -/
theorem SixThreeCrux.blockFloor_coeff_eq_zero (crux : SixThreeCrux) (hcard : block.card = 3)
    (hfloor : BlockFloor (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block)
    (hscale : ∀ atomIndex ∈ block, 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex)
    {coeffVec : Fin 3 → ℝ}
    (hblend : blockColumns crux.design hcard *ᵥ coeffVec = 0) :
    coeffVec = 0 := by
  have hkey := crux.blockFloor_embedded hcard hfloor coeffVec
  rw [hblend] at hkey
  simp only [dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hkey
  have hterms : ∀ index ∈ (Finset.univ : Finset (Fin 3)),
      0 ≤ (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight (block.orderEmbOfFin hcard index))
          * coeffVec index ^ 2 := fun index _ =>
    mul_nonneg (hscale _ (Finset.orderEmbOfFin_mem block hcard index)).le (sq_nonneg _)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp (le_antisymm hkey
    (Finset.sum_nonneg hterms))
  funext index
  have hentry := hall index (Finset.mem_univ index)
  rcases mul_eq_zero.mp hentry with hleft | hright
  · exact absurd hleft
      (ne_of_gt (hscale _ (Finset.orderEmbOfFin_mem block hcard index)))
  · simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hright

/-- The determinant of the floored block columns is nonzero. -/
theorem SixThreeCrux.blockColumns_det_ne_zero (crux : SixThreeCrux) (hcard : block.card = 3)
    (hfloor : BlockFloor (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block)
    (hscale : ∀ atomIndex ∈ block, 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex) :
    (blockColumns crux.design hcard).det ≠ 0 := by
  intro hdet
  obtain ⟨coeffVec, hne, hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hne (crux.blockFloor_coeff_eq_zero hcard hfloor hscale hkernel)

/-- **THE DUAL DOMINATION.**  A floored block of positive shifted
weights dominates every direction of the atom space: the direction's
energy sits below the block's inverse-scaled squared readings.  The
engine is the solvability of the block columns plus one Cauchy–Schwarz.
-/
theorem SixThreeCrux.blockFloor_dual_form (crux : SixThreeCrux) (hcard : block.card = 3)
    (hfloor : BlockFloor (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block)
    (hscale : ∀ atomIndex ∈ block, 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex)
    (direction : Fin 3 → ℝ) :
    direction ⬝ᵥ direction
      ≤ ∑ atomIndex ∈ block, (scaledAtomRows crux.design atomIndex ⬝ᵥ direction) ^ 2
          / (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex) := by
  classical
  have henergyNonneg : 0 ≤ direction ⬝ᵥ direction :=
    Finset.sum_nonneg fun coord _ => mul_self_nonneg _
  have hrhsNonneg : 0 ≤ ∑ index : Fin 3,
      (scaledAtomRows crux.design (block.orderEmbOfFin hcard index) ⬝ᵥ direction) ^ 2
        / (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight (block.orderEmbOfFin hcard index)) :=
    Finset.sum_nonneg fun index _ => div_nonneg (sq_nonneg _)
      (hscale _ (Finset.orderEmbOfFin_mem block hcard index)).le
  rw [sum_finset_eq_sum_orderEmbOfFin hcard fun atomIndex =>
    (scaledAtomRows crux.design atomIndex ⬝ᵥ direction) ^ 2
      / (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)]
  rcases eq_or_lt_of_le henergyNonneg with hzero | hpos
  · linarith
  have hdet := crux.blockColumns_det_ne_zero hcard hfloor hscale
  obtain ⟨coeffVec, hsolve⟩ : ∃ coeffVec : Fin 3 → ℝ,
      blockColumns crux.design hcard *ᵥ coeffVec = direction :=
    ⟨(blockColumns crux.design hcard)⁻¹ *ᵥ direction, by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
        Matrix.one_mulVec]⟩
  have hread : direction ⬝ᵥ (blockColumns crux.design hcard *ᵥ coeffVec)
      = ∑ index : Fin 3, coeffVec index
          * (scaledAtomRows crux.design (block.orderEmbOfFin hcard index) ⬝ᵥ direction) := by
    simp only [dotProduct, Matrix.mulVec, blockColumns, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun index _ => Finset.sum_congr rfl fun coord _ => by ring
  rw [hsolve] at hread
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
    (fun index => Real.sqrt (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight (block.orderEmbOfFin hcard index))
      * coeffVec index)
    (fun index =>
      (scaledAtomRows crux.design (block.orderEmbOfFin hcard index) ⬝ᵥ direction)
        / Real.sqrt (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight (block.orderEmbOfFin hcard index)))
  have hproduct : ∀ index : Fin 3,
      Real.sqrt (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight (block.orderEmbOfFin hcard index))
          * coeffVec index
          * ((scaledAtomRows crux.design (block.orderEmbOfFin hcard index) ⬝ᵥ direction)
            / Real.sqrt (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight (block.orderEmbOfFin hcard index)))
        = coeffVec index
          * (scaledAtomRows crux.design (block.orderEmbOfFin hcard index) ⬝ᵥ direction) := by
    intro index
    have hsqrt : Real.sqrt (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight (block.orderEmbOfFin hcard index)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (hscale _ (Finset.orderEmbOfFin_mem block hcard index)))
    field_simp
  have hsquareLeft : ∀ index : Fin 3,
      (Real.sqrt (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight (block.orderEmbOfFin hcard index))
          * coeffVec index) ^ 2
        = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight (block.orderEmbOfFin hcard index))
          * coeffVec index ^ 2 := by
    intro index
    rw [mul_pow, Real.sq_sqrt (hscale _ (Finset.orderEmbOfFin_mem block hcard index)).le]
  have hsquareRight : ∀ index : Fin 3,
      ((scaledAtomRows crux.design (block.orderEmbOfFin hcard index) ⬝ᵥ direction)
          / Real.sqrt (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight
              (block.orderEmbOfFin hcard index))) ^ 2
        = (scaledAtomRows crux.design (block.orderEmbOfFin hcard index) ⬝ᵥ direction) ^ 2
            / (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight
                (block.orderEmbOfFin hcard index)) := by
    intro index
    rw [div_pow, Real.sq_sqrt (hscale _ (Finset.orderEmbOfFin_mem block hcard index)).le]
  rw [Finset.sum_congr rfl fun index _ => hproduct index] at hcauchy
  rw [Finset.sum_congr rfl fun index _ => hsquareLeft index] at hcauchy
  rw [Finset.sum_congr rfl fun index _ => hsquareRight index] at hcauchy
  have hfloorRead := crux.blockFloor_embedded hcard hfloor coeffVec
  rw [hsolve] at hfloorRead
  rw [← hread] at hcauchy
  nlinarith [hcauchy, hfloorRead, hpos, hrhsNonneg]

/-- **THE CHART ENTRY LAW.**  The chart diagonal at any atom sits below
the inverse-scaled squared chart entries into a floored block. -/
theorem SixThreeCrux.blockFloor_chart_entry_le (crux : SixThreeCrux) (hcard : block.card = 3)
    (hfloor : BlockFloor (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block)
    (hscale : ∀ atomIndex ∈ block, 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex)
    (probeAtom : Fin 6) :
    (chartPointOfDesign crux.design).chart probeAtom probeAtom
      ≤ ∑ atomIndex ∈ block, (chartPointOfDesign crux.design).chart atomIndex probeAtom ^ 2
          / (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex) := by
  have hentry : ∀ rowIndex colIndex : Fin 6,
      (chartPointOfDesign crux.design).chart rowIndex colIndex
        = scaledAtomRows crux.design rowIndex ⬝ᵥ scaledAtomRows crux.design colIndex := by
    intro rowIndex colIndex
    show projectionOfDesign crux.design rowIndex colIndex = _
    rw [projectionOfDesign, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun coord _ => by rw [Matrix.transpose_apply]
  have hkey := crux.blockFloor_dual_form hcard hfloor hscale
    (scaledAtomRows crux.design probeAtom)
  rw [← hentry probeAtom probeAtom] at hkey
  refine hkey.trans (le_of_eq (Finset.sum_congr rfl fun atomIndex _ => ?_))
  rw [hentry atomIndex probeAtom]

end EmbeddedBlock

/-! ## Layer 4 — the liveness and confinement laws -/

section LivenessConfinement

variable {crux : SixThreeCrux} {block : Finset (Fin 6)}

/-- **A CHART-FIXED DIRECTION IS ALIVE ON EVERY FLOORED BLOCK.**  The
fixed direction is the blend of its own normal, every block reading of
that normal is a coordinate of the fixed direction, and the dual
domination refuses a dead block. -/
theorem SixThreeCrux.chart_fixed_live_on_floored_block (crux : SixThreeCrux)
    (hcard : block.card = 3)
    (hfloor : BlockFloor (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block)
    (hscale : ∀ atomIndex ∈ block, 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex)
    {fixedVec : Fin 6 → ℝ} (hne : fixedVec ≠ 0)
    (hfix : (chartPointOfDesign crux.design).chart *ᵥ fixedVec = fixedVec) :
    ∃ atomIndex ∈ block, fixedVec atomIndex ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hrecover : scaledAtomRows crux.design
      *ᵥ ((scaledAtomRows crux.design)ᵀ *ᵥ fixedVec) = fixedVec := by
    rw [Matrix.mulVec_mulVec]
    exact hfix
  have hnormalNe : (scaledAtomRows crux.design)ᵀ *ᵥ fixedVec ≠ 0 := by
    intro hcontra
    rw [hcontra, Matrix.mulVec_zero] at hrecover
    exact hne hrecover.symm
  have hreading : ∀ atomIndex : Fin 6,
      scaledAtomRows crux.design atomIndex
          ⬝ᵥ ((scaledAtomRows crux.design)ᵀ *ᵥ fixedVec)
        = fixedVec atomIndex := by
    intro atomIndex
    exact congrFun hrecover atomIndex
  have hdual := crux.blockFloor_dual_form hcard hfloor hscale
    ((scaledAtomRows crux.design)ᵀ *ᵥ fixedVec)
  have hdead : ∑ atomIndex ∈ block,
      (scaledAtomRows crux.design atomIndex
          ⬝ᵥ ((scaledAtomRows crux.design)ᵀ *ᵥ fixedVec)) ^ 2
        / (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex) = 0 := by
    refine Finset.sum_eq_zero fun atomIndex hmem => ?_
    rw [hreading atomIndex, hnone atomIndex hmem]
    simp
  rw [hdead] at hdual
  have henergy : 0 < ((scaledAtomRows crux.design)ᵀ *ᵥ fixedVec)
      ⬝ᵥ ((scaledAtomRows crux.design)ᵀ *ᵥ fixedVec) := by
    rcases Function.ne_iff.mp hnormalNe with ⟨coord, hcoord⟩
    exact Finset.sum_pos' (fun other _ => mul_self_nonneg _)
      ⟨coord, Finset.mem_univ coord, mul_self_pos.mpr (by simpa using hcoord)⟩
  linarith

/-- **THE CAPTURE LINE MEETS EVERY FLOORED BASIS BLOCK.** -/
theorem RankFourFrame.exists_capture_line_live_on_blocks (frame : RankFourFrame crux)
    (hfloors : ∀ slot : Fin 4, BlockFloor (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (frame.activeSubset (frame.basisLabel slot)))
    (hscales : ∀ slot : Fin 4,
      ∀ atomIndex ∈ frame.activeSubset (frame.basisLabel slot),
        0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex) :
    ∃ lineVec : Fin 6 → ℝ, lineVec ≠ 0
      ∧ (∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) ⬝ᵥ lineVec = 0)
      ∧ (chartPointOfDesign crux.design).chart *ᵥ lineVec = lineVec
      ∧ ∀ slot : Fin 4,
          ∃ atomIndex ∈ frame.activeSubset (frame.basisLabel slot),
            lineVec atomIndex ≠ 0 := by
  obtain ⟨lineVec, hne, _, hbasis, hfixChart⟩ := frame.exists_capture_line
  refine ⟨lineVec, hne, hbasis, hfixChart, fun slot => ?_⟩
  exact crux.chart_fixed_live_on_floored_block
    (frame.hdata.activeSubset_card (frame.basisLabel slot) (frame.hmemAll slot))
    (hfloors slot) (hscales slot) hne hfixChart

/-- **THE CONFINEMENT BOUND.**  The shifted energy of a chart-null
direction inside a floored block is nonpositive on the block's own
coordinates once the direction is supported there. -/
theorem SixThreeCrux.chart_null_shifted_block_le (crux : SixThreeCrux)
    (hfloor : BlockFloor (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block)
    {nullVec : Fin 6 → ℝ}
    (hsubset : ∀ atomIndex ∉ block, nullVec atomIndex = 0)
    (hnull : (chartPointOfDesign crux.design).chart *ᵥ nullVec = 0) :
    ∑ atomIndex ∈ block, (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
          * nullVec atomIndex ^ 2 ≤ 0 := by
  have hkey := hfloor.shifted_le hsubset
  rw [hnull] at hkey
  simpa using hkey

/-- **A CHART-NULL DIRECTION CANNOT LIVE INSIDE A FLOORED BLOCK** at a
rank-four frame: the floor forces every live atom to the boundary, the
three-live law supplies two of them, and the boundary law refuses the
pair. -/
theorem RankFourFrame.false_of_chart_null_subset_floored_block (frame : RankFourFrame crux)
    (hfloor : BlockFloor (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block)
    {nullVec : Fin 6 → ℝ} (hne : nullVec ≠ 0)
    (hsubset : ∀ atomIndex ∉ block, nullVec atomIndex = 0)
    (hnull : (chartPointOfDesign crux.design).chart *ᵥ nullVec = 0) : False := by
  classical
  have hmass := crux.chart_null_shifted_block_le hfloor hsubset hnull
  have hterms : ∀ atomIndex ∈ block,
      0 ≤ (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
          * nullVec atomIndex ^ 2 := fun atomIndex _ =>
    mul_nonneg (crux.shifted_weight_nonneg atomIndex) (sq_nonneg _)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp
    (le_antisymm hmass (Finset.sum_nonneg hterms))
  have hboundary : ∀ atomIndex : Fin 6, nullVec atomIndex ≠ 0 →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0 := by
    intro atomIndex hlive
    have hmem : atomIndex ∈ block := by
      by_contra hnot
      exact hlive (hsubset atomIndex hnot)
    have hentry := hall atomIndex hmem
    rcases mul_eq_zero.mp hentry with hleft | hright
    · exact hleft
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hright) hlive
  obtain ⟨atomOne, atomTwo, _, hneOneTwo, _, _, hliveOne, hliveTwo, _⟩ :=
    crux.exists_three_live_of_chart_null hne hnull
  exact crux.false_of_two_boundary_atoms frame.hdata frame.hspan frame.hrepresentation
    frame.hleft (le_of_eq frame.htrace.symm) hneOneTwo
    (hboundary atomOne hliveOne) (hboundary atomTwo hliveTwo)

/-- The rank-five reading of the confinement kill. -/
theorem RankFiveFrame.false_of_chart_null_subset_floored_block (frame : RankFiveFrame crux)
    (hfloor : BlockFloor (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block)
    {nullVec : Fin 6 → ℝ} (hne : nullVec ≠ 0)
    (hsubset : ∀ atomIndex ∉ block, nullVec atomIndex = 0)
    (hnull : (chartPointOfDesign crux.design).chart *ᵥ nullVec = 0) : False := by
  classical
  have hmass := crux.chart_null_shifted_block_le hfloor hsubset hnull
  have hterms : ∀ atomIndex ∈ block,
      0 ≤ (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
          * nullVec atomIndex ^ 2 := fun atomIndex _ =>
    mul_nonneg (crux.shifted_weight_nonneg atomIndex) (sq_nonneg _)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp
    (le_antisymm hmass (Finset.sum_nonneg hterms))
  have hboundary : ∀ atomIndex : Fin 6, nullVec atomIndex ≠ 0 →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0 := by
    intro atomIndex hlive
    have hmem : atomIndex ∈ block := by
      by_contra hnot
      exact hlive (hsubset atomIndex hnot)
    have hentry := hall atomIndex hmem
    rcases mul_eq_zero.mp hentry with hleft | hright
    · exact hleft
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hright) hlive
  obtain ⟨atomOne, atomTwo, _, hneOneTwo, _, _, hliveOne, hliveTwo, _⟩ :=
    crux.exists_three_live_of_chart_null hne hnull
  have htraceFloor : (2 : ℝ) ≤ Matrix.trace frame.coeff := by
    rcases frame.htrace with htwo | hthree
    · exact le_of_eq htwo.symm
    · rw [hthree]; norm_num
  exact crux.false_of_two_boundary_atoms frame.hdata frame.hspan frame.hrepresentation
    frame.hleft htraceFloor hneOneTwo
    (hboundary atomOne hliveOne) (hboundary atomTwo hliveTwo)

/-- The rank-six reading of the confinement kill. -/
theorem RankSixFrame.false_of_chart_null_subset_floored_block (frame : RankSixFrame crux)
    (hfloor : BlockFloor (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block)
    {nullVec : Fin 6 → ℝ} (hne : nullVec ≠ 0)
    (hsubset : ∀ atomIndex ∉ block, nullVec atomIndex = 0)
    (hnull : (chartPointOfDesign crux.design).chart *ᵥ nullVec = 0) : False := by
  classical
  have hmass := crux.chart_null_shifted_block_le hfloor hsubset hnull
  have hterms : ∀ atomIndex ∈ block,
      0 ≤ (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
          * nullVec atomIndex ^ 2 := fun atomIndex _ =>
    mul_nonneg (crux.shifted_weight_nonneg atomIndex) (sq_nonneg _)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp
    (le_antisymm hmass (Finset.sum_nonneg hterms))
  have hboundary : ∀ atomIndex : Fin 6, nullVec atomIndex ≠ 0 →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0 := by
    intro atomIndex hlive
    have hmem : atomIndex ∈ block := by
      by_contra hnot
      exact hlive (hsubset atomIndex hnot)
    have hentry := hall atomIndex hmem
    rcases mul_eq_zero.mp hentry with hleft | hright
    · exact hleft
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hright) hlive
  obtain ⟨atomOne, atomTwo, _, hneOneTwo, _, _, hliveOne, hliveTwo, _⟩ :=
    crux.exists_three_live_of_chart_null hne hnull
  have htraceFloor : (2 : ℝ) ≤ Matrix.trace frame.coeff := by
    rw [frame.htrace]; norm_num
  exact crux.false_of_two_boundary_atoms frame.hdata frame.hspan frame.hrepresentation
    frame.hleft htraceFloor hneOneTwo
    (hboundary atomOne hliveOne) (hboundary atomTwo hliveTwo)

end LivenessConfinement

/-! ## Layer 5 — the floored residue and the floored spine -/

section FlooredSpine

/-- **THE FLOORED CHART NULL BASIS NULL RESIDUE.**  The rank-four
residue, with the argmax floor handed to the prover at every active
block of the frame. -/
def RankFourChartNullBasisNullFlooredClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankFourFrame crux),
    (∀ activeLabel ∈ frame.activeSet,
      BlockFloor (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design))
        (frame.activeSubset activeLabel)) →
    ∀ nullVec : Fin 6 → ℝ, nullVec ≠ 0 →
    (∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) ⬝ᵥ nullVec = 0) →
    (chartPointOfDesign crux.design).chart *ᵥ nullVec = 0 →
    False

/-- The unfloored residue closes the floored one. -/
theorem rankFourChartNullBasisNullFlooredClosed_of_closed
    (hclosed : RankFourChartNullBasisNullClosed) :
    RankFourChartNullBasisNullFlooredClosed :=
  fun crux frame _ nullVec hne hbasis hchart =>
    hclosed crux frame nullVec hne hbasis hchart

/-- **THE FLOORED FRAME EXTRACTION.**  A floored rank-four datum yields
a frame whose active blocks carry the floor: the frame construction
keeps the datum's label type, active set and blocks. -/
theorem SixThreeCrux.exists_rankFourFrame_floored (crux : SixThreeCrux)
    {activeIndex : Type} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (hfloored : ∀ activeLabel ∈ activeSet,
      BlockFloor (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design))
        (activeSubset activeLabel))
    (hrankFour : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir))) = 4) :
    ∃ frame : RankFourFrame crux,
      ∀ activeLabel ∈ frame.activeSet,
        BlockFloor (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design))
          (frame.activeSubset activeLabel) := by
  obtain ⟨reducedWeight, basisLabel, leftInv, coeff, gram, hreducedData,
    _hassemblyEq, hinjective, hmem, hspan, hleft, hrepresentation,
    hidempotent, hHform, hsymmH, hpsd, hker, hexchange, htrace, _htrichotomy⟩ :=
    crux.exists_rankFour_pinned_dispatch hdata hrankFour
  exact ⟨⟨activeIndex, activeSet, activeSubset, reducedWeight, tightDir,
    basisLabel, leftInv, coeff, gram, hreducedData, hinjective, hmem, hspan,
    hleft, hrepresentation, hidempotent, hHform, hsymmH, hpsd, hker,
    hexchange, htrace⟩, hfloored⟩

/-- **THE FLOORED RUNG PROPOSITION.**  The assembly-rank exclusion with
the floor supplied at every active block. -/
def IsSixThreeAssemblyRankExcludedFloored (assemblyRank : ℕ) : Prop :=
  ∀ (crux : SixThreeCrux) (activeIndex : Type) (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin 6)) (activeWeight : activeIndex → ℝ)
    (tightDir : activeIndex → Fin 6 → ℝ),
    IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir →
    (∀ activeLabel ∈ activeSet,
      BlockFloor (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design))
        (activeSubset activeLabel)) →
    Module.finrank ℝ (LinearMap.range (Matrix.toLin'
      (chartMultiplierAssembly activeSet activeWeight tightDir))) ≠ assemblyRank

/-- The unfloored rung closes the floored one. -/
theorem isSixThreeAssemblyRankExcludedFloored_of_excluded (assemblyRank : ℕ)
    (hexcluded : IsSixThreeAssemblyRankExcluded assemblyRank) :
    IsSixThreeAssemblyRankExcludedFloored assemblyRank :=
  fun crux activeIndex activeSet activeSubset activeWeight tightDir hdata _ =>
    hexcluded crux activeIndex activeSet activeSubset activeWeight tightDir hdata

/-- **THE FLOORED RANK-FOUR RUNG FROM THE FLOORED RESIDUE.** -/
theorem isSixThreeAssemblyRankExcludedFloored_four_of_chartNullBasisNullFloored
    (hclosed : RankFourChartNullBasisNullFlooredClosed) :
    IsSixThreeAssemblyRankExcludedFloored 4 := by
  intro crux activeIndex activeSet activeSubset activeWeight tightDir hdata hfloored
    hrankFour
  obtain ⟨frame, hframeFloored⟩ :=
    crux.exists_rankFourFrame_floored hdata hfloored hrankFour
  obtain ⟨nullVec, hne, hbasis, hchart⟩ := frame.exists_chart_null_basis_null
  exact hclosed crux frame hframeFloored nullVec hne hbasis hchart

/-- **THE FLOORED SPINE HAS NO ROOM.**  The canonical datum of a crux
lives at the argmax family, thus it is floored, and the three floored
rungs leave its assembly rank nowhere to sit. -/
theorem false_of_sixThreeCrux_of_forall_isSixThreeAssemblyRankExcludedFloored
    (hladder : ∀ assemblyRank : ℕ, 4 ≤ assemblyRank → assemblyRank ≤ 6 →
      IsSixThreeAssemblyRankExcludedFloored assemblyRank)
    (crux : SixThreeCrux) : False := by
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  obtain ⟨hfloor, hceiling⟩ := crux.finrank_range_multiplier_mem_rankWindow hdata
  exact hladder _ hfloor hceiling crux (Finset (Fin 6)) _ _ multiplier selection hdata
    (fun block hmem => crux.blockFloor_of_canonical hmem) rfl

/-- **THE CELL FROM THE THREE FLOORED RUNGS.** -/
theorem gtzWeighted_six_three_of_forall_isSixThreeAssemblyRankExcludedFloored
    (hladder : ∀ assemblyRank : ℕ, 4 ≤ assemblyRank → assemblyRank ≤ 6 →
      IsSixThreeAssemblyRankExcludedFloored assemblyRank) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_isEmpty_sixThreeCrux
    ⟨fun crux =>
      false_of_sixThreeCrux_of_forall_isSixThreeAssemblyRankExcludedFloored hladder crux⟩

/-- **THE CELL FROM THE FLOORED RESIDUE AND THE SIX UPPER CLOSURES.**
The rank-four rung collapses into one floored residue, ranks five and
six keep their landed closure lattices, and the spine composes. -/
theorem gtzWeighted_six_three_of_flooredResidue_of_upperClosures
    (hfour : RankFourChartNullBasisNullFlooredClosed)
    (hfiveOne : RankFiveSupportTwoClosed)
    (hfiveTwo : RankFiveSharedPrivateClosed)
    (hfiveDense : RankFiveDenseClosed)
    (hsixOne : RankSixSupportTwoClosed)
    (hsixTwo : RankSixSharedPrivateClosed)
    (hsixDense : RankSixDenseClosed) :
    GtzWeighted 6 3 := by
  refine gtzWeighted_six_three_of_forall_isSixThreeAssemblyRankExcludedFloored ?_
  intro assemblyRank hfloor hceiling
  interval_cases assemblyRank
  · exact isSixThreeAssemblyRankExcludedFloored_four_of_chartNullBasisNullFloored hfour
  · exact isSixThreeAssemblyRankExcludedFloored_of_excluded 5
      (isSixThreeAssemblyRankExcluded_five_of_closures hfiveOne hfiveTwo hfiveDense)
  · exact isSixThreeAssemblyRankExcludedFloored_of_excluded 6
      (isSixThreeAssemblyRankExcluded_six_of_closures hsixOne hsixTwo hsixDense)

/-- **THE RANK-THREE PAYOFF FROM THE FLOORED RESIDUE.** -/
theorem gtzWeightedAll_three_of_flooredResidue_of_upperClosures
    (hfour : RankFourChartNullBasisNullFlooredClosed)
    (hfiveOne : RankFiveSupportTwoClosed)
    (hfiveTwo : RankFiveSharedPrivateClosed)
    (hfiveDense : RankFiveDenseClosed)
    (hsixOne : RankSixSupportTwoClosed)
    (hsixTwo : RankSixSharedPrivateClosed)
    (hsixDense : RankSixDenseClosed) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three
    (gtzWeighted_six_three_of_flooredResidue_of_upperClosures hfour hfiveOne hfiveTwo
      hfiveDense hsixOne hsixTwo hsixDense)

end FlooredSpine

end Gtz

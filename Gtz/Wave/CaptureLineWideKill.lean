import Gtz.Wave.CaptureLinePairKill
import Gtz.Quantitative.PrivateAtomQuantization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The wide spectral kill — the split diagonal prices every frame

The stationary leak law of the pair kill has a matrix reading.  Sandwich
the assembly between two charts: the price matrix `P Ξ P` is positive
semidefinite, and its diagonal is EXACTLY the shifted weight over the
size.  At a rank-four frame the capture line sits in the kernel of the
assembly, thus the price matrix kills a chart-fixed line and the whole
kernel of the chart.  Its restriction to the range of the chart is then
a rank-two form, and the shifted weights become quadratic reads of the
atoms through a diagonal form with one FREE direction.

That structure is a selection theorem away from a contradiction.  The
selection statement is `Gtz.WideSpectralSelectionClosed`: a price matrix
of positive diagonal that the chart absorbs and that kills a chart-fixed
line admits a triple whose price-total-inflated chart energy dominates
the price diagonal.  The crux then dies: the price total is `1 + 6 G`
with `G < 0`, thus the triple dominates the shifted diagonal STRICTLY,
and the argmax field of the crux refuses a strictly dominating triple.

The residue is crux-free: two matrices, one vector, pure linear algebra
at size six.  Its calibration: 20 million random samples show zero
failures, and adversarial minimisation puts the sharp constant at the
inverse price total exactly, with the tied configurations carrying
parallel duplicated atoms.  Scratchpad: `certA15_claim.c`,
`certA15_adv.c`, `certA15_wide.c`.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.stationary_tight_energy`, `Gtz.stationary_leak_energy` — the
  per-label energy laws: the chart energy of a tight direction is its
  shifted-weight energy, and the leak energy of a label is its
  variance-weighted block energy.  Generic in size and rank.
* `Gtz.mul_assembly_mul_diag_eq_sum`, `Gtz.stationary_split_diag` —
  **THE SPLIT DIAGONAL LAW**: the price diagonal `(P Ξ P)_{yy}` is the
  shifted weight over the size, at every atom, for every stationary
  datum.  Generic in size and rank.
* `Gtz.WideSpectralSelectionClosed` — **THE RESIDUE**, crux-free.
* `Gtz.SixThreeCrux.false_of_stationary_fixed_kernel_line` — **THE
  FIXED KERNEL KILL**: a stationary crux datum whose assembly kernel
  holds a chart-fixed nonzero vector dies, modulo the residue.  The
  statement is rank-free: any datum, any active family.
* `Gtz.RankFourFrame.false_of_wideSpectralSelection` — **EVERY
  RANK-FOUR FRAME DIES**, modulo the residue: the capture line is the
  fixed kernel vector.
* `Gtz.rankFourCaptureLineWideFlooredClosed_of_wideSpectralSelection`,
  `Gtz.rankFourChartNullBasisNullClosed_of_wideSpectralSelection`,
  `Gtz.rankFourChartNullBasisNullFlooredClosed_of_wideSpectralSelection`,
  `Gtz.isSixThreeAssemblyRankExcluded_four_of_wideSpectralSelection`,
  `Gtz.isSixThreeAssemblyRankExcludedFloored_four_of_wideSpectralSelection`,
  `Gtz.gtzWeighted_six_three_of_wideSpectralSelection_of_upperClosures`,
  `Gtz.gtzWeightedAll_three_of_wideSpectralSelection_of_upperClosures` —
  **THE DISCHARGED SPINE**: the wide residue, the unfloored and floored
  rank-four residues, the two rungs, and the cell, each from the one
  crux-free residue (plus the six upper closures for the cell).

## Vacuity

The residue and the split calculus are unconditional statements about
matrices and stationary data.  Every crux-quantified statement is
vacuous if `Gtz.GtzWeighted 6 3` holds: no crux exists.
-/

namespace Gtz

open Matrix

/-! ## Layer 0 — the split calculus of a stationary datum -/

section SplitCalculus

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ} {value : ℝ}
variable {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE TIGHT ENERGY LAW.**  The chart energy of a tight direction is
its shifted-weight energy: the leak is pointwise orthogonal to the
direction, thus the ambient row read collapses onto the block. -/
theorem stationary_tight_energy
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet) :
    tightDir activeLabel ⬝ᵥ (projection *ᵥ tightDir activeLabel)
      = ∑ atomIndex, (value + weight atomIndex) * tightDir activeLabel atomIndex ^ 2 := by
  rw [dotProduct]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  linear_combination stationary_leak_orthogonal hdata hmem atomIndex

/-- **THE PER-LABEL LEAK ENERGY LAW.**  The full leak energy of one
label equals the variance-weighted energy of its block coordinates:
`Σ_y ℓ(y)² = Σ_y s_y (1 - s_y) q(y)²`.  Idempotence prices the image
energy, and the pointwise orthogonality removes every cross term. -/
theorem stationary_leak_energy
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet) :
    ∑ atomIndex, ((projection *ᵥ tightDir activeLabel) atomIndex
        - (value + weight atomIndex) * tightDir activeLabel atomIndex) ^ 2
      = ∑ atomIndex, (value + weight atomIndex) * (1 - (value + weight atomIndex))
          * tightDir activeLabel atomIndex ^ 2 := by
  have himageSum : ∑ atomIndex, ((projection *ᵥ tightDir activeLabel) atomIndex) ^ 2
      = ∑ atomIndex, (value + weight atomIndex) * tightDir activeLabel atomIndex ^ 2 := by
    have hcollapse : (projection *ᵥ tightDir activeLabel)
          ⬝ᵥ (projection *ᵥ tightDir activeLabel)
        = ∑ atomIndex, ((projection *ᵥ tightDir activeLabel) atomIndex) ^ 2 := by
      rw [dotProduct]
      exact Finset.sum_congr rfl fun atomIndex _ => (pow_two _).symm
    rw [← hcollapse,
      ← dotProduct_mulVec_eq_image_dotProduct_self hdata.isSymmetric hdata.isIdempotent,
      stationary_tight_energy hdata hmem]
  have hexpand : ∀ atomIndex ∈ (Finset.univ : Finset (Fin size)),
      ((projection *ᵥ tightDir activeLabel) atomIndex
          - (value + weight atomIndex) * tightDir activeLabel atomIndex) ^ 2
        = ((projection *ᵥ tightDir activeLabel) atomIndex) ^ 2
            - (value + weight atomIndex) ^ 2 * tightDir activeLabel atomIndex ^ 2
          + (-2 * (value + weight atomIndex))
            * (tightDir activeLabel atomIndex
              * ((projection *ᵥ tightDir activeLabel) atomIndex
                - (value + weight atomIndex) * tightDir activeLabel atomIndex)) :=
    fun atomIndex _ => by ring
  have hvanish : ∀ atomIndex ∈ (Finset.univ : Finset (Fin size)),
      (-2 * (value + weight atomIndex))
          * (tightDir activeLabel atomIndex
            * ((projection *ᵥ tightDir activeLabel) atomIndex
              - (value + weight atomIndex) * tightDir activeLabel atomIndex)) = 0 :=
    fun atomIndex _ => by
      rw [stationary_leak_orthogonal hdata hmem atomIndex, mul_zero]
  rw [Finset.sum_congr rfl hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_congr rfl hvanish, Finset.sum_const_zero, add_zero, himageSum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun atomIndex _ => by ring

/-- The price diagonal as a label sum: the diagonal entry of `P Ξ P` is
the multiplier-weighted squared chart row read of every label. -/
theorem mul_assembly_mul_diag_eq_sum
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    (projection * chartMultiplierAssembly activeSet activeWeight tightDir * projection)
        atomIndex atomIndex
      = ∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * ((projection *ᵥ tightDir activeLabel) atomIndex) ^ 2 := by
  classical
  have hsym : ∀ a b : Fin size, projection a b = projection b a := by
    intro a b
    have hentry := congrFun (congrFun hdata.isSymmetric a) b
    rw [Matrix.transpose_apply] at hentry
    exact hentry.symm
  have hmv : ∀ activeLabel : activeIndex,
      (projection *ᵥ tightDir activeLabel) atomIndex
        = ∑ w, projection atomIndex w * tightDir activeLabel w :=
    fun activeLabel => rfl
  have hPXi : ∀ z : Fin size,
      (projection * chartMultiplierAssembly activeSet activeWeight tightDir) atomIndex z
        = ∑ activeLabel ∈ activeSet, activeWeight activeLabel
            * ((projection *ᵥ tightDir activeLabel) atomIndex * tightDir activeLabel z) := by
    intro z
    rw [Matrix.mul_apply]
    have hpoint : ∀ w : Fin size,
        projection atomIndex w
            * chartMultiplierAssembly activeSet activeWeight tightDir w z
          = ∑ activeLabel ∈ activeSet, projection atomIndex w
              * (activeWeight activeLabel
                * (tightDir activeLabel w * tightDir activeLabel z)) := by
      intro w
      rw [chartMultiplierAssembly_apply, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun w _ => hpoint w, Finset.sum_comm]
    refine Finset.sum_congr rfl fun activeLabel _ => ?_
    rw [hmv activeLabel]
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun w _ => by ring
  have hexp : ∀ z ∈ (Finset.univ : Finset (Fin size)),
      (projection * chartMultiplierAssembly activeSet activeWeight tightDir) atomIndex z
          * projection z atomIndex
        = (∑ activeLabel ∈ activeSet, activeWeight activeLabel
            * ((projection *ᵥ tightDir activeLabel) atomIndex * tightDir activeLabel z))
          * projection z atomIndex :=
    fun z _ => by rw [hPXi z]
  rw [Matrix.mul_apply, Finset.sum_congr rfl hexp]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun activeLabel _ => ?_
  have hcol : ∑ z, tightDir activeLabel z * projection z atomIndex
      = (projection *ᵥ tightDir activeLabel) atomIndex := by
    rw [hmv activeLabel]
    exact Finset.sum_congr rfl fun z _ => by rw [hsym z atomIndex]; ring
  have hfactor : ∑ z, activeWeight activeLabel
        * ((projection *ᵥ tightDir activeLabel) atomIndex * tightDir activeLabel z)
        * projection z atomIndex
      = activeWeight activeLabel * ((projection *ᵥ tightDir activeLabel) atomIndex
          * ∑ z, tightDir activeLabel z * projection z atomIndex) := by
    conv_rhs => rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [hfactor, hcol]
  ring

/-- **THE SPLIT DIAGONAL LAW.**  The price diagonal is the shifted
weight over the size: `(P Ξ P)_{yy} = (value + w_y) / size` at EVERY
atom, for EVERY stationary datum.  The leak law prices the leak part,
the assembly diagonal prices the block part, and the pointwise
orthogonality removes the cross term. -/
theorem stationary_split_diag
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    (projection * chartMultiplierAssembly activeSet activeWeight tightDir * projection)
        atomIndex atomIndex
      = (value + weight atomIndex) * ((size : ℝ))⁻¹ := by
  classical
  rw [mul_assembly_mul_diag_eq_sum hdata atomIndex]
  have hsplit : ∀ activeLabel ∈ activeSet,
      activeWeight activeLabel * ((projection *ᵥ tightDir activeLabel) atomIndex) ^ 2
        = activeWeight activeLabel
              * ((projection *ᵥ tightDir activeLabel) atomIndex
                - (value + weight atomIndex) * tightDir activeLabel atomIndex) ^ 2
            + (value + weight atomIndex) ^ 2
              * (activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2)
          + (2 * (value + weight atomIndex) * activeWeight activeLabel)
            * (tightDir activeLabel atomIndex
              * ((projection *ᵥ tightDir activeLabel) atomIndex
                - (value + weight atomIndex) * tightDir activeLabel atomIndex)) :=
    fun activeLabel _ => by ring
  have hvanish : ∀ activeLabel ∈ activeSet,
      (2 * (value + weight atomIndex) * activeWeight activeLabel)
          * (tightDir activeLabel atomIndex
            * ((projection *ᵥ tightDir activeLabel) atomIndex
              - (value + weight atomIndex) * tightDir activeLabel atomIndex)) = 0 :=
    fun activeLabel hmem => by
      rw [stationary_leak_orthogonal hdata hmem atomIndex, mul_zero]
  have hassembly : ∑ activeLabel ∈ activeSet,
      activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2 = ((size : ℝ))⁻¹ :=
    (chartMultiplierAssembly_diagonal activeSet activeWeight tightDir atomIndex).symm.trans
      (hdata.assembly_diagonal atomIndex)
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_congr rfl hvanish, Finset.sum_const_zero, add_zero,
    stationary_leak_sq_sum hdata atomIndex, ← Finset.mul_sum, hassembly]
  ring

end SplitCalculus

/-! ## Layer 1 — the residue -/

section TheResidue

/-- **THE WIDE SPECTRAL SELECTION RESIDUE.**  A trace-three projection,
a positive-semidefinite price matrix of positive diagonal that the
projection absorbs, and a nonzero projection-fixed vector that the
price kills, admit a triple whose price-total-inflated chart energy
dominates the price diagonal on every supported probe.

The residue is crux-free.  In spectral form: the price restricted to
the range of the projection is a rank-two form that is blind in the
fixed direction, thus the scales are quadratic reads of Parseval atoms
through `diag (d₁, d₂, 0)`, and the claim is a selection theorem for
that family.  Calibration: 20 million random samples give zero
failures, adversarial minimisation puts the sharp constant at the
inverse price total exactly, and the tied configurations duplicate
atom directions.  Scratchpad: `certA15_claim.c`, `certA15_adv.c`. -/
def WideSpectralSelectionClosed : Prop :=
  ∀ (proj price : Matrix (Fin 6) (Fin 6) ℝ) (fixedVec : Fin 6 → ℝ),
    projᵀ = proj →
    proj * proj = proj →
    Matrix.trace proj = 3 →
    priceᵀ = price →
    (∀ vec : Fin 6 → ℝ, 0 ≤ vec ⬝ᵥ (price *ᵥ vec)) →
    proj * price = price →
    (∀ atomIndex : Fin 6, 0 < price atomIndex atomIndex) →
    fixedVec ≠ 0 →
    proj *ᵥ fixedVec = fixedVec →
    price *ᵥ fixedVec = 0 →
    ∃ block : Finset (Fin 6), block.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ atomIndex ∉ block, probe atomIndex = 0) →
          ∑ atomIndex, (6 * price atomIndex atomIndex) * probe atomIndex ^ 2
            ≤ (∑ atomIndex, 6 * price atomIndex atomIndex)
              * (probe ⬝ᵥ (proj *ᵥ probe))

end TheResidue

/-! ## Layer 2 — the fixed kernel line kill -/

section FixedKernelKill

/-- **THE FIXED KERNEL KILL.**  A stationary crux datum whose assembly
kernel holds a chart-fixed nonzero vector dies, modulo the residue.
The price matrix `P Ξ P` satisfies every residue hypothesis, its
diagonal is the shifted weight over six by the split diagonal law, and
its total is `1 + 6 G`.  The residue triple then dominates the shifted
diagonal STRICTLY, because `G < 0`, and the argmax field of the crux
supplies a unit block probe at or below the value — a contradiction. -/
theorem SixThreeCrux.false_of_stationary_fixed_kernel_line (crux : SixThreeCrux)
    {activeIndex : Type*} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin 6 → ℝ)}
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    {fixedVec : Fin 6 → ℝ} (hne : fixedVec ≠ 0)
    (hfix : (chartPointOfDesign crux.design).chart *ᵥ fixedVec = fixedVec)
    (hkernel : chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ fixedVec = 0)
    (hclosed : WideSpectralSelectionClosed) : False := by
  classical
  set chartP := (chartPointOfDesign crux.design).chart with hchartPDef
  set weightW := (chartPointOfDesign crux.design).weight with hweightWDef
  set valueG := chartObjective (chartPointOfDesign crux.design) with hvalueGDef
  set assemblyXi := chartMultiplierAssembly activeSet activeWeight tightDir with hXiDef
  set priceM := chartP * assemblyXi * chartP with hpriceDef
  have hdiag : ∀ atomIndex : Fin 6,
      priceM atomIndex atomIndex = (valueG + weightW atomIndex) * ((6 : ℕ) : ℝ)⁻¹ :=
    fun atomIndex => stationary_split_diag hdata atomIndex
  have hsix : ∀ atomIndex : Fin 6,
      6 * priceM atomIndex atomIndex = valueG + weightW atomIndex := by
    intro atomIndex
    rw [hdiag atomIndex]
    push_cast
    ring
  have hpriceSym : priceMᵀ = priceM := by
    rw [hpriceDef, Matrix.transpose_mul, Matrix.transpose_mul,
      transpose_chartMultiplierAssembly_of_isChartStationaryData hdata, hdata.isSymmetric,
      Matrix.mul_assoc]
  have hpsd : ∀ vec : Fin 6 → ℝ, 0 ≤ vec ⬝ᵥ (priceM *ᵥ vec) := by
    intro vec
    have hsplit : priceM *ᵥ vec = chartP *ᵥ (assemblyXi *ᵥ (chartP *ᵥ vec)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hpriceDef]
    have hadjoint := dotProduct_mulVec_transpose chartP vec
      (assemblyXi *ᵥ (chartP *ᵥ vec))
    rw [hdata.isSymmetric] at hadjoint
    rw [hsplit, ← hadjoint, dotProduct_mulVec_chartMultiplierAssembly]
    exact Finset.sum_nonneg fun activeLabel hmem =>
      mul_nonneg (hdata.activeWeight_nonneg activeLabel hmem) (sq_nonneg _)
  have habsorb : chartP * priceM = priceM := by
    rw [hpriceDef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hdata.isIdempotent]
  have hdiagPos : ∀ atomIndex : Fin 6, 0 < priceM atomIndex atomIndex := by
    intro atomIndex
    rw [hdiag atomIndex]
    exact mul_pos (crux.shifted_weight_pos atomIndex) (by norm_num)
  have hMf : priceM *ᵥ fixedVec = 0 := by
    rw [hpriceDef, ← Matrix.mulVec_mulVec, hfix, ← Matrix.mulVec_mulVec, hkernel,
      Matrix.mulVec_zero]
  obtain ⟨block, hcard, hdom⟩ := hclosed chartP priceM fixedVec hdata.isSymmetric
    hdata.isIdempotent crux.chart_trace hpriceSym hpsd habsorb hdiagPos hne hfix hMf
  obtain ⟨probe, hunit, hsupp, hceil⟩ := crux.isChartArgmaxValue block hcard
  have hdomP := hdom probe hsupp
  have hsigma : ∑ atomIndex, 6 * priceM atomIndex atomIndex = 6 * valueG + 1 := by
    rw [Finset.sum_congr rfl fun atomIndex _ => hsix atomIndex, Finset.sum_add_distrib,
      hdata.weight_sum_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring
  have hshift : ∑ atomIndex, (6 * priceM atomIndex atomIndex) * probe atomIndex ^ 2
      = ∑ atomIndex, (valueG + weightW atomIndex) * probe atomIndex ^ 2 :=
    Finset.sum_congr rfl fun atomIndex _ => by rw [hsix atomIndex]
  rw [hsigma, hshift] at hdomP
  have hsumOne : ∑ atomIndex, probe atomIndex ^ 2 = 1 := by
    rw [dotProduct] at hunit
    rw [← hunit]
    exact Finset.sum_congr rfl fun atomIndex _ => pow_two _
  have hgap := hceil
  rw [dotProduct_chartStationaryGap_mulVec_self] at hgap
  have henergyLe : probe ⬝ᵥ (chartP *ᵥ probe)
      ≤ ∑ atomIndex, (valueG + weightW atomIndex) * probe atomIndex ^ 2 := by
    have hexpand : ∑ atomIndex, (valueG + weightW atomIndex) * probe atomIndex ^ 2
        = valueG * ∑ atomIndex, probe atomIndex ^ 2
          + ∑ atomIndex, weightW atomIndex * probe atomIndex ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun atomIndex _ => by ring
    rw [hexpand, hsumOne, mul_one]
    linarith [hgap]
  have henergyNonneg : 0 ≤ probe ⬝ᵥ (chartP *ᵥ probe) := by
    rw [dotProduct_mulVec_eq_image_dotProduct_self hdata.isSymmetric hdata.isIdempotent,
      dotProduct]
    exact Finset.sum_nonneg fun atomIndex _ => mul_self_nonneg _
  have hprobeNe : probe ≠ 0 := by
    intro hzero
    rw [hzero] at hunit
    simp [dotProduct] at hunit
  obtain ⟨liveAtom, hlive⟩ := Function.ne_iff.mp hprobeNe
  have hliveNe : probe liveAtom ≠ 0 := by simpa using hlive
  have hshiftPos : 0 < ∑ atomIndex, (valueG + weightW atomIndex) * probe atomIndex ^ 2 :=
    Finset.sum_pos'
      (fun atomIndex _ =>
        mul_nonneg (crux.shifted_weight_pos atomIndex).le (sq_nonneg _))
      ⟨liveAtom, Finset.mem_univ liveAtom,
        mul_pos (crux.shifted_weight_pos liveAtom)
          ((sq_nonneg (probe liveAtom)).lt_of_ne (Ne.symm (pow_ne_zero 2 hliveNe)))⟩
  have hvalueNeg : valueG < 0 := crux.hasNegativeChartValue
  rcases le_or_gt 0 (6 * valueG + 1) with hsigmaNonneg | hsigmaNeg
  · have hchain : ∑ atomIndex, (valueG + weightW atomIndex) * probe atomIndex ^ 2
        ≤ (6 * valueG + 1)
          * ∑ atomIndex, (valueG + weightW atomIndex) * probe atomIndex ^ 2 :=
      le_trans hdomP (mul_le_mul_of_nonneg_left henergyLe hsigmaNonneg)
    nlinarith [hchain, hshiftPos, hvalueNeg,
      mul_pos (neg_pos.mpr hvalueNeg) hshiftPos]
  · nlinarith [hdomP, hshiftPos, henergyNonneg, hsigmaNeg]

end FixedKernelKill

/-! ## Layer 3 — every rank-four frame dies -/

section RankFourKill

variable {crux : SixThreeCrux}

/-- A basis-null vector is orthogonal to the tight direction of every
positive label: the direction sits in the span of the basis. -/
theorem RankFourFrame.tightDir_dotProduct_eq_zero_of_basis_null
    (frame : RankFourFrame crux) {vec : Fin 6 → ℝ}
    (hbasis : ∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) ⬝ᵥ vec = 0)
    {activeLabel : frame.activeIndex} (hmem : activeLabel ∈ frame.activeSet)
    (hpos : 0 < frame.reducedWeight activeLabel) :
    frame.tightDir activeLabel ⬝ᵥ vec = 0 := by
  classical
  have hrange := tightDir_mem_range_multiplier_of_pos frame.hdata hmem hpos
  rw [← frame.hspan] at hrange
  obtain ⟨coeff, hcoeff⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hrange
  rw [← hcoeff, dotProduct]
  have hexpand : ∀ atomIndex ∈ (Finset.univ : Finset (Fin 6)),
      (∑ slot, coeff slot • frame.tightDir (frame.basisLabel slot)) atomIndex
          * vec atomIndex
        = ∑ slot, coeff slot
            * (frame.tightDir (frame.basisLabel slot) atomIndex * vec atomIndex) := by
    intro atomIndex _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun slot _ => by ring
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  refine Finset.sum_eq_zero fun slot _ => ?_
  rw [← Finset.mul_sum]
  have hdot := hbasis slot
  rw [dotProduct] at hdot
  rw [hdot, mul_zero]

/-- **A BASIS-NULL VECTOR SITS IN THE ASSEMBLY KERNEL.**  Every label
of the assembly has a zero multiplier or a positive one, and in the
second case its tight direction is orthogonal to the vector. -/
theorem RankFourFrame.assembly_mulVec_eq_zero_of_basis_null
    (frame : RankFourFrame crux) {vec : Fin 6 → ℝ}
    (hbasis : ∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) ⬝ᵥ vec = 0) :
    chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir *ᵥ vec
      = 0 := by
  classical
  funext atomIndex
  simp only [Pi.zero_apply]
  rw [Matrix.mulVec, dotProduct]
  have hexpand : ∀ z ∈ (Finset.univ : Finset (Fin 6)),
      chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir
          atomIndex z * vec z
        = ∑ activeLabel ∈ frame.activeSet, frame.reducedWeight activeLabel
            * (frame.tightDir activeLabel atomIndex
              * (frame.tightDir activeLabel z * vec z)) := by
    intro z _
    rw [chartMultiplierAssembly_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun activeLabel _ => by ring
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  refine Finset.sum_eq_zero fun activeLabel hmem => ?_
  have hcollect : ∑ z, frame.reducedWeight activeLabel
        * (frame.tightDir activeLabel atomIndex * (frame.tightDir activeLabel z * vec z))
      = frame.reducedWeight activeLabel * (frame.tightDir activeLabel atomIndex
          * ∑ z, frame.tightDir activeLabel z * vec z) := by
    conv_rhs => rw [Finset.mul_sum, Finset.mul_sum]
  rw [hcollect]
  rcases (frame.hdata.activeWeight_nonneg activeLabel hmem).eq_or_lt with hzero | hpos
  · rw [← hzero, zero_mul]
  · have hdot := frame.tightDir_dotProduct_eq_zero_of_basis_null hbasis hmem hpos
    rw [dotProduct] at hdot
    rw [hdot, mul_zero, mul_zero]

/-- **EVERY RANK-FOUR FRAME DIES, MODULO THE RESIDUE.**  The capture
line of the frame is chart-fixed, basis-null and nonzero, thus it is a
fixed kernel line of the frame datum. -/
theorem RankFourFrame.false_of_wideSpectralSelection (frame : RankFourFrame crux)
    (hclosed : WideSpectralSelectionClosed) : False := by
  obtain ⟨lineVec, hne, _hfixResidue, hbasis, hchart⟩ := frame.exists_capture_line
  exact crux.false_of_stationary_fixed_kernel_line frame.hdata hne hchart
    (frame.assembly_mulVec_eq_zero_of_basis_null hbasis) hclosed

end RankFourKill

/-! ## Layer 4 — the discharged spine -/

section Spine

/-- **THE WIDE RESIDUE, DISCHARGED.**  The wide capture line data is not
needed: the frame alone dies. -/
theorem rankFourCaptureLineWideFlooredClosed_of_wideSpectralSelection
    (hclosed : WideSpectralSelectionClosed) : RankFourCaptureLineWideFlooredClosed := by
  intro crux frame _hfloors _nullVec _lineVec _atomOne _atomTwo _atomThree _hne _hnullBasis
    _hnullChart _hneOneTwo _hneOneThree _hneTwoThree _hliveOne _hliveTwo _hliveThree
    _hlineChart _hlineBasis
  exact frame.false_of_wideSpectralSelection hclosed

/-- The unfloored rank-four residue, discharged. -/
theorem rankFourChartNullBasisNullClosed_of_wideSpectralSelection
    (hclosed : WideSpectralSelectionClosed) : RankFourChartNullBasisNullClosed := by
  intro crux frame _nullVec _hne _hbasis _hchart
  exact frame.false_of_wideSpectralSelection hclosed

/-- The floored rank-four residue, discharged. -/
theorem rankFourChartNullBasisNullFlooredClosed_of_wideSpectralSelection
    (hclosed : WideSpectralSelectionClosed) : RankFourChartNullBasisNullFlooredClosed := by
  intro crux frame _hfloors _nullVec _hne _hbasis _hchart
  exact frame.false_of_wideSpectralSelection hclosed

/-- The unfloored rank-four rung from the residue. -/
theorem isSixThreeAssemblyRankExcluded_four_of_wideSpectralSelection
    (hclosed : WideSpectralSelectionClosed) : IsSixThreeAssemblyRankExcluded 4 :=
  isSixThreeAssemblyRankExcluded_four_of_chartNullBasisNull
    (rankFourChartNullBasisNullClosed_of_wideSpectralSelection hclosed)

/-- The floored rank-four rung from the residue. -/
theorem isSixThreeAssemblyRankExcludedFloored_four_of_wideSpectralSelection
    (hclosed : WideSpectralSelectionClosed) : IsSixThreeAssemblyRankExcludedFloored 4 :=
  isSixThreeAssemblyRankExcludedFloored_four_of_chartNullBasisNullFloored
    (rankFourChartNullBasisNullFlooredClosed_of_wideSpectralSelection hclosed)

/-- **THE CELL FROM THE ONE CRUX-FREE RESIDUE AND THE SIX UPPER
CLOSURES.** -/
theorem gtzWeighted_six_three_of_wideSpectralSelection_of_upperClosures
    (hclosed : WideSpectralSelectionClosed)
    (hfiveOne : RankFiveSupportTwoClosed)
    (hfiveTwo : RankFiveSharedPrivateClosed)
    (hfiveDense : RankFiveDenseClosed)
    (hsixOne : RankSixSupportTwoClosed)
    (hsixTwo : RankSixSharedPrivateClosed)
    (hsixDense : RankSixDenseClosed) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_wideResidue_of_upperClosures
    (rankFourCaptureLineWideFlooredClosed_of_wideSpectralSelection hclosed)
    hfiveOne hfiveTwo hfiveDense hsixOne hsixTwo hsixDense

/-- The rank-three payoff from the one crux-free residue and the six
upper closures. -/
theorem gtzWeightedAll_three_of_wideSpectralSelection_of_upperClosures
    (hclosed : WideSpectralSelectionClosed)
    (hfiveOne : RankFiveSupportTwoClosed)
    (hfiveTwo : RankFiveSharedPrivateClosed)
    (hfiveDense : RankFiveDenseClosed)
    (hsixOne : RankSixSupportTwoClosed)
    (hsixTwo : RankSixSharedPrivateClosed)
    (hsixDense : RankSixDenseClosed) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three
    (gtzWeighted_six_three_of_wideSpectralSelection_of_upperClosures hclosed hfiveOne
      hfiveTwo hfiveDense hsixOne hsixTwo hsixDense)

end Spine

end Gtz

import Gtz.Wave.SharedPairOuterReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The shared-pair capture narrowing — the outer sharer meets the sign law

The refined bridge routes `Gtz.RankFourSupportTwoClosed` through the
outer sharer kill.  This file narrows that residual again: the two
shifted pair weights of the pair column are strictly positive at every
surviving configuration, and the capture cross entry opposes the pair
sign quantitatively.

The mechanism, in six layers:

1. **The entry Cauchy–Schwarz for positive matrices.**  The square of an
   off-diagonal entry of a positive semidefinite matrix is at most the
   product of the two diagonal entries.  The probe family prices the
   discriminant, as in the idempotent case.
2. **The capture symmetry and the complement conjugation.**  The capture
   is symmetric, and the assembly minus the capture is the conjugation
   of the assembly by the complement of the chart.  Thus the capture
   quadratic is at most the assembly quadratic at every probe.
3. **The pair kernel reads.**  The quadratic form of the pair kernel
   vector reads the four corner entries, and the assembly diagonal
   collapses the diagonal part to the uniform constant.  The pair block
   trace identity splits the two capture diagonals between the pair
   direction and the pair kernel vector.
4. **THE SIGN LAW.**  At a pair column, the capture Rayleigh cap prices
   the capture cross entry against the pair sign: twice the cross entry
   times the pair product is at most the value times the shifted pair
   energy.  The value is negative, thus the cross entry opposes the
   pair.
5. **THE ZERO PROPAGATION.**  If one shifted pair weight vanishes, the
   pair minor kills the cross entry, and the sign law kills the other
   shifted weight.  Thus the two shifted weights vanish together.
6. **THE POSITIVE BRIDGE.**  When the two shifted weights vanish, the
   pair energy vanishes, the projected direction dies, and the crux
   forbids the parallel pair — with no privacy hypothesis.  Thus the
   closure narrows to the outer kill with strictly positive shifted
   pair weights and the sign law in hand.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.sq_entry_le_diagonal_mul_of_posSemidef` — **THE POSITIVE ENTRY
  CAUCHY–SCHWARZ.**
* `Gtz.capture_transpose_of_isChartStationaryData` — the capture
  symmetry.
* `Gtz.assembly_sub_capture_eq_complement_conj`,
  `Gtz.capture_quadratic_le_assembly_quadratic` — **THE COMPLEMENT
  CONJUGATION.**
* `Gtz.pairKernel_quadratic_read`,
  `Gtz.assembly_pairKernel_quadratic_read`,
  `Gtz.pair_block_trace_sum` — **THE PAIR KERNEL READS.**
* `Gtz.shared_capture_cross_sign` — **THE SIGN LAW.**
* `Gtz.capture_pair_minor` — the pair minor.
* `Gtz.capture_pair_trace_read`, `Gtz.assembly_pair_offdiag_sq_le`,
  `Gtz.capture_pairKernel_le`,
  `Gtz.shared_pair_squeeze_inequality` — **THE SHARED SQUEEZE
  SUPPLY.**
* `Gtz.shared_pair_zero_propagation` — **THE ZERO PROPAGATION.**
* `Gtz.RankFourFrame.false_of_pair_shifted_weights_zero` — the
  privacy-free zero ending.
* `Gtz.rankFourSupportTwoClosed_of_positive_shared_kill` — **THE
  POSITIVE BRIDGE.**

## Vacuity

The closure statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no
crux exists, thus no frame exists.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## Layer 1 — the entry Cauchy–Schwarz for positive matrices -/

/-- **THE POSITIVE ENTRY CAUCHY–SCHWARZ.**  The square of an
off-diagonal entry of a positive semidefinite matrix is at most the
product of the two diagonal entries.  The probe family `t e_u + e_v`
prices the discriminant. -/
theorem sq_entry_le_diagonal_mul_of_posSemidef {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hpsd : A.PosSemidef)
    {atomU atomV : Fin n} (hne : atomU ≠ atomV) :
    A atomU atomV ^ 2 ≤ A atomU atomU * A atomV atomV := by
  have hVU : A atomV atomU = A atomU atomV := by
    have hentry := congrFun (congrFun hpsd.1 atomV) atomU
    rw [Matrix.conjTranspose_apply, star_trivial] at hentry
    exact hentry.symm
  have hquad : ∀ t : ℝ, 0 ≤ A atomU atomU * (t * t)
      + (2 * A atomU atomV) * t + A atomV atomV := by
    intro t
    have hsupp : ∀ atomIndex : Fin n, atomIndex ≠ atomU → atomIndex ≠ atomV →
        (fun probeIndex => if probeIndex = atomU then t
          else if probeIndex = atomV then 1 else 0 : Fin n → ℝ) atomIndex = 0 := by
      intro atomIndex hU hV
      simp only [if_neg hU, if_neg hV]
    have hnonneg := dotProduct_mulVec_nonneg_of_posSemidef hpsd
      (fun probeIndex => if probeIndex = atomU then t
        else if probeIndex = atomV then 1 else 0)
    have hread := dotProduct_mulVec_of_pair_support A hne hsupp
    rw [hread] at hnonneg
    simp only [if_neg (Ne.symm hne)] at hnonneg
    calc (0 : ℝ) ≤ t * (A atomU atomU * t + A atomU atomV * 1)
          + 1 * (A atomV atomU * t + A atomV atomV * 1) := hnonneg
      _ = A atomU atomU * (t * t) + (2 * A atomU atomV) * t + A atomV atomV := by
          rw [hVU]; ring
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-! ## Layer 2 — the capture symmetry and the complement conjugation -/

/-- The capture is symmetric: the commutation swaps the two factors, and
each factor is symmetric. -/
theorem capture_transpose_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    (projection * chartMultiplierAssembly activeSet activeWeight tightDir)ᵀ
      = projection * chartMultiplierAssembly activeSet activeWeight tightDir := by
  rw [Matrix.transpose_mul,
    transpose_chartMultiplierAssembly_of_isChartStationaryData hdata,
    hdata.isSymmetric, hdata.assembly_commutes]

/-- **THE COMPLEMENT CONJUGATION.**  The assembly minus the capture is
the conjugation of the assembly by the complement of the chart.  The
sandwich law and the commutation collapse the four cross terms. -/
theorem assembly_sub_capture_eq_complement_conj
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    chartMultiplierAssembly activeSet activeWeight tightDir
        - projection * chartMultiplierAssembly activeSet activeWeight tightDir
      = (1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir
          * (1 - projection) := by
  have hsandwich := projection_mul_multiplier_eq_sandwich_of_isChartStationaryData hdata
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_sub, Matrix.mul_one, ← hsandwich, ← hdata.assembly_commutes]
  abel

/-- The capture quadratic is at most the assembly quadratic at every
probe: the difference is the assembly energy of the complement-projected
probe. -/
theorem capture_quadratic_le_assembly_quadratic
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (probe : Fin size → ℝ) :
    probe ⬝ᵥ ((projection * chartMultiplierAssembly activeSet activeWeight tightDir)
        *ᵥ probe)
      ≤ probe ⬝ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ probe) := by
  have hcomplSymm : (1 - projection)ᵀ = 1 - projection := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hdata.isSymmetric]
  have hfold : probe ⬝ᵥ (((1 - projection)
          * chartMultiplierAssembly activeSet activeWeight tightDir
          * (1 - projection)) *ᵥ probe)
      = ((1 - projection) *ᵥ probe)
          ⬝ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir
            *ᵥ ((1 - projection) *ᵥ probe)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec probe (1 - projection), ← hcomplSymm,
      Matrix.vecMul_transpose, hcomplSymm]
  have hnonneg := dotProduct_mulVec_nonneg_of_posSemidef
    (posSemidef_chartMultiplierAssembly_of_isChartStationaryData hdata)
    ((1 - projection) *ᵥ probe)
  have hdiff : probe ⬝ᵥ ((chartMultiplierAssembly activeSet activeWeight tightDir
          - projection * chartMultiplierAssembly activeSet activeWeight tightDir)
        *ᵥ probe)
      = probe ⬝ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ probe)
        - probe ⬝ᵥ ((projection
            * chartMultiplierAssembly activeSet activeWeight tightDir) *ᵥ probe) := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
  rw [assembly_sub_capture_eq_complement_conj hdata, hfold] at hdiff
  linarith [hnonneg, hdiff.symm.le, hdiff.le]

/-! ## Layer 3 — the pair kernel reads -/

/-- The quadratic form of the pair kernel vector reads the four corner
entries with the wedge signs. -/
theorem pairKernel_quadratic_read {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) {atomU atomV : Fin n} (hne : atomU ≠ atomV)
    (firstCoord secondCoord : ℝ) :
    pairKernelVec firstCoord secondCoord atomU atomV
        ⬝ᵥ (S *ᵥ pairKernelVec firstCoord secondCoord atomU atomV)
      = S atomU atomU * secondCoord ^ 2
        - (S atomU atomV + S atomV atomU) * (firstCoord * secondCoord)
        + S atomV atomV * firstCoord ^ 2 := by
  have hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      pairKernelVec firstCoord secondCoord atomU atomV atomIndex = 0 :=
    fun atomIndex hU hV => pairKernelVec_apply_off hU hV
  rw [dotProduct_mulVec_of_pair_support S hne hsupp, pairKernelVec_apply_one,
    pairKernelVec_apply_two hne]
  ring

/-- The assembly quadratic of the pair kernel vector: the assembly
diagonal collapses the diagonal part to the uniform constant. -/
theorem assembly_pairKernel_quadratic_read
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {atomU atomV : Fin size} (hne : atomU ≠ atomV) (firstCoord secondCoord : ℝ) :
    pairKernelVec firstCoord secondCoord atomU atomV
        ⬝ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir
          *ᵥ pairKernelVec firstCoord secondCoord atomU atomV)
      = (firstCoord ^ 2 + secondCoord ^ 2) * ((size : ℝ))⁻¹
        - (chartMultiplierAssembly activeSet activeWeight tightDir atomU atomV
            + chartMultiplierAssembly activeSet activeWeight tightDir atomV atomU)
          * (firstCoord * secondCoord) := by
  rw [pairKernel_quadratic_read _ hne, hdata.assembly_diagonal atomU,
    hdata.assembly_diagonal atomV]
  ring

/-- **THE PAIR BLOCK TRACE SUM.**  The quadratic forms of a unit pair
direction and of its pair kernel vector split the two diagonal entries
of any square matrix. -/
theorem pair_block_trace_sum {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) {atomU atomV : Fin n} (hne : atomU ≠ atomV)
    {q : Fin n → ℝ}
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV → q atomIndex = 0)
    (hunit : q atomU ^ 2 + q atomV ^ 2 = 1) :
    q ⬝ᵥ (S *ᵥ q)
        + pairKernelVec (q atomU) (q atomV) atomU atomV
            ⬝ᵥ (S *ᵥ pairKernelVec (q atomU) (q atomV) atomU atomV)
      = S atomU atomU + S atomV atomV := by
  rw [dotProduct_mulVec_of_pair_support S hne hsupp,
    pairKernel_quadratic_read S hne]
  linear_combination (S atomU atomU + S atomV atomV) * hunit

/-! ## Layer 4 — the sign law -/

/-- **THE SIGN LAW.**  At a pair column, the capture Rayleigh cap prices
the capture cross entry against the pair sign: the cross sum times the
pair product is at most the value times the shifted pair energy.  The
capture diagonal reads cancel the trace part exactly. -/
theorem shared_capture_cross_sign
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hne : atomU ≠ atomV)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    ((projection * chartMultiplierAssembly activeSet activeWeight tightDir) atomU atomV
        + (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
            atomV atomU)
        * (tightDir label atomU * tightDir label atomV)
      ≤ value * ((value + weight atomU) * tightDir label atomU ^ 2
          + (value + weight atomV) * tightDir label atomV ^ 2) := by
  have hunit := pair_support_unit_read hdata hmem hne hsupp
  have hray := capture_quadratic_le_of_isChartStationaryData hdata (tightDir label)
  have henergy : tightDir label ⬝ᵥ (projection *ᵥ tightDir label)
      = value + (weight atomU * tightDir label atomU ^ 2
        + weight atomV * tightDir label atomV ^ 2) := by
    rw [tight_energy_read hdata hmem, pair_support_energy_read hne hsupp]
  have hcaptureRead := dotProduct_mulVec_of_pair_support
    (projection * chartMultiplierAssembly activeSet activeWeight tightDir) hne hsupp
  have hdiagU := diagonal_projection_mul_multiplier_of_isChartStationaryData
    hdata atomU
  have hdiagV := diagonal_projection_mul_multiplier_of_isChartStationaryData
    hdata atomV
  rw [hcaptureRead, hdiagU, hdiagV, henergy] at hray
  have hchart : value + (weight atomU * tightDir label atomU ^ 2
        + weight atomV * tightDir label atomV ^ 2)
      = (value + weight atomU) * tightDir label atomU ^ 2
        + (value + weight atomV) * tightDir label atomV ^ 2 := by
    linear_combination (-value) * hunit
  rw [hchart] at hray
  nlinarith [hray]

/-! ## Layer 5 — the pair minor and the zero propagation -/

/-- The pair minor of the capture: the square of the capture cross entry
is at most the product of the two shifted-weight diagonals. -/
theorem capture_pair_minor
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {atomU atomV : Fin size} (hne : atomU ≠ atomV) :
    (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
        atomU atomV ^ 2
      ≤ ((value + weight atomU) * ((size : ℝ))⁻¹)
        * ((value + weight atomV) * ((size : ℝ))⁻¹) := by
  have hcs := sq_entry_le_diagonal_mul_of_posSemidef
    (posSemidef_projection_mul_multiplier_of_isChartStationaryData hdata) hne
  rwa [diagonal_projection_mul_multiplier_of_isChartStationaryData hdata atomU,
    diagonal_projection_mul_multiplier_of_isChartStationaryData hdata atomV] at hcs

/-- **THE ZERO PROPAGATION.**  If the shifted weight at the second pair
atom vanishes, the pair minor kills the capture cross entry, and the
sign law kills the shifted weight at the first pair atom. -/
theorem shared_pair_zero_propagation
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hne : atomU ≠ atomV)
    (hneU : tightDir label atomU ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0)
    (hvalueNeg : value < 0) (hzeroV : value + weight atomV = 0) :
    value + weight atomU = 0 := by
  have hminor := capture_pair_minor hdata hne (activeSubset := activeSubset)
    (activeWeight := activeWeight) (tightDir := tightDir)
  rw [hzeroV] at hminor
  have hcrossZero : (projection
      * chartMultiplierAssembly activeSet activeWeight tightDir) atomU atomV = 0 := by
    have hsq : (projection
        * chartMultiplierAssembly activeSet activeWeight tightDir) atomU atomV ^ 2
        ≤ 0 := by
      calc (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
            atomU atomV ^ 2
          ≤ (value + weight atomU) * ((size : ℝ))⁻¹ * (0 * ((size : ℝ))⁻¹) := hminor
        _ = 0 := by ring
    nlinarith [sq_nonneg ((projection
      * chartMultiplierAssembly activeSet activeWeight tightDir) atomU atomV)]
  have hcrossZero' : (projection
      * chartMultiplierAssembly activeSet activeWeight tightDir) atomV atomU = 0 := by
    have hentry := congrFun (congrFun
      (capture_transpose_of_isChartStationaryData hdata) atomU) atomV
    rw [Matrix.transpose_apply] at hentry
    rw [hentry]
    exact hcrossZero
  have hsign := shared_capture_cross_sign hdata hmem hne hsupp
  rw [hcrossZero, hcrossZero', hzeroV] at hsign
  have hfloorU := capture_diagonal_nonneg_of_isChartStationaryData hdata atomU
  have hsqU : (0 : ℝ) < tightDir label atomU ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hneU))
  have hle : value + weight atomU ≤ 0 := by
    by_contra hpos
    push Not at hpos
    nlinarith [hsign, hvalueNeg, mul_pos hpos hsqU]
  exact le_antisymm hle hfloorU

/-! ## Layer 5b — the shared squeeze supply -/

/-- **THE CAPTURE PAIR TRACE READ.**  The capture quadratics of a unit
pair direction and of its pair kernel vector split the two shifted
weights over the size. -/
theorem capture_pair_trace_read
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hne : atomU ≠ atomV)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    tightDir label ⬝ᵥ ((projection
          * chartMultiplierAssembly activeSet activeWeight tightDir)
        *ᵥ tightDir label)
        + pairKernelVec (tightDir label atomU) (tightDir label atomV) atomU atomV
            ⬝ᵥ ((projection
                * chartMultiplierAssembly activeSet activeWeight tightDir)
              *ᵥ pairKernelVec (tightDir label atomU) (tightDir label atomV)
                atomU atomV)
      = ((value + weight atomU) + (value + weight atomV)) * ((size : ℝ))⁻¹ := by
  have hunit := pair_support_unit_read hdata hmem hne hsupp
  have htrace := pair_block_trace_sum
    (projection * chartMultiplierAssembly activeSet activeWeight tightDir) hne
    hsupp hunit
  rw [diagonal_projection_mul_multiplier_of_isChartStationaryData hdata atomU,
    diagonal_projection_mul_multiplier_of_isChartStationaryData hdata atomV]
    at htrace
  rw [htrace]
  ring

/-- The assembly pair minor: the square of the assembly cross entry is
at most the square of the uniform diagonal. -/
theorem assembly_pair_offdiag_sq_le
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {atomU atomV : Fin size} (hne : atomU ≠ atomV) :
    chartMultiplierAssembly activeSet activeWeight tightDir atomU atomV ^ 2
      ≤ ((size : ℝ))⁻¹ ^ 2 := by
  have hcs := sq_entry_le_diagonal_mul_of_posSemidef
    (posSemidef_chartMultiplierAssembly_of_isChartStationaryData hdata) hne
  rw [hdata.assembly_diagonal atomU, hdata.assembly_diagonal atomV] at hcs
  nlinarith [hcs]

/-- **THE WEDGE CAP.**  The capture quadratic of the pair kernel vector
is at most its assembly quadratic, and the assembly quadratic reads the
uniform diagonal against the assembly cross sum. -/
theorem capture_pairKernel_le
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {atomU atomV : Fin size} (hne : atomU ≠ atomV) (firstCoord secondCoord : ℝ) :
    pairKernelVec firstCoord secondCoord atomU atomV
        ⬝ᵥ ((projection * chartMultiplierAssembly activeSet activeWeight tightDir)
          *ᵥ pairKernelVec firstCoord secondCoord atomU atomV)
      ≤ (firstCoord ^ 2 + secondCoord ^ 2) * ((size : ℝ))⁻¹
        - (chartMultiplierAssembly activeSet activeWeight tightDir atomU atomV
            + chartMultiplierAssembly activeSet activeWeight tightDir atomV atomU)
          * (firstCoord * secondCoord) := by
  have hle := capture_quadratic_le_assembly_quadratic hdata
    (pairKernelVec firstCoord secondCoord atomU atomV)
  rwa [assembly_pairKernel_quadratic_read hdata hne] at hle

/-- **THE SHARED SQUEEZE INEQUALITY.**  The trace read, the wedge cap,
and the capture Rayleigh cap combine into the shared replacement of the
private alignment: the shifted pair mass minus the wedge allowance is at
most the capped pair energy.  This inequality is the entry point of the
outer sharer kill. -/
theorem shared_pair_squeeze_inequality
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hne : atomU ≠ atomV)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    ((value + weight atomU) + (value + weight atomV)) * ((size : ℝ))⁻¹
        - ((size : ℝ))⁻¹
        + (chartMultiplierAssembly activeSet activeWeight tightDir atomU atomV
            + chartMultiplierAssembly activeSet activeWeight tightDir atomV atomU)
          * (tightDir label atomU * tightDir label atomV)
      ≤ (value + ((size : ℝ))⁻¹)
        * ((value + weight atomU) * tightDir label atomU ^ 2
          + (value + weight atomV) * tightDir label atomV ^ 2) := by
  have hunit := pair_support_unit_read hdata hmem hne hsupp
  have htrace := capture_pair_trace_read hdata hmem hne hsupp
  have hwedge := capture_pairKernel_le hdata hne
    (tightDir label atomU) (tightDir label atomV)
  have hray := capture_quadratic_le_of_isChartStationaryData hdata (tightDir label)
  have henergy : tightDir label ⬝ᵥ (projection *ᵥ tightDir label)
      = value + (weight atomU * tightDir label atomU ^ 2
        + weight atomV * tightDir label atomV ^ 2) := by
    rw [tight_energy_read hdata hmem, pair_support_energy_read hne hsupp]
  have hchart : value + (weight atomU * tightDir label atomU ^ 2
        + weight atomV * tightDir label atomV ^ 2)
      = (value + weight atomU) * tightDir label atomU ^ 2
        + (value + weight atomV) * tightDir label atomV ^ 2 := by
    linear_combination (-value) * hunit
  rw [henergy, hchart] at hray
  rw [hunit, one_mul] at hwedge
  linarith [htrace, hwedge, hray]

/-! ## Layer 6 — the privacy-free zero ending and the positive bridge -/

/-- **THE PRIVACY-FREE ZERO ENDING.**  When the two shifted pair weights
of a pair column vanish, the pair energy vanishes, the projected
direction dies, and the crux forbids the parallel pair.  No privacy
hypothesis enters. -/
theorem RankFourFrame.false_of_pair_shifted_weights_zero {crux : SixThreeCrux}
    (frame : RankFourFrame crux) (columnIndex : Fin 4)
    {atomU atomV : Fin 6} (hUV : atomU ≠ atomV)
    (hneU : frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0)
    (hzeroU : chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomU = 0)
    (hzeroV : chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomV = 0) : False := by
  classical
  have hdata := frame.hdata
  have hmem := frame.hmemAll columnIndex
  set pairDir := frame.tightDir (frame.basisLabel columnIndex) with hdirDef
  have hunit : pairDir atomU ^ 2 + pairDir atomV ^ 2 = 1 :=
    pair_support_unit_read hdata hmem hUV hsupp
  have henergy : pairDir ⬝ᵥ ((chartPointOfDesign crux.design).chart *ᵥ pairDir)
      = chartObjective (chartPointOfDesign crux.design)
        + ((chartPointOfDesign crux.design).weight atomU * pairDir atomU ^ 2
          + (chartPointOfDesign crux.design).weight atomV * pairDir atomV ^ 2) := by
    rw [tight_energy_read hdata hmem, pair_support_energy_read hUV hsupp]
  have henergyZero : pairDir ⬝ᵥ ((chartPointOfDesign crux.design).chart *ᵥ pairDir)
      = 0 := by
    rw [henergy]
    linear_combination (pairDir atomU ^ 2) * hzeroU + (pairDir atomV ^ 2) * hzeroV
      + (-(chartObjective (chartPointOfDesign crux.design))) * hunit
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

/-- **THE POSITIVE BRIDGE.**  The support-two closure follows from the
outer sharer kill restricted to strictly positive shifted pair weights.
A vanishing shifted weight propagates across the pair through the sign
law, and the double zero dies at the parallel-pair field. -/
theorem rankFourSupportTwoClosed_of_positive_shared_kill
    (killPositive : ∀ (crux : SixThreeCrux) (frame : RankFourFrame crux)
      (columnIndex otherIndex : Fin 4) (atomU atomV atomT : Fin 6),
      (datumTightSupport frame.tightDir (frame.basisLabel columnIndex)).card = 2 →
      atomU ≠ atomV →
      frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0 →
      frame.tightDir (frame.basisLabel columnIndex) atomV ≠ 0 →
      (∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
        frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0) →
      otherIndex ≠ columnIndex →
      atomT ≠ atomU → atomT ≠ atomV →
      frame.tightDir (frame.basisLabel otherIndex) atomT ≠ 0 →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomU →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomV →
      False) :
    RankFourSupportTwoClosed := by
  refine rankFourSupportTwoClosed_of_outer_shared_kill ?_
  intro crux frame columnIndex otherIndex atomU atomV atomT hcard hUV hneU hneV
    hsupp hneCol hTU hTV hneT
  have hdata := frame.hdata
  have hmem := frame.hmemAll columnIndex
  have hvalueNeg := frame.hvalueNeg
  have hsuppV : ∀ atomIndex, atomIndex ≠ atomV → atomIndex ≠ atomU →
      frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0 :=
    fun atomIndex hV hU => hsupp atomIndex hU hV
  by_cases hzeroU : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomU = 0
  · have hzeroV : chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomV = 0 :=
      shared_pair_zero_propagation hdata hmem (Ne.symm hUV) hneV hsuppV
        hvalueNeg hzeroU
    exact frame.false_of_pair_shifted_weights_zero columnIndex hUV hneU hsupp
      hzeroU hzeroV
  by_cases hzeroV : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomV = 0
  · have hzeroU' : chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomU = 0 :=
      shared_pair_zero_propagation hdata hmem hUV hneU hsupp hvalueNeg hzeroV
    exact hzeroU hzeroU'
  have hfloorU := capture_diagonal_nonneg_of_isChartStationaryData hdata atomU
  have hfloorV := capture_diagonal_nonneg_of_isChartStationaryData hdata atomV
  exact killPositive crux frame columnIndex otherIndex atomU atomV atomT hcard
    hUV hneU hneV hsupp hneCol hTU hTV hneT
    (lt_of_le_of_ne hfloorU (Ne.symm hzeroU))
    (lt_of_le_of_ne hfloorV (Ne.symm hzeroV))

end Gtz

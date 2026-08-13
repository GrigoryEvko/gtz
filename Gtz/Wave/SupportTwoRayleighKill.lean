import Gtz.Wave.SupportTwoClosure
import Gtz.Wave.CycleIndependentClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The support-two Rayleigh kill — the private pair dies at the frame

The census branch one gives a basis direction on a two-atom support.  This
file builds the capture Rayleigh calculus and kills the private-pair
family: the family where no other basis label touches the two pair atoms.

The mechanism, in five layers:

1. **The trace–Rayleigh bound.**  The quadratic form of a positive
   semidefinite matrix never exceeds its trace times the square norm.
   The proof sums the pair kernel probes: for each atom pair, the
   quadratic form at the pair kernel vector is nonnegative, and the
   double sum of these probes is twice the trace defect.
2. **The capture caps.**  The captured assembly `P * Xi` is positive
   semidefinite with trace `value + 1/size`.  Thus its quadratic form at
   every probe is at most `value + 1/size` times the projected square
   norm, its diagonal gives the weight floor `0 ≤ value + weight`, and
   its trace gives the floor `0 ≤ value + 1/size`.
3. **The pair-kernel collapse.**  At a private pair, the basis transpose
   kills the pair-orthogonal vector, thus the assembly and the capture
   kill it.  The capture then aligns on the pair: the capture quadratic
   of the direction reads the two capture diagonals.
4. **The squeeze.**  The capture Rayleigh cap, the weight floors, and the
   energy read force the two shifted pair weights to zero, in pure
   arithmetic.
5. **The kill.**  Zero shifted weights make the projected direction
   vanish.  A two-sparse kernel vector of the chart makes the two design
   atoms parallel, against the crux field `hasNoParallelPair`.

The closure bridge routes `RankFourSupportTwoClosed` through one named
residual: the shared-pair kill, where some other basis label carries a
pair atom.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.mulVec_pairKernelVec_apply`, `Gtz.dotProduct_mulVec_of_pair_support`
  — the pair reading calculus.
* `Gtz.quadratic_le_trace_mul_self` — **THE TRACE–RAYLEIGH BOUND.**
* `Gtz.capture_quadratic_le_of_isChartStationaryData` — **THE CAPTURE
  RAYLEIGH CAP.**
* `Gtz.capture_diagonal_nonneg_of_isChartStationaryData`,
  `Gtz.capture_trace_nonneg_of_isChartStationaryData` — the two floors.
* `Gtz.support_two_capture_squeeze` — **THE ARITHMETIC SQUEEZE.**
* `Gtz.RankFourFrame.false_of_supportTwo_private_pair` — **THE
  PRIVATE-PAIR KILL.**
* `Gtz.rankFourSupportTwoClosed_of_shared_pair_kill` — **THE CLOSURE
  BRIDGE.**

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

/-! ## Layer 1 — the pair reading calculus -/

/-- The action of a matrix on a pair kernel vector reads two columns. -/
theorem mulVec_pairKernelVec_apply {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) {atomU atomV : Fin n} (hne : atomU ≠ atomV)
    (aCoeff bCoeff : ℝ) (rowIndex : Fin n) :
    (S *ᵥ pairKernelVec aCoeff bCoeff atomU atomV) rowIndex
      = S rowIndex atomU * bCoeff - S rowIndex atomV * aCoeff := by
  classical
  have hcollapse : ∀ atomIndex : Fin n,
      S rowIndex atomIndex * pairKernelVec aCoeff bCoeff atomU atomV atomIndex
      = (if atomIndex = atomU then S rowIndex atomU * bCoeff else 0)
        + (if atomIndex = atomV then -(S rowIndex atomV * aCoeff) else 0) := by
    intro atomIndex
    by_cases hU : atomIndex = atomU
    · subst hU
      rw [pairKernelVec_apply_one, if_pos rfl, if_neg hne]
      ring
    by_cases hV : atomIndex = atomV
    · subst hV
      rw [pairKernelVec_apply_two hne, if_neg hU, if_pos rfl]
      ring
    · rw [pairKernelVec_apply_off hU hV, if_neg hU, if_neg hV]
      ring
  show (∑ atomIndex : Fin n,
      S rowIndex atomIndex * pairKernelVec aCoeff bCoeff atomU atomV atomIndex) = _
  rw [Finset.sum_congr rfl fun atomIndex _ => hcollapse atomIndex,
    Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ atomU,
    Finset.sum_ite_eq' Finset.univ atomV]
  simp only [Finset.mem_univ, if_pos]
  ring

/-- The quadratic form of a pair-supported vector reads the four corner
entries. -/
theorem dotProduct_mulVec_of_pair_support {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) {atomU atomV : Fin n} (hne : atomU ≠ atomV)
    {q : Fin n → ℝ}
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV → q atomIndex = 0) :
    q ⬝ᵥ (S *ᵥ q)
      = q atomU * (S atomU atomU * q atomU + S atomU atomV * q atomV)
        + q atomV * (S atomV atomU * q atomU + S atomV atomV * q atomV) := by
  classical
  have hrow : ∀ rowIndex : Fin n, (S *ᵥ q) rowIndex
      = S rowIndex atomU * q atomU + S rowIndex atomV * q atomV := by
    intro rowIndex
    have hterm : ∀ atomIndex : Fin n, S rowIndex atomIndex * q atomIndex
        = (if atomIndex = atomU then S rowIndex atomU * q atomU else 0)
          + (if atomIndex = atomV then S rowIndex atomV * q atomV else 0) := by
      intro atomIndex
      by_cases hU : atomIndex = atomU
      · subst hU
        rw [if_pos rfl, if_neg hne]
        ring
      by_cases hV : atomIndex = atomV
      · subst hV
        rw [if_neg hU, if_pos rfl]
        ring
      · rw [hsupp atomIndex hU hV, if_neg hU, if_neg hV]
        ring
    show (∑ atomIndex : Fin n, S rowIndex atomIndex * q atomIndex) = _
    rw [Finset.sum_congr rfl fun atomIndex _ => hterm atomIndex,
      Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ atomU,
      Finset.sum_ite_eq' Finset.univ atomV]
    simp only [Finset.mem_univ, if_pos]
  have houter : ∀ atomIndex : Fin n, q atomIndex * (S *ᵥ q) atomIndex
      = (if atomIndex = atomU then q atomU * (S *ᵥ q) atomU else 0)
        + (if atomIndex = atomV then q atomV * (S *ᵥ q) atomV else 0) := by
    intro atomIndex
    by_cases hU : atomIndex = atomU
    · subst hU
      rw [if_pos rfl, if_neg hne]
      ring
    by_cases hV : atomIndex = atomV
    · subst hV
      rw [if_neg hU, if_pos rfl]
      ring
    · rw [hsupp atomIndex hU hV, if_neg hU, if_neg hV]
      ring
  show (∑ atomIndex : Fin n, q atomIndex * (S *ᵥ q) atomIndex) = _
  rw [Finset.sum_congr rfl fun atomIndex _ => houter atomIndex,
    Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ atomU,
    Finset.sum_ite_eq' Finset.univ atomV]
  simp only [Finset.mem_univ, if_pos]
  rw [hrow atomU, hrow atomV]

/-! ## Layer 2 — the trace–Rayleigh bound -/

/-- The plain quadratic form of a positive semidefinite real matrix is
nonnegative: the star of a real probe is the probe. -/
theorem dotProduct_mulVec_nonneg_of_posSemidef {n : ℕ}
    {S : Matrix (Fin n) (Fin n) ℝ} (hpsd : S.PosSemidef) (probe : Fin n → ℝ) :
    0 ≤ probe ⬝ᵥ (S *ᵥ probe) := by
  have hstar : star probe = probe := by
    ext atomIndex
    simp
  have hquad := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 probe
  rwa [hstar] at hquad

/-- **THE TRACE–RAYLEIGH BOUND.**  The quadratic form of a positive
semidefinite matrix never exceeds the trace times the square norm.  The
double sum of the pair kernel probes is twice the trace defect. -/
theorem quadratic_le_trace_mul_self {n : ℕ}
    {S : Matrix (Fin n) (Fin n) ℝ} (hpsd : S.PosSemidef) (probe : Fin n → ℝ) :
    probe ⬝ᵥ (S *ᵥ probe) ≤ Matrix.trace S * (probe ⬝ᵥ probe) := by
  classical
  have hterm : ∀ atomY atomZ : Fin n,
      (0 : ℝ) ≤ probe atomZ ^ 2 * S atomY atomY
        - probe atomY * (S atomY atomZ * probe atomZ)
        - probe atomZ * (S atomZ atomY * probe atomY)
        + probe atomY ^ 2 * S atomZ atomZ := by
    intro atomY atomZ
    by_cases hne : atomY = atomZ
    · subst hne
      exact le_of_eq (by ring)
    · have hquad := dotProduct_mulVec_nonneg_of_posSemidef hpsd
        (pairKernelVec (probe atomY) (probe atomZ) atomY atomZ)
      rw [dotProduct_mulVec_of_pair_support S hne
        (fun atomIndex hOne hTwo => pairKernelVec_apply_off hOne hTwo)] at hquad
      rw [pairKernelVec_apply_one, pairKernelVec_apply_two hne] at hquad
      nlinarith [hquad]
  have hsum : (0 : ℝ) ≤ ∑ atomY : Fin n, ∑ atomZ : Fin n,
      (probe atomZ ^ 2 * S atomY atomY
        - probe atomY * (S atomY atomZ * probe atomZ)
        - probe atomZ * (S atomZ atomY * probe atomY)
        + probe atomY ^ 2 * S atomZ atomZ) :=
    Finset.sum_nonneg fun atomY _ =>
      Finset.sum_nonneg fun atomZ _ => hterm atomY atomZ
  have htrace : Matrix.trace S = ∑ atomY : Fin n, S atomY atomY := by
    simp [Matrix.trace, Matrix.diag]
  have hnormSq : probe ⬝ᵥ probe = ∑ atomZ : Fin n, probe atomZ ^ 2 :=
    dotProduct_self_eq_sum_sq probe
  have hquadSum : probe ⬝ᵥ (S *ᵥ probe)
      = ∑ atomY : Fin n, ∑ atomZ : Fin n,
          probe atomY * (S atomY atomZ * probe atomZ) := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hquadSwap : ∑ atomY : Fin n, ∑ atomZ : Fin n,
      probe atomZ * (S atomZ atomY * probe atomY)
      = probe ⬝ᵥ (S *ᵥ probe) := by
    rw [Finset.sum_comm, hquadSum]
  have hpieceA : ∀ atomY : Fin n,
      ∑ atomZ : Fin n, probe atomZ ^ 2 * S atomY atomY
      = (probe ⬝ᵥ probe) * S atomY atomY := by
    intro atomY
    rw [← Finset.sum_mul, ← hnormSq]
  have hpieceD : ∀ atomY : Fin n,
      ∑ atomZ : Fin n, probe atomY ^ 2 * S atomZ atomZ
      = probe atomY ^ 2 * Matrix.trace S := by
    intro atomY
    rw [← Finset.mul_sum, ← htrace]
  have hinner : ∀ atomY : Fin n, ∑ atomZ : Fin n,
      (probe atomZ ^ 2 * S atomY atomY
        - probe atomY * (S atomY atomZ * probe atomZ)
        - probe atomZ * (S atomZ atomY * probe atomY)
        + probe atomY ^ 2 * S atomZ atomZ)
      = (probe ⬝ᵥ probe) * S atomY atomY
        - (∑ atomZ : Fin n, probe atomY * (S atomY atomZ * probe atomZ))
        - (∑ atomZ : Fin n, probe atomZ * (S atomZ atomY * probe atomY))
        + probe atomY ^ 2 * Matrix.trace S := by
    intro atomY
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      hpieceA atomY, hpieceD atomY]
  have hpieceOuterA : ∑ atomY : Fin n, (probe ⬝ᵥ probe) * S atomY atomY
      = (probe ⬝ᵥ probe) * Matrix.trace S := by
    rw [← Finset.mul_sum, ← htrace]
  have hpieceOuterD : ∑ atomY : Fin n, probe atomY ^ 2 * Matrix.trace S
      = (probe ⬝ᵥ probe) * Matrix.trace S := by
    rw [← Finset.sum_mul, ← hnormSq]
  have houter : ∑ atomY : Fin n, ∑ atomZ : Fin n,
      (probe atomZ ^ 2 * S atomY atomY
        - probe atomY * (S atomY atomZ * probe atomZ)
        - probe atomZ * (S atomZ atomY * probe atomY)
        + probe atomY ^ 2 * S atomZ atomZ)
      = (probe ⬝ᵥ probe) * Matrix.trace S
        - (probe ⬝ᵥ (S *ᵥ probe))
        - (probe ⬝ᵥ (S *ᵥ probe))
        + (probe ⬝ᵥ probe) * Matrix.trace S := by
    rw [Finset.sum_congr rfl fun atomY _ => hinner atomY,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      hpieceOuterA, hpieceOuterD, ← hquadSum, hquadSwap]
  rw [houter] at hsum
  linarith

/-! ## Layer 3 — the capture caps -/

/-- **THE CAPTURE RAYLEIGH CAP.**  The quadratic form of the captured
assembly at every probe is at most `value + 1/size` times the projected
square norm.  The sandwich law folds the probe through the chart, and the
trace–Rayleigh bound prices the folded probe. -/
theorem capture_quadratic_le_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (probe : Fin size → ℝ) :
    probe ⬝ᵥ ((projection * chartMultiplierAssembly activeSet activeWeight tightDir)
        *ᵥ probe)
      ≤ (value + ((size : ℝ))⁻¹) * (probe ⬝ᵥ (projection *ᵥ probe)) := by
  set captureMatrix := projection * chartMultiplierAssembly activeSet activeWeight
    tightDir with hcapture
  have hpsd : captureMatrix.PosSemidef :=
    posSemidef_projection_mul_multiplier_of_isChartStationaryData hdata
  have hswap : ∀ otherVec : Fin size → ℝ,
      (projection *ᵥ probe) ⬝ᵥ otherVec = probe ⬝ᵥ (projection *ᵥ otherVec) := by
    intro otherVec
    have hvec : otherVec ᵥ* projection = projection *ᵥ otherVec := by
      rw [← Matrix.vecMul_transpose, hdata.isSymmetric]
    calc (projection *ᵥ probe) ⬝ᵥ otherVec
        = otherVec ⬝ᵥ (projection *ᵥ probe) := dotProduct_comm _ _
      _ = (otherVec ᵥ* projection) ⬝ᵥ probe := Matrix.dotProduct_mulVec _ _ _
      _ = (projection *ᵥ otherVec) ⬝ᵥ probe := by rw [hvec]
      _ = probe ⬝ᵥ (projection *ᵥ otherVec) := dotProduct_comm _ _
  have hfoldVec : captureMatrix *ᵥ (projection *ᵥ probe)
      = captureMatrix *ᵥ probe := by
    rw [Matrix.mulVec_mulVec]
    have hmul : captureMatrix * projection = captureMatrix := by
      rw [hcapture,
        projection_mul_multiplier_eq_sandwich_of_isChartStationaryData hdata,
        Matrix.mul_assoc
          (projection * chartMultiplierAssembly activeSet activeWeight tightDir),
        hdata.isIdempotent]
    rw [hmul]
  have hfold : (projection *ᵥ probe) ⬝ᵥ (captureMatrix *ᵥ (projection *ᵥ probe))
      = probe ⬝ᵥ (captureMatrix *ᵥ probe) := by
    rw [hfoldVec, hswap (captureMatrix *ᵥ probe), Matrix.mulVec_mulVec]
    have hmul : projection * captureMatrix = captureMatrix := by
      rw [hcapture, ← Matrix.mul_assoc, hdata.isIdempotent]
    rw [hmul]
  have hnorm : (projection *ᵥ probe) ⬝ᵥ (projection *ᵥ probe)
      = probe ⬝ᵥ (projection *ᵥ probe) := by
    rw [hswap (projection *ᵥ probe), Matrix.mulVec_mulVec, hdata.isIdempotent]
  have hbound := quadratic_le_trace_mul_self hpsd (projection *ᵥ probe)
  rw [hfold, hnorm,
    trace_projection_mul_multiplier_of_isChartStationaryData hdata] at hbound
  exact hbound

/-- The axis quadratic of a matrix is the diagonal entry. -/
theorem single_dotProduct_mulVec_single {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (atomIndex : Fin n) :
    Pi.single atomIndex (1 : ℝ) ⬝ᵥ (A *ᵥ Pi.single atomIndex 1)
      = A atomIndex atomIndex := by
  rw [single_dotProduct, one_mul, Matrix.mulVec_single_one]
  simp [Matrix.col]

/-- **THE POINTWISE CAPTURE CAP.**  At every atom, the shifted weight
over `size` is at most `value + 1/size` times the chart diagonal.  This
is the ambient diagonal bound for the shared families. -/
theorem capture_diagonal_le_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    (value + weight atomIndex) * ((size : ℝ))⁻¹
      ≤ (value + ((size : ℝ))⁻¹) * projection atomIndex atomIndex := by
  have hcap := capture_quadratic_le_of_isChartStationaryData hdata
    (Pi.single atomIndex 1)
  rwa [single_dotProduct_mulVec_single, single_dotProduct_mulVec_single,
    diagonal_projection_mul_multiplier_of_isChartStationaryData hdata atomIndex]
    at hcap

/-- **THE WEIGHT FLOOR.**  The captured diagonal is nonnegative: every
weight is at least the negative of the value. -/
theorem capture_diagonal_nonneg_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    0 ≤ value + weight atomIndex := by
  have hpsd :=
    posSemidef_projection_mul_multiplier_of_isChartStationaryData hdata
  have hdiag := hpsd.diag_nonneg (i := atomIndex)
  rw [diagonal_projection_mul_multiplier_of_isChartStationaryData hdata atomIndex]
    at hdiag
  have hinv : (0 : ℝ) < ((size : ℝ))⁻¹ :=
    inv_pos.mpr (size_cast_pos_of_isChartStationaryData hdata)
  nlinarith [hdiag, hinv]

/-- **THE TRACE FLOOR.**  The captured trace is nonnegative: the value is
at least the negative of `1/size`. -/
theorem capture_trace_nonneg_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    0 ≤ value + ((size : ℝ))⁻¹ := by
  have hpsd :=
    posSemidef_projection_mul_multiplier_of_isChartStationaryData hdata
  have htrace := hpsd.trace_nonneg
  rwa [trace_projection_mul_multiplier_of_isChartStationaryData hdata] at htrace

/-! ## Layer 4 — the pair collapse reads -/

/-- The unit norm of a pair-supported direction collapses to the two pair
squares. -/
theorem pair_support_unit_read
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hne : atomU ≠ atomV)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    tightDir label atomU ^ 2 + tightDir label atomV ^ 2 = 1 := by
  classical
  have hunit : ∑ atomIndex : Fin size, tightDir label atomIndex ^ 2 = 1 := by
    rw [← dotProduct_self_eq_sum_sq, hdata.tightDir_unit label hmem]
  have hpairSum : ∑ atomIndex ∈ ({atomU, atomV} : Finset (Fin size)),
      tightDir label atomIndex ^ 2
      = ∑ atomIndex : Fin size, tightDir label atomIndex ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomIndex _ hnot
    have hne1 : atomIndex ≠ atomU := fun heq =>
      hnot (heq ▸ Finset.mem_insert_self _ _)
    have hne2 : atomIndex ≠ atomV := fun heq =>
      hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [hsupp atomIndex hne1 hne2]
    ring
  rw [← hunit, ← hpairSum, Finset.sum_pair hne]

/-- The weighted energy of a pair-supported direction collapses to the two
pair atoms. -/
theorem pair_support_energy_read
    {atomU atomV : Fin size} (hne : atomU ≠ atomV)
    {label : activeIndex}
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) (weightVec : Fin size → ℝ) :
    ∑ atomIndex : Fin size, weightVec atomIndex * tightDir label atomIndex ^ 2
      = weightVec atomU * tightDir label atomU ^ 2
        + weightVec atomV * tightDir label atomV ^ 2 := by
  classical
  have hpairSum : ∑ atomIndex ∈ ({atomU, atomV} : Finset (Fin size)),
      weightVec atomIndex * tightDir label atomIndex ^ 2
      = ∑ atomIndex : Fin size,
          weightVec atomIndex * tightDir label atomIndex ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomIndex _ hnot
    have hne1 : atomIndex ≠ atomU := fun heq =>
      hnot (heq ▸ Finset.mem_insert_self _ _)
    have hne2 : atomIndex ≠ atomV := fun heq =>
      hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [hsupp atomIndex hne1 hne2]
    ring
  rw [← hpairSum, Finset.sum_pair hne]

/-! ## Layer 5 — the arithmetic squeeze -/

/-- **THE ARITHMETIC SQUEEZE.**  The capture Rayleigh cap, the two weight
floors, the trace floor, and the energy read force the two shifted pair
weights to zero.  The first stage kills the smaller shifted weight, and
the second stage kills the other one through the strict pair square. -/
theorem support_two_capture_squeeze
    {value invSize weightOne weightTwo squareOne squareTwo quadCapture quadChart : ℝ}
    (hvalue : value < 0) (hinv : 0 < invSize)
    (htraceFloor : 0 ≤ value + invSize)
    (hfloorOne : 0 ≤ value + weightOne) (hfloorTwo : 0 ≤ value + weightTwo)
    (hsquareOne : 0 ≤ squareOne) (hsquareTwo : 0 < squareTwo)
    (hunit : squareOne + squareTwo = 1)
    (hchart : quadChart = value
      + (weightOne * squareOne + weightTwo * squareTwo))
    (hcapture : quadCapture
      = ((value + weightOne) + (value + weightTwo)) * invSize)
    (hrayleigh : quadCapture ≤ (value + invSize) * quadChart)
    (horder : weightOne ≤ weightTwo) :
    value + weightOne = 0 ∧ value + weightTwo = 0 := by
  have hchartLe : quadChart ≤ value + weightTwo := by nlinarith
  have hchainOne : ((value + weightOne) + (value + weightTwo)) * invSize
      ≤ (value + invSize) * (value + weightTwo) := by
    rw [← hcapture]
    exact le_trans hrayleigh (mul_le_mul_of_nonneg_left hchartLe htraceFloor)
  have hstageOne : value + weightOne ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hprodOne := mul_pos hpos hinv
    have hprodTwo : value * (value + weightTwo) ≤ 0 := by
      nlinarith [hfloorTwo, hvalue.le]
    nlinarith [hchainOne, hprodOne, hprodTwo]
  have hzeroOne : value + weightOne = 0 := le_antisymm hstageOne hfloorOne
  have hchartEq : quadChart = squareTwo * (value + weightTwo) := by
    have hweightOne : weightOne = -value := by linarith
    rw [hchart, hweightOne]
    nlinarith [hunit]
  have hstageTwo : value + weightTwo ≤ 0 := by
    by_contra hposTwo
    push Not at hposTwo
    have hchainTwo : (value + weightTwo) * invSize
        ≤ (value + invSize) * (squareTwo * (value + weightTwo)) := by
      have hrw : quadCapture = (value + weightTwo) * invSize := by
        rw [hcapture, hzeroOne]
        ring
      rw [← hrw, ← hchartEq]
      exact hrayleigh
    have hfactor : 0 < invSize * squareOne - value * squareTwo := by
      nlinarith [mul_nonneg hinv.le hsquareOne,
        mul_pos (neg_pos.mpr hvalue) hsquareTwo]
    have hrewrite : (value + weightTwo) * invSize
        - (value + invSize) * (squareTwo * (value + weightTwo))
        = (value + weightTwo) * (invSize * squareOne - value * squareTwo) := by
      linear_combination (-((value + weightTwo) * invSize)) * hunit
    have hprod := mul_pos hposTwo hfactor
    nlinarith [hchainTwo, hrewrite, hprod]
  exact ⟨hzeroOne, le_antisymm hstageTwo hfloorTwo⟩

/-! ## Layer 6 — the private-pair kill -/

/-- A vanishing projection energy kills the projected direction: the
square norm of the projected vector is the energy. -/
theorem projection_mulVec_eq_zero_of_energy_eq_zero
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex}
    (henergy : tightDir label ⬝ᵥ (projection *ᵥ tightDir label) = 0) :
    projection *ᵥ tightDir label = 0 := by
  classical
  have hnorm := projection_energy_eq hdata label
  rw [henergy] at hnorm
  have hsum : ∑ atomIndex : Fin size,
      (projection *ᵥ tightDir label) atomIndex ^ 2 = 0 := by
    rw [← dotProduct_self_eq_sum_sq, ← hnorm]
  funext atomIndex
  have hnonneg : ∀ otherIndex ∈ (Finset.univ : Finset (Fin size)),
      0 ≤ (projection *ᵥ tightDir label) otherIndex ^ 2 :=
    fun otherIndex _ => sq_nonneg _
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum atomIndex
    (Finset.mem_univ atomIndex)
  have hcoord := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
  simpa using hcoord

/-- **THE PRIVATE-PAIR KILL.**  A basis direction on a two-atom support
that no other basis label touches dies at every frame.  The pair-kernel
collapse aligns the capture on the pair, the squeeze zeroes the two
shifted weights, and the vanishing projected direction makes the two
design atoms parallel. -/
theorem RankFourFrame.false_of_supportTwo_private_pair {crux : SixThreeCrux}
    (frame : RankFourFrame crux) (columnIndex : Fin 4)
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
  -- The basis transpose annihilates the pair kernel vector.
  have hbasisKernel : (tightBasisColumns frame.tightDir frame.basisLabel)ᵀ
      *ᵥ pairKernelVec (pairDir atomU) (pairDir atomV) atomU atomV = 0 := by
    apply basis_transpose_mulVec_pairKernelVec hUV
    intro slotIndex
    by_cases hslot : slotIndex = columnIndex
    · subst hslot
      ring
    · rw [hprivU slotIndex hslot, hprivV slotIndex hslot]
      ring
  -- The assembly and the capture annihilate the pair kernel vector.
  have hassemblyKernel : chartMultiplierAssembly frame.activeSet frame.reducedWeight
      frame.tightDir *ᵥ pairKernelVec (pairDir atomU) (pairDir atomV) atomU atomV
      = 0 :=
    assembly_mulVec_of_basis_transpose_zero frame.hHform hbasisKernel
  have hcaptureKernel : ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
      *ᵥ pairKernelVec (pairDir atomU) (pairDir atomV) atomU atomV = 0 := by
    rw [← Matrix.mulVec_mulVec, hassemblyKernel, Matrix.mulVec_zero]
  -- The two alignment identities on the pair.
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
  -- The unit read on the pair.
  have hunit : pairDir atomU ^ 2 + pairDir atomV ^ 2 = 1 :=
    pair_support_unit_read hdata hmem hUV hsupp
  -- The capture quadratic reads the two capture diagonals.
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
  -- The two capture diagonals are the shifted weights over six.
  have hdiagU := diagonal_projection_mul_multiplier_of_isChartStationaryData
    hdata atomU
  have hdiagV := diagonal_projection_mul_multiplier_of_isChartStationaryData
    hdata atomV
  -- The Rayleigh cap at the pair direction.
  have hrayleigh := capture_quadratic_le_of_isChartStationaryData hdata pairDir
  -- The energy read of the chart quadratic.
  have henergy : pairDir ⬝ᵥ ((chartPointOfDesign crux.design).chart *ᵥ pairDir)
      = chartObjective (chartPointOfDesign crux.design)
        + ((chartPointOfDesign crux.design).weight atomU * pairDir atomU ^ 2
          + (chartPointOfDesign crux.design).weight atomV * pairDir atomV ^ 2) := by
    have hread := tight_energy_read hdata hmem
    rw [hread, pair_support_energy_read hUV hsupp]
  -- The floors.
  have hfloorU := capture_diagonal_nonneg_of_isChartStationaryData hdata atomU
  have hfloorV := capture_diagonal_nonneg_of_isChartStationaryData hdata atomV
  have htraceFloor := capture_trace_nonneg_of_isChartStationaryData hdata
  have hinv : (0 : ℝ) < (((6 : ℕ) : ℝ))⁻¹ := by norm_num
  have hsqU : (0 : ℝ) < pairDir atomU ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hneU))
  have hsqV : (0 : ℝ) < pairDir atomV ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hneV))
  -- The squeeze, ordered by the two pair weights.
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
  -- The projected direction vanishes.
  have henergyZero : pairDir ⬝ᵥ ((chartPointOfDesign crux.design).chart *ᵥ pairDir)
      = 0 := by
    rw [henergy]
    nlinarith [hbothZero.1, hbothZero.2, hunit]
  have hprojZero : (chartPointOfDesign crux.design).chart *ᵥ pairDir = 0 :=
    projection_mulVec_eq_zero_of_energy_eq_zero hdata henergyZero
  -- The pair direction is a pair kernel vector of the chart.
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

/-! ## The closure bridge -/

/-- **THE CLOSURE BRIDGE.**  The support-two closure follows from one
named residual: the shared-pair kill.  At every frame with a card-two
basis support, the pair is private and dies here, or some other basis
label carries a pair atom and the residual kill closes it. -/
theorem rankFourSupportTwoClosed_of_shared_pair_kill
    (killShared : ∀ (crux : SixThreeCrux) (frame : RankFourFrame crux)
      (columnIndex otherIndex : Fin 4) (atomU atomV : Fin 6),
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
    RankFourSupportTwoClosed := by
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

end Gtz

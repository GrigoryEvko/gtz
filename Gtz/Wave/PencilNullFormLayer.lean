import Gtz.Wave.CoefficientEngineCore
import Gtz.Wave.RankFourRungAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The pencil null-form layer — the H-layer endgame of the commutation kills

The vertex systems of the engine core are not sufficient: the K4 vertex
system escapes through the heavy-edge wedge, and the doubled-cycle vertex
system is feasible outright.  The missing layer is the PENCIL: at every
two-carrier atom, the captured core `X = M H` and the Gram core `H` share
one null direction of the shifted pencil `X - d H`, where `d` is the
shifted weight of the atom.  The null direction is the carrier coordinate
pair itself, and the pencil inherits the exchange symmetry.

The layers, from the bottom:

1. **The scalar null-form law.**  A real symmetric two-by-two form with a
   nonzero null vector has a nonpositive determinant.  The proof is one
   polynomial identity: `(a u + b v)^2 = (b^2 - a c) v^2` on the null
   vector.
2. **The pair pencil identity.**  The capture pair form minus `d` times
   the Gram pair form is zero: the two landed two-carrier dictionary
   instantiations subtract, and the free carrier scale cancels.  With the
   capture symmetry the identity becomes a genuine symmetric null form.
3. **The pencil corner inequality.**  Layers one and two give, at every
   two-carrier atom with carrier pair `(i, j)`:
   `(X_ii - d H_ii) (X_jj - d H_jj) <= (X_ij - d H_ij)^2`.
4. **The doubled-pair eigenpair laws.**  Two atoms on one carrier pair
   are two left eigenvectors of the coefficient corner.  The four scaled
   solves are division-free, and the two unconditional laws follow:
   `(trace - d - d') * crossDet = 0` and
   `(det - d d') * crossDet^2 = 0`.  A nonzero cross determinant thus
   reads the corner spectrum exactly — the consistency layer that the
   doubled-cycle kill consumes.
5. **The frame lifts.**  The capture symmetry, the pencil identity, the
   corner inequality, and the eigenpair laws, all at a `RankFourFrame`.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.null_vector_det_nonpos` — **THE SCALAR LAW.**
* `Gtz.pair_pencil_identity_raw`, `Gtz.pair_pencil_identity` — **THE
  PENCIL.**
* `Gtz.pair_pencil_det_nonpos` — **THE CORNER INEQUALITY.**
* `Gtz.doubled_pair_diag_solve_left`, `Gtz.doubled_pair_diag_solve_right`,
  `Gtz.doubled_pair_offdiag_solve_left`,
  `Gtz.doubled_pair_offdiag_solve_right` — the four scaled solves.
* `Gtz.doubled_pair_trace_law`, `Gtz.doubled_pair_det_law` — **THE
  EIGENPAIR LAWS.**
* `Gtz.doubled_pair_corner_spectrum` — the spectrum reading at a nonzero
  cross determinant.
* `Gtz.RankFourFrame.captureSymm`, `Gtz.RankFourFrame.pair_pencil`,
  `Gtz.RankFourFrame.pair_pencil_det_nonpos`,
  `Gtz.RankFourFrame.doubled_pair_trace`,
  `Gtz.RankFourFrame.doubled_pair_det` — **THE FRAME LIFTS.**

## Vacuity

Nothing here quantifies over a crux alone: every statement holds at each
stationary datum with a chosen basis, and the scalar law is unconditional.
The frame statements are vacuous if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the scalar null-form law -/

/-- **THE SCALAR NULL-FORM LAW.**  A real symmetric two-by-two form with a
nonzero null vector has a nonpositive determinant: `a c <= b^2`. -/
theorem null_vector_det_nonpos {a b c u v : ℝ}
    (hform : a * u ^ 2 + 2 * b * (u * v) + c * v ^ 2 = 0) (hne : u ≠ 0) :
    a * c ≤ b ^ 2 := by
  by_cases hv : v = 0
  · have hzero : a * u ^ 2 = 0 := by
      rw [hv] at hform
      linarith [hform]
    have ha : a = 0 := by
      have husq : u ^ 2 ≠ 0 := pow_ne_zero 2 hne
      exact (mul_eq_zero.mp hzero).resolve_right husq
    rw [ha, zero_mul]
    exact sq_nonneg b
  · have hkey : (a * u + b * v) ^ 2 = (b ^ 2 - a * c) * v ^ 2 := by
      linear_combination a * hform
    have hvsq : 0 < v ^ 2 := by positivity
    nlinarith [sq_nonneg (a * u + b * v), hkey, hvsq]

/-- The mirrored scalar law: the nonzero coordinate can sit second. -/
theorem null_vector_det_nonpos' {a b c u v : ℝ}
    (hform : a * u ^ 2 + 2 * b * (u * v) + c * v ^ 2 = 0) (hne : v ≠ 0) :
    a * c ≤ b ^ 2 := by
  have hswap : c * v ^ 2 + 2 * b * (v * u) + a * u ^ 2 = 0 := by
    linear_combination hform
  have hresult := null_vector_det_nonpos hswap hne
  linarith [hresult]

/-! ## Layer 2 — the pair pencil identity -/

/-- **THE RAW PENCIL.**  At a two-carrier atom, the capture pair form
minus the shifted weight times the Gram pair form vanishes: the two
dictionary instantiations subtract, and the constant diagonals cancel. -/
theorem pair_pencil_identity_raw
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    {firstSlot secondSlot : Fin basisCount} (hne : firstSlot ≠ secondSlot)
    {sharedAtom : Fin size}
    (hcarriers : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) sharedAtom = 0) :
    tightDir (basisLabel firstSlot) sharedAtom
        * tightDir (basisLabel firstSlot) sharedAtom
        * ((M * H) firstSlot firstSlot
          - (value + weight sharedAtom) * H firstSlot firstSlot)
      + tightDir (basisLabel firstSlot) sharedAtom
        * tightDir (basisLabel secondSlot) sharedAtom
        * (((M * H) firstSlot secondSlot
            - (value + weight sharedAtom) * H firstSlot secondSlot)
          + ((M * H) secondSlot firstSlot
            - (value + weight sharedAtom) * H secondSlot firstSlot))
      + tightDir (basisLabel secondSlot) sharedAtom
        * tightDir (basisLabel secondSlot) sharedAtom
        * ((M * H) secondSlot secondSlot
          - (value + weight sharedAtom) * H secondSlot secondSlot) = 0 := by
  have hgram := two_carrier_gram_eq_inv_size hdata basisLabel hHform hne hcarriers
  have hcapture := two_carrier_capture_eq_forced_diagonal hdata basisLabel
    hrepresentation hHform hne hcarriers
  linear_combination hcapture - (value + weight sharedAtom) * hgram

/-- **THE PENCIL.**  The symmetric form of the raw identity: with the
exchange law and the Gram symmetry, the mixed pencil entries agree, and
the identity becomes a null form of the symmetric pencil
`X - d H` at the carrier coordinates. -/
theorem pair_pencil_identity
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    (hsymm : Hᵀ = H) (hexchange : M * H = H * Mᵀ)
    {firstSlot secondSlot : Fin basisCount} (hne : firstSlot ≠ secondSlot)
    {sharedAtom : Fin size}
    (hcarriers : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) sharedAtom = 0) :
    ((M * H) firstSlot firstSlot
        - (value + weight sharedAtom) * H firstSlot firstSlot)
        * tightDir (basisLabel firstSlot) sharedAtom ^ 2
      + 2 * ((M * H) firstSlot secondSlot
          - (value + weight sharedAtom) * H firstSlot secondSlot)
        * (tightDir (basisLabel firstSlot) sharedAtom
          * tightDir (basisLabel secondSlot) sharedAtom)
      + ((M * H) secondSlot secondSlot
          - (value + weight sharedAtom) * H secondSlot secondSlot)
        * tightDir (basisLabel secondSlot) sharedAtom ^ 2 = 0 := by
  have hraw := pair_pencil_identity_raw hdata basisLabel hrepresentation hHform
    hne hcarriers
  have hXsymm : (M * H) secondSlot firstSlot = (M * H) firstSlot secondSlot :=
    (capture_entry_symm hsymm hexchange firstSlot secondSlot).symm
  have hHsymm : H secondSlot firstSlot = H firstSlot secondSlot := by
    have hentry := congrFun (congrFun hsymm firstSlot) secondSlot
    rw [Matrix.transpose_apply] at hentry
    exact hentry
  linear_combination hraw
    - (tightDir (basisLabel firstSlot) sharedAtom
        * tightDir (basisLabel secondSlot) sharedAtom) * hXsymm
    + ((value + weight sharedAtom)
        * (tightDir (basisLabel firstSlot) sharedAtom
          * tightDir (basisLabel secondSlot) sharedAtom)) * hHsymm

/-! ## Layer 3 — the pencil corner inequality -/

/-- **THE PENCIL CORNER INEQUALITY.**  At every two-carrier atom with a
nonzero first carrier coordinate, the shifted-pencil corner determinant is
nonpositive:

    `(X_ii - d H_ii) (X_jj - d H_jj) <= (X_ij - d H_ij)^2` .

This is the non-diagonal generalization of the corner window: no diagonal
Gram hypothesis enters. -/
theorem pair_pencil_det_nonpos
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    (hsymm : Hᵀ = H) (hexchange : M * H = H * Mᵀ)
    {firstSlot secondSlot : Fin basisCount} (hne : firstSlot ≠ secondSlot)
    {sharedAtom : Fin size}
    (hcarriers : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) sharedAtom = 0)
    (hfirstNe : tightDir (basisLabel firstSlot) sharedAtom ≠ 0) :
    ((M * H) firstSlot firstSlot
        - (value + weight sharedAtom) * H firstSlot firstSlot)
        * ((M * H) secondSlot secondSlot
          - (value + weight sharedAtom) * H secondSlot secondSlot)
      ≤ ((M * H) firstSlot secondSlot
          - (value + weight sharedAtom) * H firstSlot secondSlot) ^ 2 :=
  null_vector_det_nonpos
    (pair_pencil_identity hdata basisLabel hrepresentation hHform hsymm
      hexchange hne hcarriers) hfirstNe

/-! ## Layer 4 — the doubled-pair eigenpair laws -/

section DoubledPair

variable {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
variable {firstSlot secondSlot : Fin basisCount}
variable {firstAtom secondAtom : Fin size}

/-- The cross determinant of two atoms on one carrier pair. -/
noncomputable def pairCrossDet (tightDir : activeIndex → (Fin size → ℝ))
    (basisLabel : Fin basisCount → activeIndex)
    (firstSlot secondSlot : Fin basisCount)
    (firstAtom secondAtom : Fin size) : ℝ :=
  tightDir (basisLabel firstSlot) firstAtom
      * tightDir (basisLabel secondSlot) secondAtom
    - tightDir (basisLabel firstSlot) secondAtom
      * tightDir (basisLabel secondSlot) firstAtom

/-- The first diagonal solve: the cross determinant times the first corner
diagonal is a polynomial in the carrier coordinates and the shifted
weights.  Division-free. -/
theorem doubled_pair_diag_solve_left
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hne : firstSlot ≠ secondSlot)
    (hmemFirst : basisLabel firstSlot ∈ activeSet)
    (hatomFirst : firstAtom ∈ activeSubset (basisLabel firstSlot))
    (hatomSecond : secondAtom ∈ activeSubset (basisLabel firstSlot))
    (hcarriersFirst : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) firstAtom = 0)
    (hcarriersSecond : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) secondAtom = 0) :
    M firstSlot firstSlot
        * pairCrossDet tightDir basisLabel firstSlot secondSlot firstAtom secondAtom
      = (value + weight firstAtom)
          * (tightDir (basisLabel firstSlot) firstAtom
            * tightDir (basisLabel secondSlot) secondAtom)
        - (value + weight secondAtom)
          * (tightDir (basisLabel firstSlot) secondAtom
            * tightDir (basisLabel secondSlot) firstAtom) := by
  have hrowFirst := two_carrier_row_reading hdata basisLabel hrepresentation
    hne hmemFirst hatomFirst hcarriersFirst
  have hrowSecond := two_carrier_row_reading hdata basisLabel hrepresentation
    hne hmemFirst hatomSecond hcarriersSecond
  rw [pairCrossDet]
  linear_combination tightDir (basisLabel secondSlot) secondAtom * hrowFirst
    - tightDir (basisLabel secondSlot) firstAtom * hrowSecond

/-- The second diagonal solve, at the second slot. -/
theorem doubled_pair_diag_solve_right
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hne : firstSlot ≠ secondSlot)
    (hmemSecond : basisLabel secondSlot ∈ activeSet)
    (hatomFirst : firstAtom ∈ activeSubset (basisLabel secondSlot))
    (hatomSecond : secondAtom ∈ activeSubset (basisLabel secondSlot))
    (hcarriersFirst : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) firstAtom = 0)
    (hcarriersSecond : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) secondAtom = 0) :
    M secondSlot secondSlot
        * pairCrossDet tightDir basisLabel firstSlot secondSlot firstAtom secondAtom
      = (value + weight secondAtom)
          * (tightDir (basisLabel firstSlot) firstAtom
            * tightDir (basisLabel secondSlot) secondAtom)
        - (value + weight firstAtom)
          * (tightDir (basisLabel firstSlot) secondAtom
            * tightDir (basisLabel secondSlot) firstAtom) := by
  have hrowFirst := two_carrier_row_reading hdata basisLabel hrepresentation
    hne hmemSecond hatomFirst hcarriersFirst
  have hrowSecond := two_carrier_row_reading hdata basisLabel hrepresentation
    hne hmemSecond hatomSecond hcarriersSecond
  rw [pairCrossDet]
  linear_combination tightDir (basisLabel firstSlot) firstAtom * hrowSecond
    - tightDir (basisLabel firstSlot) secondAtom * hrowFirst

/-- The first off-diagonal solve: the cross determinant times the lower
corner entry reads the shifted-weight difference against the first-slot
coordinates. -/
theorem doubled_pair_offdiag_solve_left
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hne : firstSlot ≠ secondSlot)
    (hmemFirst : basisLabel firstSlot ∈ activeSet)
    (hatomFirst : firstAtom ∈ activeSubset (basisLabel firstSlot))
    (hatomSecond : secondAtom ∈ activeSubset (basisLabel firstSlot))
    (hcarriersFirst : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) firstAtom = 0)
    (hcarriersSecond : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) secondAtom = 0) :
    M secondSlot firstSlot
        * pairCrossDet tightDir basisLabel firstSlot secondSlot firstAtom secondAtom
      = ((value + weight secondAtom) - (value + weight firstAtom))
        * (tightDir (basisLabel firstSlot) firstAtom
          * tightDir (basisLabel firstSlot) secondAtom) := by
  have hrowFirst := two_carrier_row_reading hdata basisLabel hrepresentation
    hne hmemFirst hatomFirst hcarriersFirst
  have hrowSecond := two_carrier_row_reading hdata basisLabel hrepresentation
    hne hmemFirst hatomSecond hcarriersSecond
  rw [pairCrossDet]
  linear_combination tightDir (basisLabel firstSlot) firstAtom * hrowSecond
    - tightDir (basisLabel firstSlot) secondAtom * hrowFirst

/-- The second off-diagonal solve, mirrored. -/
theorem doubled_pair_offdiag_solve_right
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hne : firstSlot ≠ secondSlot)
    (hmemSecond : basisLabel secondSlot ∈ activeSet)
    (hatomFirst : firstAtom ∈ activeSubset (basisLabel secondSlot))
    (hatomSecond : secondAtom ∈ activeSubset (basisLabel secondSlot))
    (hcarriersFirst : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) firstAtom = 0)
    (hcarriersSecond : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) secondAtom = 0) :
    M firstSlot secondSlot
        * pairCrossDet tightDir basisLabel firstSlot secondSlot firstAtom secondAtom
      = ((value + weight firstAtom) - (value + weight secondAtom))
        * (tightDir (basisLabel secondSlot) firstAtom
          * tightDir (basisLabel secondSlot) secondAtom) := by
  have hrowFirst := two_carrier_row_reading hdata basisLabel hrepresentation
    hne hmemSecond hatomFirst hcarriersFirst
  have hrowSecond := two_carrier_row_reading hdata basisLabel hrepresentation
    hne hmemSecond hatomSecond hcarriersSecond
  rw [pairCrossDet]
  linear_combination tightDir (basisLabel secondSlot) secondAtom * hrowFirst
    - tightDir (basisLabel secondSlot) firstAtom * hrowSecond

/-- **THE EIGENPAIR TRACE LAW.**  Unconditional: the corner trace deficit
against the two shifted weights is annihilated by the cross determinant.
Two atoms on one pair are two left eigenvectors of the corner. -/
theorem doubled_pair_trace_law
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hne : firstSlot ≠ secondSlot)
    (hmemFirst : basisLabel firstSlot ∈ activeSet)
    (hmemSecond : basisLabel secondSlot ∈ activeSet)
    (hatomFF : firstAtom ∈ activeSubset (basisLabel firstSlot))
    (hatomFS : secondAtom ∈ activeSubset (basisLabel firstSlot))
    (hatomSF : firstAtom ∈ activeSubset (basisLabel secondSlot))
    (hatomSS : secondAtom ∈ activeSubset (basisLabel secondSlot))
    (hcarriersFirst : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) firstAtom = 0)
    (hcarriersSecond : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) secondAtom = 0) :
    (M firstSlot firstSlot + M secondSlot secondSlot
        - (value + weight firstAtom) - (value + weight secondAtom))
        * pairCrossDet tightDir basisLabel firstSlot secondSlot firstAtom secondAtom
      = 0 := by
  have hleft := doubled_pair_diag_solve_left hdata basisLabel hrepresentation
    hne hmemFirst hatomFF hatomFS hcarriersFirst hcarriersSecond
  have hright := doubled_pair_diag_solve_right hdata basisLabel hrepresentation
    hne hmemSecond hatomSF hatomSS hcarriersFirst hcarriersSecond
  rw [pairCrossDet] at hleft hright ⊢
  linear_combination hleft + hright

/-- **THE EIGENPAIR DETERMINANT LAW.**  Unconditional: the corner
determinant deficit against the product of the two shifted weights is
annihilated by the square of the cross determinant. -/
theorem doubled_pair_det_law
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hne : firstSlot ≠ secondSlot)
    (hmemFirst : basisLabel firstSlot ∈ activeSet)
    (hmemSecond : basisLabel secondSlot ∈ activeSet)
    (hatomFF : firstAtom ∈ activeSubset (basisLabel firstSlot))
    (hatomFS : secondAtom ∈ activeSubset (basisLabel firstSlot))
    (hatomSF : firstAtom ∈ activeSubset (basisLabel secondSlot))
    (hatomSS : secondAtom ∈ activeSubset (basisLabel secondSlot))
    (hcarriersFirst : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) firstAtom = 0)
    (hcarriersSecond : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) secondAtom = 0) :
    (M firstSlot firstSlot * M secondSlot secondSlot
        - M firstSlot secondSlot * M secondSlot firstSlot
        - (value + weight firstAtom) * (value + weight secondAtom))
        * pairCrossDet tightDir basisLabel firstSlot secondSlot firstAtom
            secondAtom ^ 2
      = 0 := by
  have hdiagL := doubled_pair_diag_solve_left hdata basisLabel hrepresentation
    hne hmemFirst hatomFF hatomFS hcarriersFirst hcarriersSecond
  have hdiagR := doubled_pair_diag_solve_right hdata basisLabel hrepresentation
    hne hmemSecond hatomSF hatomSS hcarriersFirst hcarriersSecond
  have hoffL := doubled_pair_offdiag_solve_left hdata basisLabel hrepresentation
    hne hmemFirst hatomFF hatomFS hcarriersFirst hcarriersSecond
  have hoffR := doubled_pair_offdiag_solve_right hdata basisLabel hrepresentation
    hne hmemSecond hatomSF hatomSS hcarriersFirst hcarriersSecond
  rw [pairCrossDet] at hdiagL hdiagR hoffL hoffR ⊢
  linear_combination
    (M secondSlot secondSlot
        * (tightDir (basisLabel firstSlot) firstAtom
            * tightDir (basisLabel secondSlot) secondAtom
          - tightDir (basisLabel firstSlot) secondAtom
            * tightDir (basisLabel secondSlot) firstAtom)) * hdiagL
    + ((value + weight firstAtom)
          * (tightDir (basisLabel firstSlot) firstAtom
            * tightDir (basisLabel secondSlot) secondAtom)
        - (value + weight secondAtom)
          * (tightDir (basisLabel firstSlot) secondAtom
            * tightDir (basisLabel secondSlot) firstAtom)) * hdiagR
    - (M firstSlot secondSlot
        * (tightDir (basisLabel firstSlot) firstAtom
            * tightDir (basisLabel secondSlot) secondAtom
          - tightDir (basisLabel firstSlot) secondAtom
            * tightDir (basisLabel secondSlot) firstAtom)) * hoffL
    - (((value + weight secondAtom) - (value + weight firstAtom))
        * (tightDir (basisLabel firstSlot) firstAtom
          * tightDir (basisLabel firstSlot) secondAtom)) * hoffR

/-- **THE CORNER SPECTRUM.**  At a nonzero cross determinant, the corner
trace and the corner determinant read the two shifted weights exactly:
the two atoms are two independent left eigenvectors. -/
theorem doubled_pair_corner_spectrum
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hne : firstSlot ≠ secondSlot)
    (hmemFirst : basisLabel firstSlot ∈ activeSet)
    (hmemSecond : basisLabel secondSlot ∈ activeSet)
    (hatomFF : firstAtom ∈ activeSubset (basisLabel firstSlot))
    (hatomFS : secondAtom ∈ activeSubset (basisLabel firstSlot))
    (hatomSF : firstAtom ∈ activeSubset (basisLabel secondSlot))
    (hatomSS : secondAtom ∈ activeSubset (basisLabel secondSlot))
    (hcarriersFirst : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) firstAtom = 0)
    (hcarriersSecond : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot → tightDir (basisLabel columnIndex) secondAtom = 0)
    (hdet : pairCrossDet tightDir basisLabel firstSlot secondSlot firstAtom
      secondAtom ≠ 0) :
    M firstSlot firstSlot + M secondSlot secondSlot
        = (value + weight firstAtom) + (value + weight secondAtom)
      ∧ M firstSlot firstSlot * M secondSlot secondSlot
          - M firstSlot secondSlot * M secondSlot firstSlot
        = (value + weight firstAtom) * (value + weight secondAtom) := by
  have htrace := doubled_pair_trace_law hdata basisLabel hrepresentation hne
    hmemFirst hmemSecond hatomFF hatomFS hatomSF hatomSS hcarriersFirst
    hcarriersSecond
  have hdetLaw := doubled_pair_det_law hdata basisLabel hrepresentation hne
    hmemFirst hmemSecond hatomFF hatomFS hatomSF hatomSS hcarriersFirst
    hcarriersSecond
  have hsqNe : pairCrossDet tightDir basisLabel firstSlot secondSlot firstAtom
      secondAtom ^ 2 ≠ 0 := pow_ne_zero 2 hdet
  constructor
  · have hfactor := mul_eq_zero.mp htrace
    have hzero := hfactor.resolve_right hdet
    linarith [hzero]
  · have hfactor := mul_eq_zero.mp hdetLaw
    have hzero := hfactor.resolve_right hsqNe
    linarith [hzero]

end DoubledPair

/-! ## Layer 5 — the frame lifts -/

namespace RankFourFrame

variable {crux : SixThreeCrux} (frame : RankFourFrame crux)

/-- The captured core of a frame is symmetric: the exchange law and the
Gram symmetry combine. -/
theorem captureSymm : (frame.coeff * frame.gram)ᵀ = frame.coeff * frame.gram :=
  capture_transpose_eq frame.hsymmH frame.hexchange

/-- The pencil identity at a two-carrier atom of a frame. -/
theorem pair_pencil {firstSlot secondSlot : Fin 4} (hne : firstSlot ≠ secondSlot)
    {sharedAtom : Fin 6}
    (hcarriers : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot →
      frame.tightDir (frame.basisLabel columnIndex) sharedAtom = 0) :
    ((frame.coeff * frame.gram) firstSlot firstSlot
        - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight sharedAtom)
          * frame.gram firstSlot firstSlot)
        * frame.tightDir (frame.basisLabel firstSlot) sharedAtom ^ 2
      + 2 * ((frame.coeff * frame.gram) firstSlot secondSlot
          - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight sharedAtom)
            * frame.gram firstSlot secondSlot)
        * (frame.tightDir (frame.basisLabel firstSlot) sharedAtom
          * frame.tightDir (frame.basisLabel secondSlot) sharedAtom)
      + ((frame.coeff * frame.gram) secondSlot secondSlot
          - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight sharedAtom)
            * frame.gram secondSlot secondSlot)
        * frame.tightDir (frame.basisLabel secondSlot) sharedAtom ^ 2 = 0 :=
  pair_pencil_identity frame.hdata frame.basisLabel frame.hrepresentation
    frame.hHform frame.hsymmH frame.hexchange hne hcarriers

/-- The pencil corner inequality at a two-carrier atom of a frame. -/
theorem pair_pencil_det_nonpos {firstSlot secondSlot : Fin 4}
    (hne : firstSlot ≠ secondSlot) {sharedAtom : Fin 6}
    (hcarriers : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot →
      frame.tightDir (frame.basisLabel columnIndex) sharedAtom = 0)
    (hfirstNe : frame.tightDir (frame.basisLabel firstSlot) sharedAtom ≠ 0) :
    ((frame.coeff * frame.gram) firstSlot firstSlot
        - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight sharedAtom)
          * frame.gram firstSlot firstSlot)
        * ((frame.coeff * frame.gram) secondSlot secondSlot
          - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight sharedAtom)
            * frame.gram secondSlot secondSlot)
      ≤ ((frame.coeff * frame.gram) firstSlot secondSlot
          - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight sharedAtom)
            * frame.gram firstSlot secondSlot) ^ 2 :=
  Gtz.pair_pencil_det_nonpos frame.hdata frame.basisLabel frame.hrepresentation
    frame.hHform frame.hsymmH frame.hexchange hne hcarriers hfirstNe

/-- The eigenpair trace law at a doubled pair of a frame. -/
theorem doubled_pair_trace {firstSlot secondSlot : Fin 4}
    (hne : firstSlot ≠ secondSlot) {firstAtom secondAtom : Fin 6}
    (hatomFF : firstAtom ∈ frame.activeSubset (frame.basisLabel firstSlot))
    (hatomFS : secondAtom ∈ frame.activeSubset (frame.basisLabel firstSlot))
    (hatomSF : firstAtom ∈ frame.activeSubset (frame.basisLabel secondSlot))
    (hatomSS : secondAtom ∈ frame.activeSubset (frame.basisLabel secondSlot))
    (hcarriersFirst : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot →
      frame.tightDir (frame.basisLabel columnIndex) firstAtom = 0)
    (hcarriersSecond : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot →
      frame.tightDir (frame.basisLabel columnIndex) secondAtom = 0) :
    (frame.coeff firstSlot firstSlot + frame.coeff secondSlot secondSlot
        - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight firstAtom)
        - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight secondAtom))
        * pairCrossDet frame.tightDir frame.basisLabel firstSlot secondSlot
            firstAtom secondAtom
      = 0 :=
  doubled_pair_trace_law frame.hdata frame.basisLabel frame.hrepresentation hne
    (frame.hmemAll firstSlot) (frame.hmemAll secondSlot) hatomFF hatomFS
    hatomSF hatomSS hcarriersFirst hcarriersSecond

/-- The eigenpair determinant law at a doubled pair of a frame. -/
theorem doubled_pair_det {firstSlot secondSlot : Fin 4}
    (hne : firstSlot ≠ secondSlot) {firstAtom secondAtom : Fin 6}
    (hatomFF : firstAtom ∈ frame.activeSubset (frame.basisLabel firstSlot))
    (hatomFS : secondAtom ∈ frame.activeSubset (frame.basisLabel firstSlot))
    (hatomSF : firstAtom ∈ frame.activeSubset (frame.basisLabel secondSlot))
    (hatomSS : secondAtom ∈ frame.activeSubset (frame.basisLabel secondSlot))
    (hcarriersFirst : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot →
      frame.tightDir (frame.basisLabel columnIndex) firstAtom = 0)
    (hcarriersSecond : ∀ columnIndex, columnIndex ≠ firstSlot →
      columnIndex ≠ secondSlot →
      frame.tightDir (frame.basisLabel columnIndex) secondAtom = 0) :
    (frame.coeff firstSlot firstSlot * frame.coeff secondSlot secondSlot
        - frame.coeff firstSlot secondSlot * frame.coeff secondSlot firstSlot
        - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight firstAtom)
          * (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight secondAtom))
        * pairCrossDet frame.tightDir frame.basisLabel firstSlot secondSlot
            firstAtom secondAtom ^ 2
      = 0 :=
  doubled_pair_det_law frame.hdata frame.basisLabel frame.hrepresentation hne
    (frame.hmemAll firstSlot) (frame.hmemAll secondSlot) hatomFF hatomFS
    hatomSF hatomSS hcarriersFirst hcarriersSecond

end RankFourFrame

end Gtz

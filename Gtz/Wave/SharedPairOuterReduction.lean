import Gtz.Wave.SupportTwoRayleighKill
import Gtz.Quantitative.DiscriminantSystem

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The shared-pair outer reduction — the residual narrows to the outer sharer

The landed closure bridge routes `Gtz.RankFourSupportTwoClosed` through
the shared-pair kill: some other basis label carries a pair atom.  This
file kills the sharers that live INSIDE the pair, and narrows the
residual to the outer sharer: a label with a nonzero atom outside the
pair.

The mechanism, in five layers:

1. **The row reads.**  The action of a matrix row on a vector with one
   or two support atoms reads one or two entries.
2. **The entry Cauchy–Schwarz.**  A symmetric idempotent matrix has a
   nonnegative quadratic form.  The probe family `t e_u + e_v` prices
   the discriminant.  Thus the square of an off-diagonal entry is at
   most the product of the two diagonal entries.
3. **The gap floor.**  At an all-heavy crux, every diagonal entry of the
   stationary gap is positive.  The leverage excess prices it.
4. **The two inner kills.**  A singleton support forces one diagonal gap
   entry to the negative value, against the floor.  A second label on
   the same pair forces the two-atom gap block to a multiple of the
   identity, with the same end.  The left inverse of the basis columns
   makes the two pair restrictions independent.
5. **The narrowing window.**  The pair characteristic prices the square
   of the cross entry from the floor, and the compression of the
   complement projection caps it.  The window inequalities are the
   supply for the outer kill.

The refined bridge routes the closure through one residual: the outer
sharer kill.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.mulVec_apply_of_single_support`, `Gtz.mulVec_apply_of_pair_support`
  — the row reads.
* `Gtz.dotProduct_mulVec_nonneg_of_symm_idem`,
  `Gtz.sq_entry_le_diagonal_mul_of_symm_idem` — **THE ENTRY
  CAUCHY–SCHWARZ.**
* `Gtz.SixThreeCrux.gap_diagonal_pos_of_allHeavy` — **THE GAP FLOOR.**
* `Gtz.false_of_singleton_tight_direction` — **THE SINGLETON KILL.**
* `Gtz.RankFourFrame.false_of_samePair_columns` — **THE SAME-PAIR
  KILL.**
* `Gtz.sharedPair_gap_offdiag_sq_lt`,
  `Gtz.sharedPair_capture_window`,
  `Gtz.sharedPair_compression_window` — **THE NARROWING WINDOW.**
* `Gtz.rankFourSupportTwoClosed_of_outer_shared_kill` — **THE REFINED
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

/-! ## Layer 1 — the row reads -/

/-- The action of a matrix row on a vector with a single support atom
reads one entry. -/
theorem mulVec_apply_of_single_support {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) {atomU : Fin n} {q : Fin n → ℝ}
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → q atomIndex = 0)
    (rowIndex : Fin n) :
    (S *ᵥ q) rowIndex = S rowIndex atomU * q atomU := by
  have hterm : ∀ atomIndex : Fin n, S rowIndex atomIndex * q atomIndex
      = if atomIndex = atomU then S rowIndex atomU * q atomU else 0 := by
    intro atomIndex
    by_cases hU : atomIndex = atomU
    · subst hU
      rw [if_pos rfl]
    · rw [hsupp atomIndex hU, if_neg hU]
      ring
  show (∑ atomIndex : Fin n, S rowIndex atomIndex * q atomIndex) = _
  rw [Finset.sum_congr rfl fun atomIndex _ => hterm atomIndex,
    Finset.sum_ite_eq' Finset.univ atomU]
  simp only [Finset.mem_univ, if_pos]

/-- The action of a matrix row on a vector with a two-atom support reads
two entries. -/
theorem mulVec_apply_of_pair_support {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) {atomU atomV : Fin n} (hne : atomU ≠ atomV)
    {q : Fin n → ℝ}
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV → q atomIndex = 0)
    (rowIndex : Fin n) :
    (S *ᵥ q) rowIndex
      = S rowIndex atomU * q atomU + S rowIndex atomV * q atomV := by
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

/-! ## Layer 2 — the entry Cauchy–Schwarz -/

/-- A symmetric idempotent matrix has a nonnegative quadratic form: the
form at a probe is the square norm of the image. -/
theorem dotProduct_mulVec_nonneg_of_symm_idem {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : Aᵀ = A) (hidem : A * A = A)
    (probe : Fin n → ℝ) : 0 ≤ probe ⬝ᵥ (A *ᵥ probe) := by
  rw [dotProduct_mulVec_eq_image_dotProduct_self hsymm hidem probe]
  exact Finset.sum_nonneg fun atomIndex _ => mul_self_nonneg _

/-- **THE ENTRY CAUCHY–SCHWARZ.**  The square of an off-diagonal entry
of a symmetric idempotent matrix is at most the product of the two
diagonal entries.  The probe family `t e_u + e_v` prices the
discriminant. -/
theorem sq_entry_le_diagonal_mul_of_symm_idem {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : Aᵀ = A) (hidem : A * A = A)
    {atomU atomV : Fin n} (hne : atomU ≠ atomV) :
    A atomU atomV ^ 2 ≤ A atomU atomU * A atomV atomV := by
  have hVU : A atomV atomU = A atomU atomV := by
    have hentry := congrFun (congrFun hsymm atomV) atomU
    rw [Matrix.transpose_apply] at hentry
    exact hentry.symm
  have hquad : ∀ t : ℝ, 0 ≤ A atomU atomU * (t * t)
      + (2 * A atomU atomV) * t + A atomV atomV := by
    intro t
    have hsupp : ∀ atomIndex : Fin n, atomIndex ≠ atomU → atomIndex ≠ atomV →
        (fun probeIndex => if probeIndex = atomU then t
          else if probeIndex = atomV then 1 else 0 : Fin n → ℝ) atomIndex = 0 := by
      intro atomIndex hU hV
      simp only [if_neg hU, if_neg hV]
    have hnonneg := dotProduct_mulVec_nonneg_of_symm_idem hsymm hidem
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

/-! ## Layer 3 — the gap floor -/

/-- **THE GAP FLOOR.**  At an all-heavy crux, every diagonal entry of
the stationary gap is positive: the leverage excess prices it.  The
derivation goes through the design diagonal of the projection. -/
theorem SixThreeCrux.gap_diagonal_pos_of_allHeavy (crux : SixThreeCrux)
    (atomIndex : Fin 6) :
    0 < chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomIndex atomIndex := by
  have hbridge : chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      = chartPointGap (chartPointOfDesign crux.design) := rfl
  rw [hbridge]
  simp only [chartPointGap, chartPointOfDesign, Matrix.sub_apply,
    Matrix.diagonal_apply_eq]
  rw [projectionOfDesign_diagonal]
  have hweight := crux.design.weight_pos atomIndex
  have hexcess := allHeavy_heavyExcess_pos crux.isAllHeavy atomIndex
  rw [heavyExcess] at hexcess
  nlinarith

/-! ## Layer 4 — the two inner kills -/

/-- **THE SINGLETON KILL.**  A tight direction with a single support
atom forces the diagonal gap entry at that atom to the value.  A
positive floor with a negative value is a contradiction. -/
theorem false_of_singleton_tight_direction
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet) {atomU : Fin size}
    (hneU : tightDir label atomU ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → tightDir label atomIndex = 0)
    (hfloor : 0 < chartStationaryGap projection weight atomU atomU)
    (hvalueNeg : value < 0) : False := by
  have hmemU : atomU ∈ activeSubset label := by
    by_contra hout
    exact hneU (hdata.tightDir_support label hmem atomU hout)
  have hrow := hdata.tightDir_isTight label hmem atomU hmemU
  rw [mulVec_apply_of_single_support _ hsupp atomU] at hrow
  have hgap : chartStationaryGap projection weight atomU atomU = value :=
    mul_right_cancel₀ hneU hrow
  rw [hgap] at hfloor
  linarith

/-- **THE SAME-PAIR KILL.**  Two distinct basis columns supported inside
one pair of atoms are impossible.  A zero column breaks the unit norm.
A singleton column dies at the floor.  Two genuine pair columns are
independent through the left inverse, thus the two-atom gap block is the
value times the identity, and the floor kills the diagonal. -/
theorem RankFourFrame.false_of_samePair_columns {crux : SixThreeCrux}
    (frame : RankFourFrame crux) {colA colB : Fin 4} (hne : colB ≠ colA)
    {atomU atomV : Fin 6} (hUV : atomU ≠ atomV)
    (hAU : frame.tightDir (frame.basisLabel colA) atomU ≠ 0)
    (hAV : frame.tightDir (frame.basisLabel colA) atomV ≠ 0)
    (hAsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel colA) atomIndex = 0)
    (hBsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel colB) atomIndex = 0) : False := by
  by_cases hBU : frame.tightDir (frame.basisLabel colB) atomU = 0
  · by_cases hBV : frame.tightDir (frame.basisLabel colB) atomV = 0
    · -- The zero column breaks the unit norm.
      have hzero : ∀ atomIndex, frame.tightDir (frame.basisLabel colB) atomIndex = 0 := by
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
    · -- The singleton column at the second pair atom dies at the floor.
      refine false_of_singleton_tight_direction frame.hdata (frame.hmemAll colB)
        hBV (fun atomIndex hV => ?_)
        (crux.gap_diagonal_pos_of_allHeavy atomV) frame.hvalueNeg
      by_cases hU : atomIndex = atomU
      · rw [hU]; exact hBU
      · exact hBsupp atomIndex hU hV
  · by_cases hBV : frame.tightDir (frame.basisLabel colB) atomV = 0
    · -- The singleton column at the first pair atom dies at the floor.
      refine false_of_singleton_tight_direction frame.hdata (frame.hmemAll colB)
        hBU (fun atomIndex hU => ?_)
        (crux.gap_diagonal_pos_of_allHeavy atomU) frame.hvalueNeg
      by_cases hV : atomIndex = atomV
      · rw [hV]; exact hBV
      · exact hBsupp atomIndex hU hV
    · -- Two genuine pair columns: the block elimination against the floor.
      have hmemAU : atomU ∈ frame.activeSubset (frame.basisLabel colA) := by
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
      · -- Proportional pair restrictions beat the left inverse.
        have hratio : frame.tightDir (frame.basisLabel colB)
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
      · -- The block elimination pins the diagonal gap entry to the value.
        have helim : (chartStationaryGap (chartPointOfDesign crux.design).chart
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

/-! ## Layer 5 — the narrowing window -/

/-- **THE CROSS FLOOR.**  At a frame with a pair column, the square of
the pair cross entry of the gap is strictly above the value squared.
The pair characteristic prices it from the two diagonal floors. -/
theorem sharedPair_gap_offdiag_sq_lt {crux : SixThreeCrux}
    (frame : RankFourFrame crux) {columnIndex : Fin 4}
    {atomU atomV : Fin 6} (hUV : atomU ≠ atomV)
    (hneU : frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0)
    (hneV : frame.tightDir (frame.basisLabel columnIndex) atomV ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0) :
    chartObjective (chartPointOfDesign crux.design) ^ 2
      < chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomU atomV ^ 2 := by
  have hmemU : atomU ∈ frame.activeSubset (frame.basisLabel columnIndex) := by
    by_contra hout
    exact hneU (frame.hdata.tightDir_support _ (frame.hmemAll columnIndex) atomU hout)
  have hmemV : atomV ∈ frame.activeSubset (frame.basisLabel columnIndex) := by
    by_contra hout
    exact hneV (frame.hdata.tightDir_support _ (frame.hmemAll columnIndex) atomV hout)
  have hchar := pair_characteristic frame.hdata (frame.hmemAll columnIndex) hUV
    hmemU hmemV hneU hneV hsupp
  have hfloorU := crux.gap_diagonal_pos_of_allHeavy atomU
  have hfloorV := crux.gap_diagonal_pos_of_allHeavy atomV
  have hvalueNeg := frame.hvalueNeg
  nlinarith [hchar, hfloorU, hfloorV, hvalueNeg]

/-- **THE CAPTURE WINDOW.**  The characteristic square is capped by the
product of the two shifted diagonals of the chart: the chart itself is
the compressing projection. -/
theorem sharedPair_capture_window {crux : SixThreeCrux}
    (frame : RankFourFrame crux) {columnIndex : Fin 4}
    {atomU atomV : Fin 6} (hUV : atomU ≠ atomV)
    (hneU : frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0)
    (hneV : frame.tightDir (frame.basisLabel columnIndex) atomV ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0) :
    (chartObjective (chartPointOfDesign crux.design)
        - chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomU atomU)
      * (chartObjective (chartPointOfDesign crux.design)
        - chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomV atomV)
      ≤ (chartPointOfDesign crux.design).chart atomU atomU
        * (chartPointOfDesign crux.design).chart atomV atomV := by
  have hmemU : atomU ∈ frame.activeSubset (frame.basisLabel columnIndex) := by
    by_contra hout
    exact hneU (frame.hdata.tightDir_support _ (frame.hmemAll columnIndex) atomU hout)
  have hmemV : atomV ∈ frame.activeSubset (frame.basisLabel columnIndex) := by
    by_contra hout
    exact hneV (frame.hdata.tightDir_support _ (frame.hmemAll columnIndex) atomV hout)
  have hchar := pair_characteristic frame.hdata (frame.hmemAll columnIndex) hUV
    hmemU hmemV hneU hneV hsupp
  have hcs := sq_entry_le_diagonal_mul_of_symm_idem frame.hdata.isSymmetric
    frame.hdata.isIdempotent hUV
  have hoff : chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomU atomV
      = (chartPointOfDesign crux.design).chart atomU atomV := by
    rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hUV,
      sub_zero]
  rw [hchar, hoff]
  exact hcs

/-- **THE COMPRESSION WINDOW.**  The characteristic square is also
capped by the product of the two complement diagonals: the complement of
the chart is a projection too. -/
theorem sharedPair_compression_window {crux : SixThreeCrux}
    (frame : RankFourFrame crux) {columnIndex : Fin 4}
    {atomU atomV : Fin 6} (hUV : atomU ≠ atomV)
    (hneU : frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0)
    (hneV : frame.tightDir (frame.basisLabel columnIndex) atomV ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0) :
    (chartObjective (chartPointOfDesign crux.design)
        - chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomU atomU)
      * (chartObjective (chartPointOfDesign crux.design)
        - chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomV atomV)
      ≤ (1 - (chartPointOfDesign crux.design).chart atomU atomU)
        * (1 - (chartPointOfDesign crux.design).chart atomV atomV) := by
  have hmemU : atomU ∈ frame.activeSubset (frame.basisLabel columnIndex) := by
    by_contra hout
    exact hneU (frame.hdata.tightDir_support _ (frame.hmemAll columnIndex) atomU hout)
  have hmemV : atomV ∈ frame.activeSubset (frame.basisLabel columnIndex) := by
    by_contra hout
    exact hneV (frame.hdata.tightDir_support _ (frame.hmemAll columnIndex) atomV hout)
  have hchar := pair_characteristic frame.hdata (frame.hmemAll columnIndex) hUV
    hmemU hmemV hneU hneV hsupp
  have hsymm : (1 - (chartPointOfDesign crux.design).chart)ᵀ
      = 1 - (chartPointOfDesign crux.design).chart := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, frame.hdata.isSymmetric]
  have hidem : (1 - (chartPointOfDesign crux.design).chart)
        * (1 - (chartPointOfDesign crux.design).chart)
      = 1 - (chartPointOfDesign crux.design).chart := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      frame.hdata.isIdempotent]
    abel
  have hcs := sq_entry_le_diagonal_mul_of_symm_idem hsymm hidem hUV
  have hcomplOff : (1 - (chartPointOfDesign crux.design).chart) atomU atomV
      = -(chartPointOfDesign crux.design).chart atomU atomV := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne hUV]
    ring
  have hcomplU : (1 - (chartPointOfDesign crux.design).chart) atomU atomU
      = 1 - (chartPointOfDesign crux.design).chart atomU atomU := by
    rw [Matrix.sub_apply, Matrix.one_apply_eq]
  have hcomplV : (1 - (chartPointOfDesign crux.design).chart) atomV atomV
      = 1 - (chartPointOfDesign crux.design).chart atomV atomV := by
    rw [Matrix.sub_apply, Matrix.one_apply_eq]
  rw [hcomplOff, hcomplU, hcomplV] at hcs
  have hoff : chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomU atomV
      = (chartPointOfDesign crux.design).chart atomU atomV := by
    rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hUV,
      sub_zero]
  rw [hchar, hoff]
  nlinarith [hcs]

/-! ## Layer 6 — the refined bridge -/

/-- **THE REFINED BRIDGE.**  The support-two closure follows from one
residual: the outer sharer kill, where some other basis label carries a
nonzero atom outside the pair.  The inner sharers die here: a sharer
inside the pair is a zero column, a singleton column, or a second pair
column, and each of these dies at the floor or at the left inverse. -/
theorem rankFourSupportTwoClosed_of_outer_shared_kill
    (killOuter : ∀ (crux : SixThreeCrux) (frame : RankFourFrame crux)
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
      False) :
    RankFourSupportTwoClosed := by
  refine rankFourSupportTwoClosed_of_shared_pair_kill ?_
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

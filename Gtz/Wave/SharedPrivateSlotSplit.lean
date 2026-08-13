import Gtz.Wave.SharedPrivateComplementLedger
import Gtz.Wave.SharedPrivateDiagonalKill

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The slot case split — the singular block budget, the straddle rank-one
extension, and the refusal of a second complement pair

The cover ledger is exhausted at three members, thus no budget kills the
identical-support branch on its own.  The next input is the OTHER basis
slots.  Every basis slot carries a tight direction supported in a triple,
thus every basis slot supplies a KERNEL VECTOR of its own shifted gap
block.  This module prices that kernel vector, splits the identical
branch by the position of the other supports, and pays the three parts
that the split produces.

## The defect Cauchy-Schwarz

The chart defect `1 - chart` is symmetric and idempotent, thus the defect
form `x . x - x . (chart x)` is a plain square length.  Two readings of
that square length give a Cauchy-Schwarz inequality at every pair of
probes, with no positive semidefinite hypothesis and no eigenvalue:

  `(x . y - x . (chart y)) ^ 2 ≤ (x . x - x . (chart x)) * (y . y - y . (chart y))`

At a coordinate probe the left side reads one entry of the defect image
and the right side reads one diagonal entry of the defect.

## The singular block budget

A tight direction is a kernel vector of the shifted gap block on its own
block.  The coordinate reading of the defect Cauchy-Schwarz against that
kernel vector gives, at every block atom,

  `(1 - d y) * v y ^ 2 ≤ (1 - A y y / (1 - d y)) * Q`,  `Q = Σ (1 - d) v ^ 2`

and the sum over the block is `Q` on the left.  Thus

  **`Σ_{y ∈ block} A y y / (1 - d y) ≤ card block - 1`.**

That is the elementary form of "a singular block has at most `card - 1`
positive directions".  It needs no spectral theorem, no inertia and no
positive semidefinite block.  Every basis support of a shared-private
datum has three atoms, thus **every basis block pays at most two units**.

## The straddle rank-one extension

A basis slot whose support meets a rank-one triple in TWO atoms makes its
OWN support a rank-one block.  The three tight rows of that slot, against
the one vanishing pair minor of the rank-one triple, produce the five
remaining rank-one equations by Cramer cancellation against the live
third coordinate.  No positivity is used.

## The case split of the identical branch

The pinned slot is never one of the two identical slots, because the pin
atom sits outside the shared triple.  Thus the identical branch always
carries a third slot.  Its support either avoids the shared triple, and
then it IS the complement triple, or it meets the shared triple.  The
three parts are:

* TWO slots on the complement triple — the complement block is rank one,
  and the ledger refuses it.  **The branch dies at once.**
* ONE slot on the complement triple — the complement block is singular,
  thus it pays at most two units.
* A straddling slot that meets the shared triple in two atoms — its own
  support is a rank-one block, thus it pays at most one unit.

## Vacuity

The matrix statements are unconditional.  The datum statements quantify
over shared-private data, and no shared-private datum exists if
`Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the quadratic sign test and the dot product square -/

section QuadraticCore

/-- **THE QUADRATIC SIGN TEST.**  A real quadratic with a nonnegative
leading coefficient that stays nonnegative on the whole line has a
nonpositive discriminant.  The two cases are the vanishing leading
coefficient, where the linear term must vanish, and the positive leading
coefficient, where the vertex gives the bound. -/
theorem sq_le_of_quadratic_nonneg {corner cross tip : ℝ} (htip : 0 ≤ tip)
    (hquad : ∀ scale : ℝ, 0 ≤ corner + 2 * scale * cross + scale * scale * tip) :
    cross * cross ≤ corner * tip := by
  rcases htip.lt_or_eq with hpos | hzero
  · have hvertex := hquad (-(cross / tip))
    have hclear : corner * tip - cross * cross
        = tip * (corner + 2 * (-(cross / tip)) * cross
          + (-(cross / tip)) * (-(cross / tip)) * tip) := by
      field_simp
      ring
    nlinarith [mul_nonneg hpos.le hvertex]
  · -- the leading coefficient vanishes, thus the linear term must vanish
    have hcrossZero : cross = 0 := by
      by_contra hne
      have hchoice := hquad (-(corner + 1) / (2 * cross))
      rw [← hzero, mul_zero, add_zero] at hchoice
      have hlinear : 2 * (-(corner + 1) / (2 * cross)) * cross = -(corner + 1) := by
        field_simp
      rw [hlinear] at hchoice
      linarith
    rw [hcrossZero, ← hzero]
    norm_num

/-- **THE DOT PRODUCT SQUARE.**  The Cauchy-Schwarz inequality of the
plain dot product, proved by the quadratic sign test on the length of a
one-parameter family. -/
theorem dotProduct_sq_le_self {size : ℕ} (probeOne probeTwo : Fin size → ℝ) :
    (probeOne ⬝ᵥ probeTwo) * (probeOne ⬝ᵥ probeTwo)
      ≤ (probeOne ⬝ᵥ probeOne) * (probeTwo ⬝ᵥ probeTwo) := by
  refine sq_le_of_quadratic_nonneg (dotProduct_self_nonneg probeTwo) fun scale => ?_
  have hlength : (0 : ℝ) ≤ ∑ atomIndex : Fin size,
      (probeOne atomIndex + scale * probeTwo atomIndex)
        * (probeOne atomIndex + scale * probeTwo atomIndex) :=
    Finset.sum_nonneg fun atomIndex _ => mul_self_nonneg _
  have hexpand : ∑ atomIndex : Fin size,
      (probeOne atomIndex + scale * probeTwo atomIndex)
        * (probeOne atomIndex + scale * probeTwo atomIndex)
      = (probeOne ⬝ᵥ probeOne) + 2 * scale * (probeOne ⬝ᵥ probeTwo)
        + scale * scale * (probeTwo ⬝ᵥ probeTwo) := by
    simp only [dotProduct]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun atomIndex _ => by ring
  rw [hexpand] at hlength
  exact hlength

end QuadraticCore

/-! ## Layer 2 — the chart defect and its Cauchy-Schwarz -/

section ChartDefect

variable {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}

/-- **THE SYMMETRIC READING.**  A symmetric chart reads the same against
either order of two probes. -/
theorem dotProduct_mulVec_comm (hsymm : projectionᵀ = projection)
    (probeOne probeTwo : Fin size → ℝ) :
    probeOne ⬝ᵥ (projection *ᵥ probeTwo) = probeTwo ⬝ᵥ (projection *ᵥ probeOne) := by
  have hstep : probeOne ᵥ* projection = projection *ᵥ probeOne := by
    conv_lhs => rw [← hsymm]
    rw [Matrix.vecMul_transpose]
  rw [Matrix.dotProduct_mulVec, hstep, dotProduct_comm]

/-- **THE DEFECT EXPANSION.**  The chart defect form of a one-parameter
family of probes is the quadratic with the three defect readings as
coefficients. -/
theorem chartDefect_quadratic (hsymm : projectionᵀ = projection)
    (probeOne probeTwo : Fin size → ℝ) (scale : ℝ) :
    (probeOne + scale • probeTwo) ⬝ᵥ (probeOne + scale • probeTwo)
        - (probeOne + scale • probeTwo)
          ⬝ᵥ (projection *ᵥ (probeOne + scale • probeTwo))
      = (probeOne ⬝ᵥ probeOne - probeOne ⬝ᵥ (projection *ᵥ probeOne))
        + 2 * scale * (probeOne ⬝ᵥ probeTwo - probeOne ⬝ᵥ (projection *ᵥ probeTwo))
        + scale * scale
          * (probeTwo ⬝ᵥ probeTwo - probeTwo ⬝ᵥ (projection *ᵥ probeTwo)) := by
  have hcomm : probeTwo ⬝ᵥ probeOne = probeOne ⬝ᵥ probeTwo := dotProduct_comm _ _
  have hchart : probeTwo ⬝ᵥ (projection *ᵥ probeOne)
      = probeOne ⬝ᵥ (projection *ᵥ probeTwo) :=
    dotProduct_mulVec_comm hsymm probeTwo probeOne
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hcomm, hchart]
  ring

/-- **THE DEFECT CAUCHY-SCHWARZ.**  Two probes read against the chart
defect obey the Cauchy-Schwarz inequality.  No positive semidefinite
hypothesis is used: the defect form of a symmetric idempotent chart is
nonnegative at every probe, and that alone gives the discriminant. -/
theorem chartDefect_cauchy_schwarz (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection) (probeOne probeTwo : Fin size → ℝ) :
    (probeOne ⬝ᵥ probeTwo - probeOne ⬝ᵥ (projection *ᵥ probeTwo))
        * (probeOne ⬝ᵥ probeTwo - probeOne ⬝ᵥ (projection *ᵥ probeTwo))
      ≤ (probeOne ⬝ᵥ probeOne - probeOne ⬝ᵥ (projection *ᵥ probeOne))
        * (probeTwo ⬝ᵥ probeTwo - probeTwo ⬝ᵥ (projection *ᵥ probeTwo)) := by
  refine sq_le_of_quadratic_nonneg ?_ fun scale => ?_
  · have hcontract := dotProduct_mulVec_le_self_of_symmetricIdempotent hsymm hidem probeTwo
    linarith
  · have hcontract := dotProduct_mulVec_le_self_of_symmetricIdempotent hsymm hidem
      (probeOne + scale • probeTwo)
    have hexpand := chartDefect_quadratic hsymm probeOne probeTwo scale
    linarith

/-- The coordinate probe reads one coordinate of a vector. -/
theorem single_one_dotProduct {size : ℕ} (atomIndex : Fin size) (probe : Fin size → ℝ) :
    (Pi.single atomIndex (1 : ℝ)) ⬝ᵥ probe = probe atomIndex := by
  classical
  rw [dotProduct]
  rw [Finset.sum_eq_single atomIndex]
  · rw [Pi.single_eq_same, one_mul]
  · intro otherIndex _ hne
    rw [Pi.single_eq_of_ne hne, zero_mul]
  · intro hnot
    exact absurd (Finset.mem_univ atomIndex) hnot

/-- **THE ROW DEFECT BOUND.**  The coordinate instance of the defect
Cauchy-Schwarz: one entry of the defect image, squared, is capped by the
diagonal defect at that atom times the defect energy of the probe. -/
theorem chartDefect_row_bound (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection) (atomIndex : Fin size)
    (probe : Fin size → ℝ) :
    (probe atomIndex - (projection *ᵥ probe) atomIndex)
        * (probe atomIndex - (projection *ᵥ probe) atomIndex)
      ≤ (1 - projection atomIndex atomIndex)
        * (probe ⬝ᵥ probe - probe ⬝ᵥ (projection *ᵥ probe)) := by
  have hbase := chartDefect_cauchy_schwarz hsymm hidem
    (Pi.single atomIndex (1 : ℝ)) probe
  rw [single_dotProduct_mulVec_single projection atomIndex] at hbase
  rw [single_one_dotProduct, single_one_dotProduct, single_one_dotProduct] at hbase
  rwa [Pi.single_eq_same] at hbase

end ChartDefect

/-! ## Layer 3 — the singular block budget -/

section SingularBudget

variable {size rank : ℕ} {activeIndex : Type}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE KERNEL ENERGY.**  A probe that the chart moves by the captured
diagonal on its own carrier has defect energy equal to the
defect-weighted square mass of the probe. -/
theorem gapSet_kernel_energy {probeSet : Finset (Fin size)} {probe : Fin size → ℝ}
    (hcarrier : ∀ atomIndex, atomIndex ∉ probeSet → probe atomIndex = 0)
    (hkernel : ∀ atomIndex ∈ probeSet,
      (projection *ᵥ probe) atomIndex = (value + weight atomIndex) * probe atomIndex) :
    probe ⬝ᵥ probe - probe ⬝ᵥ (projection *ᵥ probe)
      = ∑ atomIndex ∈ probeSet,
          (1 - (value + weight atomIndex)) * (probe atomIndex * probe atomIndex) := by
  classical
  have hmass : probe ⬝ᵥ probe
      = ∑ atomIndex ∈ probeSet, probe atomIndex * probe atomIndex := by
    rw [dotProduct]
    refine (Finset.sum_subset (Finset.subset_univ probeSet) ?_).symm
    intro atomIndex _ hnot
    rw [hcarrier atomIndex hnot, mul_zero]
  have himage : probe ⬝ᵥ (projection *ᵥ probe)
      = ∑ atomIndex ∈ probeSet,
          (value + weight atomIndex) * (probe atomIndex * probe atomIndex) := by
    rw [dotProduct]
    refine (Finset.sum_subset (Finset.subset_univ probeSet) ?_).symm.trans ?_
    · intro atomIndex _ hnot
      rw [hcarrier atomIndex hnot, zero_mul]
    · refine Finset.sum_congr rfl fun atomIndex hprobe => ?_
      rw [hkernel atomIndex hprobe]
      ring
  rw [hmass, himage, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun atomIndex _ => by ring

/-- **THE KERNEL ROW BUDGET.**  At every carrier atom, the defect
Cauchy-Schwarz against the kernel probe reads as one inequality between
the captured defect, the shifted gap diagonal, and the defect energy of
the probe. -/
theorem gapSet_kernel_row_budget (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    {probeSet : Finset (Fin size)} {probe : Fin size → ℝ}
    (hcarrier : ∀ atomIndex, atomIndex ∉ probeSet → probe atomIndex = 0)
    (hkernel : ∀ atomIndex ∈ probeSet,
      (projection *ᵥ probe) atomIndex = (value + weight atomIndex) * probe atomIndex)
    {atomIndex : Fin size} (hmem : atomIndex ∈ probeSet) :
    ((1 - (value + weight atomIndex)) * probe atomIndex)
        * ((1 - (value + weight atomIndex)) * probe atomIndex)
      ≤ (1 - (value + weight atomIndex)
          - shiftedGapDiag projection weight value atomIndex)
        * ∑ carrierIndex ∈ probeSet,
            (1 - (value + weight carrierIndex))
              * (probe carrierIndex * probe carrierIndex) := by
  have hrow := chartDefect_row_bound hsymm hidem atomIndex probe
  rw [hkernel atomIndex hmem, gapSet_kernel_energy hcarrier hkernel] at hrow
  have hdiag : projection atomIndex atomIndex
      = shiftedGapDiag projection weight value atomIndex + (value + weight atomIndex) :=
    projection_diag_eq_shift (projection := projection) (weight := weight)
      (value := value) atomIndex
  rw [hdiag] at hrow
  have hleft : probe atomIndex - (value + weight atomIndex) * probe atomIndex
      = (1 - (value + weight atomIndex)) * probe atomIndex := by ring
  rw [hleft] at hrow
  have hright : 1 - (shiftedGapDiag projection weight value atomIndex
      + (value + weight atomIndex))
      = 1 - (value + weight atomIndex)
        - shiftedGapDiag projection weight value atomIndex := by ring
  rwa [hright] at hrow

/-- **THE SINGULAR SET BUDGET.**  A set whose shifted gap block carries a
nonzero kernel vector pays at most `card - 1` units.  The rank-one law is
NOT used, and neither is any spectral count, any inertia and any positive
semidefinite block.  The whole proof is the defect Cauchy-Schwarz read at
each coordinate of the kernel vector. -/
theorem gapSet_kernel_saturation (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    {probeSet : Finset (Fin size)} {probe : Fin size → ℝ}
    (hcarrier : ∀ atomIndex, atomIndex ∉ probeSet → probe atomIndex = 0)
    (hkernel : ∀ atomIndex ∈ probeSet,
      (projection *ᵥ probe) atomIndex = (value + weight atomIndex) * probe atomIndex)
    (hcap : ∀ atomIndex ∈ probeSet, value + weight atomIndex < 1)
    {liveAtom : Fin size} (hlive : liveAtom ∈ probeSet) (hne : probe liveAtom ≠ 0) :
    ∑ atomIndex ∈ probeSet,
        shiftedGapDiag projection weight value atomIndex
          / (1 - (value + weight atomIndex))
      ≤ (probeSet.card : ℝ) - 1 := by
  classical
  set energy : ℝ := ∑ carrierIndex ∈ probeSet,
    (1 - (value + weight carrierIndex))
      * (probe carrierIndex * probe carrierIndex) with henergyDef
  have hdefectPos : ∀ atomIndex ∈ probeSet,
      (0 : ℝ) < 1 - (value + weight atomIndex) :=
    fun atomIndex hprobe => by linarith [hcap atomIndex hprobe]
  have henergyPos : 0 < energy := by
    rw [henergyDef]
    refine Finset.sum_pos' (fun carrierIndex hcarr => ?_) ⟨liveAtom, hlive, ?_⟩
    · exact mul_nonneg (hdefectPos carrierIndex hcarr).le (mul_self_nonneg _)
    · exact mul_pos (hdefectPos liveAtom hlive) (mul_self_pos.mpr hne)
  have hstep : ∀ atomIndex ∈ probeSet,
      (1 - (value + weight atomIndex)) * (probe atomIndex * probe atomIndex)
        ≤ energy * (1 - shiftedGapDiag projection weight value atomIndex
          / (1 - (value + weight atomIndex))) := by
    intro atomIndex hprobe
    have hpos := hdefectPos atomIndex hprobe
    have hrow := gapSet_kernel_row_budget hsymm hidem hcarrier hkernel hprobe
    rw [← henergyDef] at hrow
    have hratio : shiftedGapDiag projection weight value atomIndex
        / (1 - (value + weight atomIndex)) * (1 - (value + weight atomIndex))
        = shiftedGapDiag projection weight value atomIndex :=
      div_mul_cancel₀ _ hpos.ne'
    refine le_of_mul_le_mul_left ?_ hpos
    nlinarith [hrow, hratio, henergyPos]
  have hsum := Finset.sum_le_sum hstep
  rw [← henergyDef] at hsum
  have hright : ∑ atomIndex ∈ probeSet,
      energy * (1 - shiftedGapDiag projection weight value atomIndex
        / (1 - (value + weight atomIndex)))
      = energy * ((probeSet.card : ℝ)
        - ∑ atomIndex ∈ probeSet,
          shiftedGapDiag projection weight value atomIndex
            / (1 - (value + weight atomIndex))) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hright] at hsum
  nlinarith [hsum, henergyPos]

/-- **THE TIGHT DIRECTION IS A KERNEL VECTOR AT EVERY PROBE SET.**  Every
set between the direction's SUPPORT and its BLOCK pays at most `card - 1`
units. -/
theorem chart_tightDir_saturation (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {probeSet : Finset (Fin size)} (hsub : probeSet ⊆ activeSubset label)
    (hsupport : datumTightSupport tightDir label ⊆ probeSet)
    (hcap : ∀ atomIndex ∈ probeSet, value + weight atomIndex < 1)
    {liveAtom : Fin size} (hlive : liveAtom ∈ probeSet)
    (hne : tightDir label liveAtom ≠ 0) :
    ∑ atomIndex ∈ probeSet,
        shiftedGapDiag projection weight value atomIndex
          / (1 - (value + weight atomIndex))
      ≤ (probeSet.card : ℝ) - 1 := by
  classical
  refine gapSet_kernel_saturation hsymm hidem (fun atomIndex hnot => ?_)
    (fun atomIndex hprobe => chart_mulVec_tightDir_apply hdata hmem (hsub hprobe))
    hcap hlive hne
  by_contra hliveOut
  exact hnot (hsupport (mem_datumTightSupport.mpr hliveOut))

/-- **THE SINGULAR BLOCK BUDGET.**  The block instance of the singular
budget.  At a block of three atoms the payment is two. -/
theorem chart_tightDir_block_saturation (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    (hcap : ∀ atomIndex ∈ activeSubset label, value + weight atomIndex < 1)
    {liveAtom : Fin size} (hlive : liveAtom ∈ activeSubset label)
    (hne : tightDir label liveAtom ≠ 0) :
    ∑ atomIndex ∈ activeSubset label,
        shiftedGapDiag projection weight value atomIndex
          / (1 - (value + weight atomIndex))
      ≤ ((activeSubset label).card : ℝ) - 1 :=
  chart_tightDir_saturation hsymm hidem hdata hmem (Finset.Subset.refl _)
    (datumTightSupport_subset hdata hmem) hcap hlive hne

/-- **THE SINGULAR SUPPORT BUDGET.**  The support instance of the
singular budget.  A support of two atoms pays a SINGLE unit, with no
rank-one law and no vanishing minor. -/
theorem chart_tightDir_support_saturation (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    (hcap : ∀ atomIndex ∈ datumTightSupport tightDir label,
      value + weight atomIndex < 1)
    {liveAtom : Fin size} (hlive : liveAtom ∈ datumTightSupport tightDir label) :
    ∑ atomIndex ∈ datumTightSupport tightDir label,
        shiftedGapDiag projection weight value atomIndex
          / (1 - (value + weight atomIndex))
      ≤ ((datumTightSupport tightDir label).card : ℝ) - 1 :=
  chart_tightDir_saturation hsymm hidem hdata hmem
    (datumTightSupport_subset hdata hmem) (Finset.Subset.refl _) hcap hlive
    (mem_datumTightSupport.mp hlive)

/-- **THE FOREIGN ROW EXTENSION.**  A tight direction whose shifted gap
row VANISHES at a foreign atom is a kernel vector of the larger block
that adds that atom.  The larger set then pays `card - 1` units.  This is
the reading the live-wedge branch supplies at each of its two foreign
atoms. -/
theorem chart_tightDir_foreign_saturation (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {probeSet : Finset (Fin size)}
    (hsupport : datumTightSupport tightDir label ⊆ probeSet)
    (hkernel : ∀ atomIndex ∈ probeSet, atomIndex ∉ activeSubset label →
      (chartStationaryGap projection weight *ᵥ tightDir label) atomIndex = 0)
    (hcap : ∀ atomIndex ∈ probeSet, value + weight atomIndex < 1)
    {liveAtom : Fin size} (hlive : liveAtom ∈ probeSet)
    (hne : tightDir label liveAtom ≠ 0) :
    ∑ atomIndex ∈ probeSet,
        shiftedGapDiag projection weight value atomIndex
          / (1 - (value + weight atomIndex))
      ≤ (probeSet.card : ℝ) - 1 := by
  classical
  refine gapSet_kernel_saturation hsymm hidem (fun atomIndex hnot => ?_)
    (fun atomIndex hprobe => ?_) hcap hlive hne
  · by_contra hliveOut
    exact hnot (hsupport (mem_datumTightSupport.mpr hliveOut))
  · by_cases hblock : atomIndex ∈ activeSubset label
    · exact chart_mulVec_tightDir_apply hdata hmem hblock
    · have hforeign := hkernel atomIndex hprobe hblock
      have hzero : tightDir label atomIndex = 0 := by
        by_contra hliveOut
        exact hblock (datumTightSupport_subset hdata hmem
          (mem_datumTightSupport.mpr hliveOut))
      rw [chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply,
        Matrix.mulVec_diagonal, hzero, mul_zero, sub_zero] at hforeign
      rw [hforeign, hzero, mul_zero]

/-- **THE FOREIGN ROW READING.**  A probe whose shifted gap row vanishes
at an atom where the probe itself vanishes is moved by the captured
diagonal at that atom. -/
theorem chart_mulVec_capture_of_zero_row {probe : Fin size → ℝ}
    {atomIndex : Fin size}
    (hrow : (chartStationaryGap projection weight *ᵥ probe) atomIndex = 0)
    (hzero : probe atomIndex = 0) :
    (projection *ᵥ probe) atomIndex = (value + weight atomIndex) * probe atomIndex := by
  rw [chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal,
    hzero, mul_zero, sub_zero] at hrow
  rw [hrow, hzero, mul_zero]

/-- **THE KERNEL COMBINATION BUDGET.**  Two tight directions that the
chart moves diagonally on one common set span a plane of kernel vectors
of that set.  A combination chosen to die at one atom of the set is
carried by the SMALLER set, thus that smaller set pays `card - 1`.  This
is how two directions buy a stronger budget than either one alone. -/
theorem chart_pair_combination_saturation (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    {labelOne labelTwo : activeIndex} {probeSet : Finset (Fin size)}
    {scaleOne scaleTwo : ℝ}
    (hkernelOne : ∀ atomIndex ∈ probeSet,
      (projection *ᵥ tightDir labelOne) atomIndex
        = (value + weight atomIndex) * tightDir labelOne atomIndex)
    (hkernelTwo : ∀ atomIndex ∈ probeSet,
      (projection *ᵥ tightDir labelTwo) atomIndex
        = (value + weight atomIndex) * tightDir labelTwo atomIndex)
    (hcarrier : ∀ atomIndex, atomIndex ∉ probeSet →
      scaleOne * tightDir labelOne atomIndex
        + scaleTwo * tightDir labelTwo atomIndex = 0)
    (hcap : ∀ atomIndex ∈ probeSet, value + weight atomIndex < 1)
    {liveAtom : Fin size} (hlive : liveAtom ∈ probeSet)
    (hne : scaleOne * tightDir labelOne liveAtom
      + scaleTwo * tightDir labelTwo liveAtom ≠ 0) :
    ∑ atomIndex ∈ probeSet,
        shiftedGapDiag projection weight value atomIndex
          / (1 - (value + weight atomIndex))
      ≤ (probeSet.card : ℝ) - 1 := by
  classical
  have happly : ∀ atomIndex : Fin size,
      (scaleOne • tightDir labelOne + scaleTwo • tightDir labelTwo) atomIndex
        = scaleOne * tightDir labelOne atomIndex
          + scaleTwo * tightDir labelTwo atomIndex := fun _ => rfl
  refine gapSet_kernel_saturation hsymm hidem
    (probe := scaleOne • tightDir labelOne + scaleTwo • tightDir labelTwo)
    (fun atomIndex hnot => by rw [happly]; exact hcarrier atomIndex hnot)
    (fun atomIndex hprobe => ?_) hcap hlive
    (by rw [happly]; exact hne)
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.add_apply,
    Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    hkernelOne atomIndex hprobe, hkernelTwo atomIndex hprobe, happly]
  ring

end SingularBudget

/-! ## Layer 4 — the straddle rank-one extension -/

section Straddle

variable {size rank : ℕ} {activeIndex : Type}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE STRADDLE RANK-ONE EXTENSION.**  A tight direction supported in a
triple whose FIRST TWO atoms already carry a vanishing pair minor makes
the WHOLE triple a rank-one shifted gap block.  The three tight rows plus
the one minor give the five remaining equations by Cramer cancellation
against the live third coordinate.  No positivity of any diagonal is
used. -/
theorem gapBlockRankOne_of_straddle
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomY atomZ atomW : Fin size} (hYZ : atomY ≠ atomZ) (hYW : atomY ≠ atomW)
    (hZW : atomZ ≠ atomW)
    (hYblock : atomY ∈ activeSubset label) (hZblock : atomZ ∈ activeSubset label)
    (hWblock : atomW ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomY → atomIndex ≠ atomZ →
      atomIndex ≠ atomW → tightDir label atomIndex = 0)
    (hliveW : tightDir label atomW ≠ 0)
    (hminor : chartStationaryGap projection weight atomY atomZ
        * chartStationaryGap projection weight atomY atomZ
      = (chartStationaryGap projection weight atomY atomY - value)
        * (chartStationaryGap projection weight atomZ atomZ - value)) :
    GapBlockRankOne projection weight value atomY atomZ atomW := by
  obtain ⟨hrowY, hrowZ, hrowW⟩ := triple_tight_corner_rows hdata hmem hYZ hYW hZW
    hYblock hZblock hWblock hsupp
  -- the two cross equations, by Cramer cancellation against the live third atom
  have hcrossY : (chartStationaryGap projection weight atomY atomY - value)
      * chartStationaryGap projection weight atomZ atomW
      = chartStationaryGap projection weight atomY atomZ
        * chartStationaryGap projection weight atomY atomW := by
    have hkey : (chartStationaryGap projection weight atomY atomZ
          * chartStationaryGap projection weight atomY atomW
        - (chartStationaryGap projection weight atomY atomY - value)
          * chartStationaryGap projection weight atomZ atomW)
        * tightDir label atomW = 0 := by
      linear_combination chartStationaryGap projection weight atomY atomZ * hrowY
        - (chartStationaryGap projection weight atomY atomY - value) * hrowZ
        - tightDir label atomZ * hminor
    rcases mul_eq_zero.mp hkey with hzero | hzero
    · linarith
    · exact absurd hzero hliveW
  have hcrossZ : (chartStationaryGap projection weight atomZ atomZ - value)
      * chartStationaryGap projection weight atomY atomW
      = chartStationaryGap projection weight atomY atomZ
        * chartStationaryGap projection weight atomZ atomW := by
    have hkey : (chartStationaryGap projection weight atomY atomZ
          * chartStationaryGap projection weight atomZ atomW
        - (chartStationaryGap projection weight atomZ atomZ - value)
          * chartStationaryGap projection weight atomY atomW)
        * tightDir label atomW = 0 := by
      linear_combination chartStationaryGap projection weight atomY atomZ * hrowZ
        - (chartStationaryGap projection weight atomZ atomZ - value) * hrowY
        - tightDir label atomY * hminor
    rcases mul_eq_zero.mp hkey with hzero | hzero
    · linarith
    · exact absurd hzero hliveW
  -- the two mixed minors
  have hminorYW : chartStationaryGap projection weight atomY atomW
      * chartStationaryGap projection weight atomY atomW
      = (chartStationaryGap projection weight atomY atomY - value)
        * (chartStationaryGap projection weight atomW atomW - value) := by
    have hkey : ((chartStationaryGap projection weight atomY atomY - value)
          * (chartStationaryGap projection weight atomW atomW - value)
        - chartStationaryGap projection weight atomY atomW
          * chartStationaryGap projection weight atomY atomW)
        * tightDir label atomW = 0 := by
      linear_combination (chartStationaryGap projection weight atomY atomY - value) * hrowW
        - chartStationaryGap projection weight atomY atomW * hrowY
        - tightDir label atomZ * hcrossY
    rcases mul_eq_zero.mp hkey with hzero | hzero
    · linarith
    · exact absurd hzero hliveW
  have hminorZW : chartStationaryGap projection weight atomZ atomW
      * chartStationaryGap projection weight atomZ atomW
      = (chartStationaryGap projection weight atomZ atomZ - value)
        * (chartStationaryGap projection weight atomW atomW - value) := by
    have hkey : ((chartStationaryGap projection weight atomZ atomZ - value)
          * (chartStationaryGap projection weight atomW atomW - value)
        - chartStationaryGap projection weight atomZ atomW
          * chartStationaryGap projection weight atomZ atomW)
        * tightDir label atomW = 0 := by
      linear_combination (chartStationaryGap projection weight atomZ atomZ - value) * hrowW
        - chartStationaryGap projection weight atomZ atomW * hrowZ
        - tightDir label atomY * hcrossZ
    rcases mul_eq_zero.mp hkey with hzero | hzero
    · linarith
    · exact absurd hzero hliveW
  -- the corner equation at the third atom
  have hcrossW : (chartStationaryGap projection weight atomW atomW - value)
      * chartStationaryGap projection weight atomY atomZ
      = chartStationaryGap projection weight atomY atomW
        * chartStationaryGap projection weight atomZ atomW := by
    have hkey : (chartStationaryGap projection weight atomY atomW
          * chartStationaryGap projection weight atomZ atomW
        - (chartStationaryGap projection weight atomW atomW - value)
          * chartStationaryGap projection weight atomY atomZ)
        * tightDir label atomW = 0 := by
      linear_combination chartStationaryGap projection weight atomZ atomW * hrowY
        - chartStationaryGap projection weight atomY atomZ * hrowW
        - tightDir label atomY * hcrossY
    rcases mul_eq_zero.mp hkey with hzero | hzero
    · linarith
    · exact absurd hzero hliveW
  exact ⟨hminor, hminorYW, hminorZW, hcrossY, hcrossZ, hcrossW⟩

end Straddle

/-! ## Layer 5 — the pair minors of a rank-one triple -/

section PairMinor

variable {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}
variable {weight : Fin size → ℝ} {value : ℝ}

/-- The gap entry of a symmetric chart is symmetric. -/
theorem chartStationaryGap_swap (hsymm : projectionᵀ = projection)
    (rowIndex colIndex : Fin size) :
    chartStationaryGap projection weight colIndex rowIndex
      = chartStationaryGap projection weight rowIndex colIndex := by
  rw [chartStationaryGap, Matrix.sub_apply, Matrix.sub_apply,
    projection_symm_entry hsymm rowIndex colIndex]
  by_cases hne : rowIndex = colIndex
  · subst hne; rfl
  · rw [Matrix.diagonal_apply_ne _ (Ne.symm hne), Matrix.diagonal_apply_ne _ hne]

/-- **EVERY PAIR OF A RANK-ONE TRIPLE HAS A VANISHING MINOR.**  The three
listed minors plus the entry symmetry cover the six ordered pairs. -/
theorem gapPairMinor_of_mem_rankOne_triple (hsymm : projectionᵀ = projection)
    {atomU atomV atomS : Fin size}
    (hshape : GapBlockRankOne projection weight value atomU atomV atomS)
    {atomY atomZ : Fin size} (hYZ : atomY ≠ atomZ)
    (hY : atomY ∈ ({atomU, atomV, atomS} : Finset (Fin size)))
    (hZ : atomZ ∈ ({atomU, atomV, atomS} : Finset (Fin size))) :
    chartStationaryGap projection weight atomY atomZ
        * chartStationaryGap projection weight atomY atomZ
      = (chartStationaryGap projection weight atomY atomY - value)
        * (chartStationaryGap projection weight atomZ atomZ - value) := by
  classical
  obtain ⟨hminorUV, hminorUS, hminorVS, _, _, _⟩ := hshape
  have hVU := chartStationaryGap_swap (weight := weight) hsymm atomU atomV
  have hSU := chartStationaryGap_swap (weight := weight) hsymm atomU atomS
  have hSV := chartStationaryGap_swap (weight := weight) hsymm atomV atomS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hY hZ
  rcases hY with rfl | rfl | rfl <;> rcases hZ with rfl | rfl | rfl
  · exact absurd rfl hYZ
  · exact hminorUV
  · exact hminorUS
  · rw [hVU]; linear_combination hminorUV
  · exact absurd rfl hYZ
  · exact hminorVS
  · rw [hSU]; linear_combination hminorUS
  · rw [hSV]; linear_combination hminorVS
  · exact absurd rfl hYZ

end PairMinor

/-! ## Layer 6 — the datum readings of the two new laws -/

namespace SharedPrivateData

variable {crux : SixThreeCrux}

/-- **EVERY BASIS BLOCK PAYS TWO.**  A basis support has three atoms and
carries a live tight direction, thus the singular block budget prices it
at two units. -/
theorem basis_block_saturation (data : SharedPrivateData crux)
    (slot : Fin data.basisCount) :
    ∑ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomIndex
          / (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex))
      ≤ 2 := by
  classical
  obtain ⟨atomU, atomV, atomS, _, _, _, hsupport⟩ :=
    Finset.card_eq_three.mp (data.hthree slot)
  have hblock := data.basisBlock_eq_support slot
  have hliveMem : atomU ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
    rw [hsupport]; simp
  have hbudget := chart_tightDir_block_saturation data.hdata.isSymmetric
    data.hdata.isIdempotent data.hdata (data.basisLabel_mem_activeSet slot)
    (fun atomIndex _ => data.captureDiag_lt_one atomIndex)
    (by rw [hblock]; exact hliveMem)
    (data.basis_live_of_mem_support hliveMem)
  rw [hblock] at hbudget
  have hcard : ((datumTightSupport data.tightDir (data.basisLabel slot)).card : ℝ) = 3 := by
    rw [data.hthree slot]; norm_num
  rw [hcard] at hbudget
  linarith

/-- **THE DEFECT DROP.**  The captured defect is at most one, thus the
plain shifted gap sum is at most the divided one. -/
theorem shiftedGapDiag_sum_le_of_ratio (data : SharedPrivateData crux)
    (setS : Finset (Fin 6)) {bound : ℝ}
    (hratio : ∑ atomIndex ∈ setS,
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomIndex
          / (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)) ≤ bound) :
    ∑ atomIndex ∈ setS,
        shiftedGapDiag (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design)) atomIndex ≤ bound := by
  classical
  refine le_trans (Finset.sum_le_sum fun atomIndex _ => ?_) hratio
  have hcap := data.captureDiag_lt_one atomIndex
  have hfloor := data.captureDiag_nonneg atomIndex
  have hgap := data.shiftedGapDiag_pos atomIndex
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- **THE PLAIN FORM OF THE BASIS BLOCK BUDGET.** -/
theorem basis_block_shifted_sum_le_two (data : SharedPrivateData crux)
    (slot : Fin data.basisCount) :
    ∑ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        shiftedGapDiag (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design)) atomIndex
      ≤ 2 :=
  data.shiftedGapDiag_sum_le_of_ratio _ (data.basis_block_saturation slot)

/-- **THE EXPANDED BASIS TRIPLE BUDGET.**  The three named atoms of a
basis support pay two units together. -/
theorem basis_triple_shifted_sum_le_two (data : SharedPrivateData crux)
    {slot : Fin data.basisCount} {atomU atomV atomS : Fin 6}
    (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS) (hVS : atomV ≠ atomS)
    (hsupport : datumTightSupport data.tightDir (data.basisLabel slot)
      = {atomU, atomV, atomS}) :
    shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomU
      + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomV
      + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomS ≤ 2 := by
  classical
  have hbudget := data.basis_block_shifted_sum_le_two slot
  rw [hsupport, Finset.sum_insert (by simp [hUV, hUS]),
    Finset.sum_insert (by simp [hVS]), Finset.sum_singleton] at hbudget
  linarith

/-- **EVERY ACTIVE SUPPORT PAYS ITS CARDINALITY LESS ONE.**  No basis, no
rank-one law, no minor: the tight direction of the label is the kernel
vector and the defect Cauchy-Schwarz prices it. -/
theorem label_support_saturation (data : SharedPrivateData crux)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet)
    {liveAtom : Fin 6} (hlive : liveAtom ∈ datumTightSupport data.tightDir label) :
    ∑ atomIndex ∈ datumTightSupport data.tightDir label,
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomIndex
          / (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex))
      ≤ ((datumTightSupport data.tightDir label).card : ℝ) - 1 :=
  chart_tightDir_support_saturation data.hdata.isSymmetric data.hdata.isIdempotent
    data.hdata hmem (fun atomIndex _ => data.captureDiag_lt_one atomIndex) hlive

/-- **THE SUPPORT-TWO BUDGET, FREE OF EVERY MINOR.**  A label whose tight
direction lives on two atoms pays a single unit.  The landed pair budget
needs a vanishing minor for this: the kernel reading needs nothing. -/
theorem supportTwo_shifted_sum_le_one (data : SharedPrivateData crux)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet)
    {atomX atomY : Fin 6} (hXY : atomX ≠ atomY)
    (hsupport : datumTightSupport data.tightDir label = {atomX, atomY}) :
    shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomX
      + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomY ≤ 1 := by
  classical
  have hliveX : atomX ∈ datumTightSupport data.tightDir label := by
    rw [hsupport]; simp
  have hcard : ((datumTightSupport data.tightDir label).card : ℝ) = 2 := by
    rw [hsupport, Finset.card_insert_of_notMem (by simp [hXY]), Finset.card_singleton]
    norm_num
  have hbudget := data.label_support_saturation hmem hliveX
  rw [hcard] at hbudget
  have hplain := data.shiftedGapDiag_sum_le_of_ratio
    (datumTightSupport data.tightDir label) hbudget
  rw [hsupport, Finset.sum_insert (by simp [hXY]), Finset.sum_singleton] at hplain
  linarith

/-- **THE FOREIGN-ROW FOUR-SET BUDGET.**  A basis slot whose shifted gap
row vanishes at a foreign atom carries a kernel vector of the four-atom
block that adds that atom, thus that four-set pays three units.  This is
the live-wedge reading. -/
theorem foreign_quad_shifted_sum_le_three (data : SharedPrivateData crux)
    {slot : Fin data.basisCount} {atomA atomB atomX atomY : Fin 6}
    (hAB : atomA ≠ atomB) (hAX : atomA ≠ atomX) (hAY : atomA ≠ atomY)
    (hBX : atomB ≠ atomX) (hBY : atomB ≠ atomY) (hXY : atomX ≠ atomY)
    (hsupport : datumTightSupport data.tightDir (data.basisLabel slot)
      = {atomA, atomB, atomX})
    (hforeign : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
      *ᵥ data.tightDir (data.basisLabel slot)) atomY = 0) :
    shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomA
      + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomB
      + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomX
      + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomY ≤ 3 := by
  classical
  have hblock := data.basisBlock_eq_support slot
  have hsubset : datumTightSupport data.tightDir (data.basisLabel slot)
      ⊆ ({atomA, atomB, atomX, atomY} : Finset (Fin 6)) := by
    rw [hsupport]
    intro atomIndex hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    tauto
  have hliveA : atomA ∈ ({atomA, atomB, atomX, atomY} : Finset (Fin 6)) := by simp
  have hkernel : ∀ atomIndex ∈ ({atomA, atomB, atomX, atomY} : Finset (Fin 6)),
      atomIndex ∉ data.activeSubset (data.basisLabel slot) →
      (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        *ᵥ data.tightDir (data.basisLabel slot)) atomIndex = 0 := by
    intro atomIndex hmem hout
    rw [hblock, hsupport] at hout
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem hout
    rcases hmem with rfl | rfl | rfl | rfl
    · exact absurd rfl hout.1
    · exact absurd rfl hout.2.1
    · exact absurd rfl hout.2.2
    · exact hforeign
  have hbudget := chart_tightDir_foreign_saturation data.hdata.isSymmetric
    data.hdata.isIdempotent data.hdata (data.basisLabel_mem_activeSet slot)
    hsubset hkernel (fun atomIndex _ => data.captureDiag_lt_one atomIndex) hliveA
    (data.basis_live_of_mem_support (by rw [hsupport]; simp))
  have hcard : ((({atomA, atomB, atomX, atomY} : Finset (Fin 6))).card : ℝ) = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hAB, hAX, hAY]),
      Finset.card_insert_of_notMem (by simp [hBX, hBY]),
      Finset.card_insert_of_notMem (by simp [hXY]), Finset.card_singleton]
    norm_num
  rw [hcard] at hbudget
  have hplain := data.shiftedGapDiag_sum_le_of_ratio _ hbudget
  rw [Finset.sum_insert (by simp [hAB, hAX, hAY]),
    Finset.sum_insert (by simp [hBX, hBY]),
    Finset.sum_insert (by simp [hXY]), Finset.sum_singleton] at hplain
  linarith

/-- **THE LIVE-WEDGE TRIPLE BUDGET.**  The two wedge slots share the pair
`{atomA, atomB}` and each has a vanishing shifted gap row at the other's
foreign atom.  The combination that dies at `atomA` is carried by the
triple `{atomB, atomX, atomY}`, thus that triple pays TWO units.  The
same reading with the roles of `atomA` and `atomB` exchanged prices the
other triple, and the two together cap the four-set at `8/3`. -/
theorem liveWedge_triple_shifted_sum_le_two (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} {atomA atomB atomX atomY : Fin 6}
    (hAB : atomA ≠ atomB) (hAX : atomA ≠ atomX) (hAY : atomA ≠ atomY)
    (hBX : atomB ≠ atomX) (hBY : atomB ≠ atomY) (hXY : atomX ≠ atomY)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomA, atomB, atomX})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomA, atomB, atomY})
    (hforeignX : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
      *ᵥ data.tightDir (data.basisLabel slotTwo)) atomX = 0)
    (hforeignY : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
      *ᵥ data.tightDir (data.basisLabel slotOne)) atomY = 0) :
    shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomB
      + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomX
      + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomY ≤ 2 := by
  classical
  have hblockOne := data.basisBlock_eq_support slotOne
  have hblockTwo := data.basisBlock_eq_support slotTwo
  have hdeadOneY : data.tightDir (data.basisLabel slotOne) atomY = 0 :=
    data.basis_dead_of_notMem_support
      (by rw [hsupportOne]; simp [Ne.symm hAY, Ne.symm hBY, Ne.symm hXY])
  have hdeadTwoX : data.tightDir (data.basisLabel slotTwo) atomX = 0 :=
    data.basis_dead_of_notMem_support
      (by rw [hsupportTwo]; simp [Ne.symm hAX, Ne.symm hBX, hXY])
  have hliveOneX : data.tightDir (data.basisLabel slotOne) atomX ≠ 0 :=
    data.basis_live_of_mem_support (by rw [hsupportOne]; simp)
  have hliveTwoA : data.tightDir (data.basisLabel slotTwo) atomA ≠ 0 :=
    data.basis_live_of_mem_support (by rw [hsupportTwo]; simp)
  have hkernelOne : ∀ atomIndex ∈ ({atomB, atomX, atomY} : Finset (Fin 6)),
      ((chartPointOfDesign crux.design).chart
          *ᵥ data.tightDir (data.basisLabel slotOne)) atomIndex
        = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
          * data.tightDir (data.basisLabel slotOne) atomIndex := by
    intro atomIndex hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact chart_mulVec_tightDir_apply data.hdata
        (data.basisLabel_mem_activeSet slotOne)
        (by rw [hblockOne, hsupportOne]; simp)
    · exact chart_mulVec_tightDir_apply data.hdata
        (data.basisLabel_mem_activeSet slotOne)
        (by rw [hblockOne, hsupportOne]; simp)
    · exact chart_mulVec_capture_of_zero_row hforeignY hdeadOneY
  have hkernelTwo : ∀ atomIndex ∈ ({atomB, atomX, atomY} : Finset (Fin 6)),
      ((chartPointOfDesign crux.design).chart
          *ᵥ data.tightDir (data.basisLabel slotTwo)) atomIndex
        = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
          * data.tightDir (data.basisLabel slotTwo) atomIndex := by
    intro atomIndex hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact chart_mulVec_tightDir_apply data.hdata
        (data.basisLabel_mem_activeSet slotTwo)
        (by rw [hblockTwo, hsupportTwo]; simp)
    · exact chart_mulVec_capture_of_zero_row hforeignX hdeadTwoX
    · exact chart_mulVec_tightDir_apply data.hdata
        (data.basisLabel_mem_activeSet slotTwo)
        (by rw [hblockTwo, hsupportTwo]; simp)
  have hcarrier : ∀ atomIndex : Fin 6,
      atomIndex ∉ ({atomB, atomX, atomY} : Finset (Fin 6)) →
      data.tightDir (data.basisLabel slotTwo) atomA
          * data.tightDir (data.basisLabel slotOne) atomIndex
        + -(data.tightDir (data.basisLabel slotOne) atomA)
          * data.tightDir (data.basisLabel slotTwo) atomIndex = 0 := by
    intro atomIndex hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    by_cases hA : atomIndex = atomA
    · subst hA; ring
    · have hdeadOne : data.tightDir (data.basisLabel slotOne) atomIndex = 0 :=
        data.basis_dead_of_notMem_support
          (by rw [hsupportOne]; simp [hA, hnot.1, hnot.2.1])
      have hdeadTwo : data.tightDir (data.basisLabel slotTwo) atomIndex = 0 :=
        data.basis_dead_of_notMem_support
          (by rw [hsupportTwo]; simp [hA, hnot.1, hnot.2.2])
      rw [hdeadOne, hdeadTwo, mul_zero, mul_zero, add_zero]
  have hbudget := chart_pair_combination_saturation data.hdata.isSymmetric
    data.hdata.isIdempotent (labelOne := data.basisLabel slotOne)
    (labelTwo := data.basisLabel slotTwo)
    (scaleOne := data.tightDir (data.basisLabel slotTwo) atomA)
    (scaleTwo := -(data.tightDir (data.basisLabel slotOne) atomA))
    hkernelOne hkernelTwo hcarrier
    (fun atomIndex _ => data.captureDiag_lt_one atomIndex)
    (by simp : atomX ∈ ({atomB, atomX, atomY} : Finset (Fin 6)))
    (by rw [hdeadTwoX, mul_zero, add_zero]; exact mul_ne_zero hliveTwoA hliveOneX)
  have hcard : ((({atomB, atomX, atomY} : Finset (Fin 6))).card : ℝ) = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hBX, hBY]),
      Finset.card_insert_of_notMem (by simp [hXY]), Finset.card_singleton]
    norm_num
  rw [hcard] at hbudget
  have hplain := data.shiftedGapDiag_sum_le_of_ratio _ hbudget
  rw [Finset.sum_insert (by simp [hBX, hBY]), Finset.sum_insert (by simp [hXY]),
    Finset.sum_singleton] at hplain
  linarith

/-- **THE PIN SLOT IS A THIRD SLOT.**  The pin atom sits in the pinned
slot's support and outside the shared triple, thus the pinned slot is
neither of the two identical slots. -/
theorem privateSlot_notMem_identical_pair (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hsame : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = datumTightSupport data.tightDir (data.basisLabel slotOne)) :
    data.privateSlot ≠ slotOne ∧ data.privateSlot ≠ slotTwo := by
  have hpinMem : data.pinAtom
      ∈ datumTightSupport data.tightDir (data.basisLabel data.privateSlot) :=
    mem_datumTightSupport.mpr data.hpinNe
  have hout := data.pinAtom_notMem_of_identical_support hne hsame
  constructor
  · intro heq
    rw [heq] at hpinMem
    exact hout hpinMem
  · intro heq
    rw [heq, hsame] at hpinMem
    exact hout hpinMem

/-- **THE PIN SLOT AVOIDS THE SHARED TRIPLE.**  The pin atom is outside
the shared triple, thus the pinned slot's support is not the shared
triple. -/
theorem privateSlot_support_ne_of_identical (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hsame : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = datumTightSupport data.tightDir (data.basisLabel slotOne)) :
    datumTightSupport data.tightDir (data.basisLabel data.privateSlot)
      ≠ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
  intro hsupport
  have hpinMem : data.pinAtom
      ∈ datumTightSupport data.tightDir (data.basisLabel data.privateSlot) :=
    mem_datumTightSupport.mpr data.hpinNe
  rw [hsupport] at hpinMem
  exact data.pinAtom_notMem_of_identical_support hne hsame hpinMem

/-- **THE COMPLEMENT DICHOTOMY OF A SLOT.**  A basis support that misses
the shared triple entirely IS the complement of the shared triple: three
atoms inside three atoms. -/
theorem support_eq_complement_of_disjoint (data : SharedPrivateData crux)
    {slot : Fin data.basisCount} {shared : Finset (Fin 6)} (hcard : shared.card = 3)
    (hdisjoint : ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
      atomIndex ∉ shared) :
    datumTightSupport data.tightDir (data.basisLabel slot) = Finset.univ \ shared := by
  classical
  refine Finset.eq_of_subset_of_card_le (fun atomIndex hmem => ?_) ?_
  · rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ atomIndex, hdisjoint atomIndex hmem⟩
  · have hcompl : (Finset.univ \ shared : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_sdiff, Finset.inter_univ, hcard, Finset.card_univ, Fintype.card_fin]
    rw [hcompl, data.hthree slot]

/-- **CASE A OF THE SPLIT — THE BRANCH DIES.**  Two further slots that
share the complement of the shared triple make that complement a rank-one
shifted gap block, and the cover ledger refuses it.  This is a full kill
of the sub-branch, with no residue. -/
theorem false_of_complement_identical_pair (data : SharedPrivateData crux)
    {slotOne slotTwo slotThree slotFour : Fin data.basisCount}
    (hneShared : slotOne ≠ slotTwo) (hneOther : slotThree ≠ slotFour)
    {atomU atomV atomS atomP atomQ atomR : Fin 6}
    (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS) (hVS : atomV ≠ atomS)
    (hPQ : atomP ≠ atomQ) (hPR : atomP ≠ atomR) (hQR : atomQ ≠ atomR)
    (hcover : ({atomU, atomV, atomS} : Finset (Fin 6)) ∪ {atomP, atomQ, atomR}
      = Finset.univ)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomU, atomV, atomS})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS})
    (hsupportThree : datumTightSupport data.tightDir (data.basisLabel slotThree)
      = {atomP, atomQ, atomR})
    (hsupportFour : datumTightSupport data.tightDir (data.basisLabel slotFour)
      = {atomP, atomQ, atomR}) :
    False :=
  data.not_gapBlockRankOne_complement_of_identical_support hneShared hUV hUS hVS
    hPQ hPR hQR hcover hsupportOne hsupportTwo
    (data.gapBlockRankOne_of_identical_support hneOther hPQ hPR hQR hsupportThree
      hsupportFour)

/-- **CASE C OF THE SPLIT — THE STRADDLE IS RANK ONE.**  A further slot
whose support meets the shared triple in two atoms carries its own
rank-one shifted gap block.  The shared triple supplies the one pair
minor, and the slot's three tight rows supply the rest. -/
theorem gapBlockRankOne_of_straddle_slot (data : SharedPrivateData crux)
    {slot : Fin data.basisCount} {atomY atomZ atomW : Fin 6}
    (hYZ : atomY ≠ atomZ) (hYW : atomY ≠ atomW) (hZW : atomZ ≠ atomW)
    (hsupport : datumTightSupport data.tightDir (data.basisLabel slot)
      = {atomY, atomZ, atomW})
    (hminor : chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomY atomZ
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomY atomZ
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomY atomY
          - chartObjective (chartPointOfDesign crux.design))
        * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomZ atomZ
          - chartObjective (chartPointOfDesign crux.design))) :
    GapBlockRankOne (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) atomY atomZ atomW := by
  classical
  have hblock := data.basisBlock_eq_support slot
  have hmemY : atomY ∈ ({atomY, atomZ, atomW} : Finset (Fin 6)) := by simp
  have hmemZ : atomZ ∈ ({atomY, atomZ, atomW} : Finset (Fin 6)) := by simp
  have hmemW : atomW ∈ ({atomY, atomZ, atomW} : Finset (Fin 6)) := by simp
  exact gapBlockRankOne_of_straddle data.hdata (data.basisLabel_mem_activeSet slot)
    hYZ hYW hZW
    (by rw [hblock, hsupport]; exact hmemY)
    (by rw [hblock, hsupport]; exact hmemZ)
    (by rw [hblock, hsupport]; exact hmemW)
    (fun atomIndex hY hZ hW => data.basis_dead_of_notMem_support
      (by rw [hsupport]; simp [hY, hZ, hW]))
    (data.basis_live_of_mem_support (by rw [hsupport]; exact hmemW))
    hminor

/-- **THE STRADDLE PAYS ONE.**  A straddling slot's own support is a
rank-one block, thus it pays a single unit — half of what the singular
budget alone gives. -/
theorem straddle_shifted_sum_le_one (data : SharedPrivateData crux)
    {slot : Fin data.basisCount} {atomY atomZ atomW : Fin 6}
    (hYZ : atomY ≠ atomZ) (hYW : atomY ≠ atomW) (hZW : atomZ ≠ atomW)
    (hsupport : datumTightSupport data.tightDir (data.basisLabel slot)
      = {atomY, atomZ, atomW})
    (hminor : chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomY atomZ
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomY atomZ
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomY atomY
          - chartObjective (chartPointOfDesign crux.design))
        * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomZ atomZ
          - chartObjective (chartPointOfDesign crux.design))) :
    shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomY
      + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomZ
      + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomW ≤ 1 :=
  gapBlockRankOne_shifted_sum_le_one data.hdata.isSymmetric data.hdata.isIdempotent
    hYZ hYW hZW (data.captureDiag_nonneg atomY) (data.captureDiag_nonneg atomZ)
    (data.captureDiag_nonneg atomW) (data.captureDiag_lt_one atomY)
    (data.captureDiag_lt_one atomZ) (data.captureDiag_lt_one atomW)
    (data.shiftedGapDiag_pos atomY) (data.shiftedGapDiag_pos atomZ)
    (data.shiftedGapDiag_pos atomW)
    (data.gapBlockRankOne_of_straddle_slot hYZ hYW hZW hsupport hminor)

/-- **THE STRADDLE BUDGET AGAINST THE SHARED TRIPLE.**  A further slot
whose support carries two atoms of the shared rank-one triple pays a
single unit on its OWN support.  This is the practical form of case C:
the shared triple supplies the pair minor by membership alone. -/
theorem straddle_shifted_sum_le_one_of_shared (data : SharedPrivateData crux)
    {slot : Fin data.basisCount} {atomU atomV atomS atomY atomZ atomW : Fin 6}
    (hshape : GapBlockRankOne (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) atomU atomV atomS)
    (hYZ : atomY ≠ atomZ) (hYW : atomY ≠ atomW) (hZW : atomZ ≠ atomW)
    (hY : atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)))
    (hZ : atomZ ∈ ({atomU, atomV, atomS} : Finset (Fin 6)))
    (hsupport : datumTightSupport data.tightDir (data.basisLabel slot)
      = {atomY, atomZ, atomW}) :
    shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomY
      + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomZ
      + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomW ≤ 1 :=
  data.straddle_shifted_sum_le_one hYZ hYW hZW hsupport
    (gapPairMinor_of_mem_rankOne_triple data.hdata.isSymmetric hshape hYZ hY hZ)

/-- **THE THIRD SLOT OF THE IDENTICAL BRANCH.**  The pinned slot is
distinct from the two identical slots and its support is a different
triple, thus the identical branch always carries a third support. -/
theorem exists_third_slot_of_identical_support (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hsame : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = datumTightSupport data.tightDir (data.basisLabel slotOne)) :
    ∃ slotThree : Fin data.basisCount, slotThree ≠ slotOne ∧ slotThree ≠ slotTwo
      ∧ datumTightSupport data.tightDir (data.basisLabel slotThree)
        ≠ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
  obtain ⟨hOne, hTwo⟩ := data.privateSlot_notMem_identical_pair hne hsame
  exact ⟨data.privateSlot, hOne, hTwo,
    data.privateSlot_support_ne_of_identical hne hsame⟩

/-- **THE CASE SPLIT OF THE THIRD SLOT.**  A basis slot either carries an
atom of the shared triple, and then it straddles, or it misses the shared
triple entirely and then it IS the complement triple. -/
theorem slot_straddle_or_complement (data : SharedPrivateData crux)
    (slot : Fin data.basisCount) {atomU atomV atomS : Fin 6}
    (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS) (hVS : atomV ≠ atomS) :
    (∃ atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
        atomY ∈ datumTightSupport data.tightDir (data.basisLabel slot))
      ∨ datumTightSupport data.tightDir (data.basisLabel slot)
        = Finset.univ \ ({atomU, atomV, atomS} : Finset (Fin 6)) := by
  classical
  by_cases hmeet : ∃ atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
      atomY ∈ datumTightSupport data.tightDir (data.basisLabel slot)
  · exact Or.inl hmeet
  · refine Or.inr (data.support_eq_complement_of_disjoint ?_ ?_)
    · rw [Finset.card_insert_of_notMem (by simp [hUV, hUS]),
        Finset.card_insert_of_notMem (by simp [hVS]), Finset.card_singleton]
    · intro atomIndex hmem hshared
      exact hmeet ⟨atomIndex, hshared, hmem⟩

end SharedPrivateData

/-! ## Layer 7 — the identical residue on the slot-split lattice -/

/-- **THE SLOT-SPLIT IDENTICAL RESIDUE.**  The identical-support branch
carries every payment of the complement ledger AND the four payments of
the slot case split:

* the singular block budget at EVERY basis support,
* the pin slot as a genuine third slot,
* the refusal of a second identical pair on the complement triple,
* the rank-one budget of every straddling support.

Only the case that no further slot straddles the shared triple in two
atoms and no further pair repeats a support remains open. -/
def SharedPrivateCircuitPairIdenticalSlotClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      (∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
        data.labelCoeff label slot = 0) →
      ∀ atomU atomV atomS : Fin 6, atomU ≠ atomV → atomU ≠ atomS → atomV ≠ atomS →
        datumTightSupport data.tightDir (data.basisLabel slotOne)
          = {atomU, atomV, atomS} →
        datumTightSupport data.tightDir (data.basisLabel slotTwo)
          = {atomU, atomV, atomS} →
        GapBlockRankOne (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design)) atomU atomV atomS →
        data.pinAtom ∉ datumTightSupport data.tightDir (data.basisLabel slotOne) →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomU
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomV
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomS ≤ 1 →
        1 - 6 * chartObjective (chartPointOfDesign crux.design)
          ≤ ∑ atomIndex ∈ Finset.univ \ ({atomU, atomV, atomS} : Finset (Fin 6)),
              shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomIndex →
        (∀ atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
          shiftedGapDiag (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight
              (chartObjective (chartPointOfDesign crux.design)) atomY
              * ((∑ atomIndex ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
                    shiftedGapDiag (chartPointOfDesign crux.design).chart
                      (chartPointOfDesign crux.design).weight
                      (chartObjective (chartPointOfDesign crux.design)) atomIndex)
                + 2 * (chartObjective (chartPointOfDesign crux.design)
                  + (chartPointOfDesign crux.design).weight atomY) - 1)
            ≤ (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomY)
              * (1 - (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomY))) →
        (∀ atomP atomQ atomR : Fin 6, atomP ≠ atomQ → atomP ≠ atomR → atomQ ≠ atomR →
          ({atomU, atomV, atomS} : Finset (Fin 6)) ∪ {atomP, atomQ, atomR}
              = Finset.univ →
          ¬ GapBlockRankOne (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomP atomQ atomR) →
        -- the singular block budget at every basis support
        (∀ slot : Fin data.basisCount,
          ∑ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
              shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomIndex ≤ 2) →
        -- the pin slot is a genuine third slot with a different support
        (data.privateSlot ≠ slotOne ∧ data.privateSlot ≠ slotTwo
          ∧ datumTightSupport data.tightDir (data.basisLabel data.privateSlot)
            ≠ ({atomU, atomV, atomS} : Finset (Fin 6))) →
        -- no second identical pair on the complement triple
        (∀ slotThree slotFour : Fin data.basisCount,
          ∀ atomP atomQ atomR : Fin 6, atomP ≠ atomQ → atomP ≠ atomR → atomQ ≠ atomR →
            ({atomU, atomV, atomS} : Finset (Fin 6)) ∪ {atomP, atomQ, atomR}
                = Finset.univ →
            slotThree ≠ slotFour →
            datumTightSupport data.tightDir (data.basisLabel slotThree)
              = {atomP, atomQ, atomR} →
            datumTightSupport data.tightDir (data.basisLabel slotFour)
              = {atomP, atomQ, atomR} →
            False) →
        -- every straddling support pays a single unit
        (∀ slotThree : Fin data.basisCount, ∀ atomY atomZ atomW : Fin 6,
          atomY ≠ atomZ → atomY ≠ atomW → atomZ ≠ atomW →
            atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) →
            atomZ ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) →
            datumTightSupport data.tightDir (data.basisLabel slotThree)
              = {atomY, atomZ, atomW} →
            shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomY
              + shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomZ
              + shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomW ≤ 1) →
        False

/-- **THE SLOT-SPLIT PAYMENT BRIDGE.**  Every hypothesis that the
slot-split residue adds is a theorem at the datum, thus the slot-split
residue closes the ledger residue. -/
theorem sharedPrivateCircuitPairIdenticalLedgerClosed_of_slotSplit
    (hpaid : SharedPrivateCircuitPairIdenticalSlotClosed) :
    SharedPrivateCircuitPairIdenticalLedgerClosed := by
  intro crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomU atomV atomS hUV hUS hVS hsupportOne hsupportTwo hshape hpin hbudget
    hcomplement hleak hnotRankOne
  have hsame : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne, hsupportTwo]
  obtain ⟨hpinOne, hpinTwo⟩ := data.privateSlot_notMem_identical_pair hne hsame
  refine hpaid crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomU atomV atomS hUV hUS hVS hsupportOne hsupportTwo hshape hpin hbudget
    hcomplement hleak hnotRankOne
    (fun slot => data.basis_block_shifted_sum_le_two slot)
    ⟨hpinOne, hpinTwo, ?_⟩
    (fun slotThree slotFour atomP atomQ atomR hPQ hPR hQR hcover hneOther
      hsupportThree hsupportFour =>
      data.false_of_complement_identical_pair hne hneOther hUV hUS hVS hPQ hPR hQR
        hcover hsupportOne hsupportTwo hsupportThree hsupportFour)
    fun slotThree atomY atomZ atomW hYZ hYW hZW hY hZ hsupportThree =>
      data.straddle_shifted_sum_le_one_of_shared hshape hYZ hYW hZW hY hZ hsupportThree
  rw [← hsupportOne]
  exact data.privateSlot_support_ne_of_identical hne hsame

/-! ## Layer 8 — the live-wedge residue on the slot-split lattice -/

/-- **THE PAID LIVE-WEDGE RESIDUE.**  The live-wedge branch with its five
budgets: the two support budgets of the wedge slots, the two combination
budgets of the triples that drop one shared atom, and the four-set budget
of the union.  The four triples together cap the four-set at `8/3`, which
is strictly better than the union budget alone. -/
def SharedPrivateCircuitSplitWedgeSlotClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      (∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
        data.labelCoeff label slot = 0) →
      ∀ atomA atomB atomX atomY : Fin 6,
        atomA ≠ atomB → atomA ≠ atomX → atomA ≠ atomY →
        atomB ≠ atomX → atomB ≠ atomY → atomX ≠ atomY →
        datumTightSupport data.tightDir (data.basisLabel slotOne)
          = {atomA, atomB, atomX} →
        datumTightSupport data.tightDir (data.basisLabel slotTwo)
          = {atomA, atomB, atomY} →
        (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
          *ᵥ data.tightDir (data.basisLabel slotTwo)) atomX = 0 →
        (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
          *ᵥ data.tightDir (data.basisLabel slotOne)) atomY = 0 →
        data.tightDir (data.basisLabel slotOne) atomA
            * data.tightDir (data.basisLabel slotTwo) atomB
          - data.tightDir (data.basisLabel slotOne) atomB
            * data.tightDir (data.basisLabel slotTwo) atomA ≠ 0 →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomA
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomB
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomX ≤ 2 →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomA
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomB
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomY ≤ 2 →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomB
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomX
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomY ≤ 2 →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomA
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomX
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomY ≤ 2 →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomA
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomB
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomX
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomY ≤ 3 →
        False

/-- **THE LIVE-WEDGE PAYMENT BRIDGE.**  All five budgets are theorems at
the datum, thus the paid live-wedge residue closes the plain one. -/
theorem sharedPrivateCircuitSplitWedgeClosed_of_slotSplit
    (hpaid : SharedPrivateCircuitSplitWedgeSlotClosed) :
    SharedPrivateCircuitSplitWedgeClosed := by
  intro crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomA atomB atomX atomY hAB hAX hAY hBX hBY hXY hsupportOne hsupportTwo
    hforeignX hforeignY hwedge
  have hswapOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomB, atomA, atomX} := by rw [hsupportOne, Finset.insert_comm]
  have hswapTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomB, atomA, atomY} := by rw [hsupportTwo, Finset.insert_comm]
  exact hpaid crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomA atomB atomX atomY hAB hAX hAY hBX hBY hXY hsupportOne hsupportTwo
    hforeignX hforeignY hwedge
    (data.basis_triple_shifted_sum_le_two hAB hAX hBX hsupportOne)
    (data.basis_triple_shifted_sum_le_two hAB hAY hBY hsupportTwo)
    (data.liveWedge_triple_shifted_sum_le_two hAB hAX hAY hBX hBY hXY
      hsupportOne hsupportTwo hforeignX hforeignY)
    (data.liveWedge_triple_shifted_sum_le_two (Ne.symm hAB) hBX hBY hAX hAY hXY
      hswapOne hswapTwo hforeignX hforeignY)
    (data.foreign_quad_shifted_sum_le_three hAB hAX hAY hBX hBY hXY
      hsupportOne hforeignY)

/-- **THE EXTRAS FROM THE SLOT-SPLIT LATTICE.** -/
theorem sharedPrivateExtrasClosed_of_slotSplit_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalSlotClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateExtrasClosed :=
  sharedPrivateExtrasClosed_of_ledger_lattice
    (sharedPrivateCircuitPairIdenticalLedgerClosed_of_slotSplit hidentical) hwedgeLive
    hwedgeDead hwide

/-- **THE WHOLE OF CLOSURE TWO ON THE SLOT-SPLIT LATTICE.** -/
theorem sharedPrivateKilled_of_slotSplit_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalSlotClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_ledger_lattice
    (sharedPrivateCircuitPairIdenticalLedgerClosed_of_slotSplit hidentical) hwedgeLive
    hwedgeDead hwide hconfined

/-- Closure two of the rank-four rung on the slot-split lattice. -/
theorem rankFourSharedPrivateClosed_of_slotSplit_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalSlotClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_ledger_lattice
    (sharedPrivateCircuitPairIdenticalLedgerClosed_of_slotSplit hidentical) hwedgeLive
    hwedgeDead hwide hconfined

/-- The shared-private closure of the rank-five rung on the slot-split
lattice. -/
theorem rankFiveSharedPrivateClosed_of_slotSplit_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalSlotClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_ledger_lattice
    (sharedPrivateCircuitPairIdenticalLedgerClosed_of_slotSplit hidentical) hwedgeLive
    hwedgeDead hwide hconfined

/-- The shared-private closure of the rank-six rung on the slot-split
lattice. -/
theorem rankSixSharedPrivateClosed_of_slotSplit_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalSlotClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_ledger_lattice
    (sharedPrivateCircuitPairIdenticalLedgerClosed_of_slotSplit hidentical) hwedgeLive
    hwedgeDead hwide hconfined

/-! ## Layer 9 — the fully paid slot lattice -/

/-- **CLOSURE TWO FROM THE FOUR CIRCUIT RESIDUES ALONE.**  The trace-two
boundary stratum is a theorem and a datum never has a diagonal Gram core,
thus the extras residue IS the generic kill.  The four circuit residues
on the slot-split lattice therefore discharge closure two with NO
boundary hypothesis. -/
theorem sharedPrivateKilled_of_slotSplit_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalSlotClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_extras
    (sharedPrivateExtrasClosed_of_slotSplit_lattice hidentical
      (sharedPrivateCircuitSplitWedgeClosed_of_slotSplit hwedgeLive) hwedgeDead hwide)

/-- Closure two of the rank-four rung from the four circuit residues. -/
theorem rankFourSharedPrivateClosed_of_slotSplit_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalSlotClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_extras
    (sharedPrivateExtrasClosed_of_slotSplit_lattice hidentical
      (sharedPrivateCircuitSplitWedgeClosed_of_slotSplit hwedgeLive) hwedgeDead hwide)

/-- The shared-private closure of the rank-five rung from the four
circuit residues.  The rank-five rung still carries this closure on its
critical path. -/
theorem rankFiveSharedPrivateClosed_of_slotSplit_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalSlotClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_extras
    (sharedPrivateExtrasClosed_of_slotSplit_lattice hidentical
      (sharedPrivateCircuitSplitWedgeClosed_of_slotSplit hwedgeLive) hwedgeDead hwide)

/-- The shared-private closure of the rank-six rung from the four circuit
residues. -/
theorem rankSixSharedPrivateClosed_of_slotSplit_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalSlotClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_extras
    (sharedPrivateExtrasClosed_of_slotSplit_lattice hidentical
      (sharedPrivateCircuitSplitWedgeClosed_of_slotSplit hwedgeLive) hwedgeDead hwide)


/-- **THE EXTRAS ON THE FULLY PAID SLOT LATTICE.**  Both the identical
residue and the live-wedge residue carry their slot payments. -/
theorem sharedPrivateExtrasClosed_of_slotLattice
    (hidentical : SharedPrivateCircuitPairIdenticalSlotClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateExtrasClosed :=
  sharedPrivateExtrasClosed_of_slotSplit_lattice hidentical
    (sharedPrivateCircuitSplitWedgeClosed_of_slotSplit hwedgeLive) hwedgeDead hwide

/-- **CLOSURE TWO ON THE FULLY PAID SLOT LATTICE.** -/
theorem sharedPrivateKilled_of_slotLattice
    (hidentical : SharedPrivateCircuitPairIdenticalSlotClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_slotSplit_lattice hidentical
    (sharedPrivateCircuitSplitWedgeClosed_of_slotSplit hwedgeLive) hwedgeDead hwide
    hconfined

/-- Closure two of the rank-four rung on the fully paid slot lattice. -/
theorem rankFourSharedPrivateClosed_of_slotLattice
    (hidentical : SharedPrivateCircuitPairIdenticalSlotClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_slotSplit_lattice hidentical
    (sharedPrivateCircuitSplitWedgeClosed_of_slotSplit hwedgeLive) hwedgeDead hwide
    hconfined

/-- The shared-private closure of the rank-five rung on the fully paid
slot lattice. -/
theorem rankFiveSharedPrivateClosed_of_slotLattice
    (hidentical : SharedPrivateCircuitPairIdenticalSlotClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_slotSplit_lattice hidentical
    (sharedPrivateCircuitSplitWedgeClosed_of_slotSplit hwedgeLive) hwedgeDead hwide
    hconfined

/-- The shared-private closure of the rank-six rung on the fully paid
slot lattice. -/
theorem rankSixSharedPrivateClosed_of_slotLattice
    (hidentical : SharedPrivateCircuitPairIdenticalSlotClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_slotSplit_lattice hidentical
    (sharedPrivateCircuitSplitWedgeClosed_of_slotSplit hwedgeLive) hwedgeDead hwide
    hconfined

end Gtz

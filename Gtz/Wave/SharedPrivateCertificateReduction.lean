import Gtz.Wave.RankFourRungAssembly
import Gtz.Wave.RankFiveRungAssembly
import Gtz.Wave.RankSixRungAssembly
import Gtz.Wave.SupportTwoRayleighKill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The shared-private certificate reduction — one kill target for three rungs

The shared-private closure shape occurs at the three rungs: closure two
of the rank-four assembly, and the shared-private closures at ranks five
and six.  The three hypothesis lists agree.  This file gives the shape
once, over a generic basis count with the trace disjunction, and the
three bridges prove the closure propositions from the one generic kill.

The numeric extraction of this campaign fixed the certificate frame.  The
free-core frame with the Gamma layer kills every rank-four shape and
every rank-five shape at trace three, with floors linear in the value.
At trace two of rank five, one shape admits an exact frame witness, and
the witness puts `value + weight = 0` at the shared atom.  At rank six,
two shapes admit frame witnesses with an interior escape.  The heavy
diagonal floor closes the rank-six escapes, and the diagonal legality of
the Gram core closes the trace-two escape.  Thus the generic kill must
consume the ambient datum, not the frame algebra alone.  The boundary
laws of this file kill the `value + weight = 0` stratum: the captured
column dies, the projected axis falls into the assembly kernel, and a
kernel-free assembly with the heavy floor refuses the stratum.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.capture_column_eq_zero_of_diagonal_zero` — a zero captured
  diagonal kills the captured column.
* `Gtz.assembly_mulVec_projection_single_of_diagonal_zero` — the
  projected axis falls into the assembly kernel.
* `Gtz.capture_diagonal_pos_of_kernel_free` — **THE STRICT WEIGHT
  FLOOR**: a kernel-free assembly with the heavy diagonal floor forces
  `0 < value + weight` at every atom.
* `Gtz.SharedPrivateData` with `Gtz.SharedPrivateKilled` — **THE GENERIC
  KILL TARGET.**
* `Gtz.SharedPrivateData.hvalueNeg` — the value is negative at every
  datum of the kill target.
* `Gtz.rankFourSharedPrivateClosed_of_killed`,
  `Gtz.rankFiveSharedPrivateClosed_of_killed`,
  `Gtz.rankSixSharedPrivateClosed_of_killed` — **THE THREE BRIDGES.**

## Vacuity

The three bridges are vacuous if `Gtz.GtzWeighted 6 3` holds: no crux
exists, thus no frame exists.  The boundary laws quantify over stationary
data only, and they are unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## The boundary laws of the captured diagonal -/

/-- A zero captured diagonal kills the captured column.  The capture
`P * Xi` is positive semidefinite, and its diagonal at the atom reads
`(value + weight) / size`. -/
theorem capture_column_eq_zero_of_diagonal_zero
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {atomIndex : Fin size} (hzero : value + weight atomIndex = 0)
    (rowIndex : Fin size) :
    (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
      rowIndex atomIndex = 0 :=
  posSemidef_col_eq_zero_of_diag_eq_zero
    (posSemidef_projection_mul_multiplier_of_isChartStationaryData hdata)
    (by rw [diagonal_projection_mul_multiplier_of_isChartStationaryData
        hdata atomIndex, hzero, zero_mul])
    rowIndex

/-- The projected axis falls into the assembly kernel when the captured
diagonal vanishes: `Xi *ᵥ (P *ᵥ e_y) = 0` at `value + weight y = 0`. -/
theorem assembly_mulVec_projection_single_of_diagonal_zero
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {atomIndex : Fin size} (hzero : value + weight atomIndex = 0) :
    chartMultiplierAssembly activeSet activeWeight tightDir
      *ᵥ (projection *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ)) = 0 := by
  have hcol : (projection
      * chartMultiplierAssembly activeSet activeWeight tightDir)
      *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ) = 0 := by
    funext rowIndex
    have happly : ((projection
        * chartMultiplierAssembly activeSet activeWeight tightDir)
        *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ)) rowIndex
        = (projection
            * chartMultiplierAssembly activeSet activeWeight tightDir)
          rowIndex atomIndex := by
      rw [Matrix.mulVec_single_one]
      simp [Matrix.col]
    rw [happly, capture_column_eq_zero_of_diagonal_zero hdata hzero rowIndex]
    rfl
  calc chartMultiplierAssembly activeSet activeWeight tightDir
      *ᵥ (projection *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ))
      = (chartMultiplierAssembly activeSet activeWeight tightDir
          * projection) *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ) := by
        rw [Matrix.mulVec_mulVec]
    _ = (projection
          * chartMultiplierAssembly activeSet activeWeight tightDir)
        *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ) := by
        rw [hdata.assembly_commutes]
    _ = 0 := hcol

/-- **THE STRICT WEIGHT FLOOR.**  A kernel-free assembly with the heavy
diagonal floor forces `0 < value + weight` at every atom.  At the zero
boundary the projected axis dies in the assembly kernel, thus the chart
diagonal vanishes below the positive weight. -/
theorem capture_diagonal_pos_of_kernel_free
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (hker : ∀ probe : Fin size → ℝ,
      chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ probe = 0 →
      probe = 0)
    {atomIndex : Fin size}
    (hheavy : weight atomIndex < projection atomIndex atomIndex) :
    0 < value + weight atomIndex := by
  rcases (capture_diagonal_nonneg_of_isChartStationaryData hdata
      atomIndex).lt_or_eq with hpos | heq
  · exact hpos
  · exfalso
    have hann := assembly_mulVec_projection_single_of_diagonal_zero hdata
      heq.symm
    have hproj : projection *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ) = 0 :=
      hker _ hann
    have hdiagP := single_dotProduct_mulVec_single projection atomIndex
    rw [hproj, dotProduct_zero] at hdiagP
    linarith [hdata.weight_pos atomIndex]

/-! ## The generic kill target -/

/-- **THE SHARED-PRIVATE DATA.**  The one shape behind closure two of
rank four and the shared-private closures of ranks five and six: the
reduced datum, a basis of generic count with the coefficient triple and
its laws, the trace disjunction, the pinned private atom, and the shared
atom of the pinned slot.  The certificate kill consumes this structure
and nothing else. -/
structure SharedPrivateData (crux : SixThreeCrux) where
  /-- The basis count: four, five, or six at the three rungs. -/
  basisCount : ℕ
  /-- The label type of the datum. -/
  activeIndex : Type
  /-- The active label set. -/
  activeSet : Finset activeIndex
  /-- The block of each label. -/
  activeSubset : activeIndex → Finset (Fin 6)
  /-- The reduced multiplier weights. -/
  reducedWeight : activeIndex → ℝ
  /-- The tight directions. -/
  tightDir : activeIndex → Fin 6 → ℝ
  /-- The basis labels. -/
  basisLabel : Fin basisCount → activeIndex
  /-- The left inverse of the basis columns. -/
  leftInv : Matrix (Fin basisCount) (Fin 6) ℝ
  /-- The coefficient matrix of the projection. -/
  coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ
  /-- The coefficient Gram core. -/
  gram : Matrix (Fin basisCount) (Fin basisCount) ℝ
  /-- The reduced datum is stationary. -/
  hdata : IsChartStationaryData 3
    (chartPointOfDesign crux.design).chart
    (chartPointOfDesign crux.design).weight
    (chartObjective (chartPointOfDesign crux.design))
    activeSet activeSubset reducedWeight tightDir
  /-- The basis is injective. -/
  hinjective : Function.Injective basisLabel
  /-- Every basis label is positive. -/
  hmem : ∀ columnIndex, basisLabel columnIndex
    ∈ positiveActiveSet activeSet reducedWeight
  /-- The basis spans the assembly range. -/
  hspan : Submodule.span ℝ
      (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
    = LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet reducedWeight tightDir))
  /-- The left inverse law. -/
  hleft : leftInv * tightBasisColumns tightDir basisLabel = 1
  /-- The coefficient representation of the projection. -/
  hrepresentation : (chartPointOfDesign crux.design).chart
      * tightBasisColumns tightDir basisLabel
    = tightBasisColumns tightDir basisLabel * coeff
  /-- The coefficient matrix is idempotent. -/
  hidempotent : coeff * coeff = coeff
  /-- The Gram form of the assembly. -/
  hHform : tightBasisColumns tightDir basisLabel * gram
      * (tightBasisColumns tightDir basisLabel)ᵀ
    = chartMultiplierAssembly activeSet reducedWeight tightDir
  /-- The Gram core is symmetric. -/
  hsymmH : gramᵀ = gram
  /-- The Gram core is positive semidefinite. -/
  hpsd : gram.PosSemidef
  /-- The Gram core has a trivial kernel. -/
  hker : ∀ coeffVec : Fin basisCount → ℝ, gram *ᵥ coeffVec = 0 → coeffVec = 0
  /-- The exchange law. -/
  hexchange : coeff * gram = gram * coeffᵀ
  /-- The trace disjunction across the three rungs. -/
  htrace : Matrix.trace coeff = 2 ∨ Matrix.trace coeff = 3
  /-- The pinned slot. -/
  privateSlot : Fin basisCount
  /-- The pinned multiplicity-one atom. -/
  pinAtom : Fin 6
  /-- The shared atom of the pinned slot. -/
  sharedAtom : Fin 6
  /-- Every basis support has cardinality three. -/
  hthree : ∀ columnIndex, (datumTightSupport tightDir
    (basisLabel columnIndex)).card = 3
  /-- The pin atom has multiplicity one. -/
  hmultOne : basisSupportMultiplicity tightDir basisLabel pinAtom = 1
  /-- The pin atom sits in the pinned slot's block. -/
  hpinMem : pinAtom ∈ activeSubset (basisLabel privateSlot)
  /-- The pinned slot's direction is nonzero at the pin atom. -/
  hpinNe : tightDir (basisLabel privateSlot) pinAtom ≠ 0
  /-- The other basis directions vanish at the pin atom. -/
  hprivate : ∀ columnIndex, columnIndex ≠ privateSlot →
    tightDir (basisLabel columnIndex) pinAtom = 0
  /-- The diagonal pin at the pinned slot. -/
  hpin : coeff privateSlot privateSlot
    = chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight pinAtom
  /-- The shared atom sits in the pinned slot's support. -/
  hsharedMem : sharedAtom ∈ datumTightSupport tightDir
    (basisLabel privateSlot)
  /-- The shared atom has multiplicity at least two. -/
  hsharedMult : 2 ≤ basisSupportMultiplicity tightDir basisLabel sharedAtom

/-- The value is negative at every datum of the kill target. -/
theorem SharedPrivateData.hvalueNeg {crux : SixThreeCrux}
    (_data : SharedPrivateData crux) :
    chartObjective (chartPointOfDesign crux.design) < 0 :=
  crux.hasNegativeChartValue

/-- **THE GENERIC KILL TARGET.**  Every shared-private datum dies.  One
certificate at this level discharges the three closure propositions
through the bridges. -/
def SharedPrivateKilled : Prop :=
  ∀ (crux : SixThreeCrux), SharedPrivateData crux → False

/-! ## The three bridges -/

/-- **THE RANK-FOUR BRIDGE.**  The generic kill discharges closure two
of the rank-four rung. -/
theorem rankFourSharedPrivateClosed_of_killed
    (hkill : SharedPrivateKilled) : RankFourSharedPrivateClosed := by
  intro crux frame privateSlot pinAtom sharedAtom hthree hmultOne hatomMem
    hslotNe hprivate hpin hsharedMem hsharedMult
  exact hkill crux
    ⟨4, frame.activeIndex, frame.activeSet, frame.activeSubset,
      frame.reducedWeight, frame.tightDir, frame.basisLabel, frame.leftInv,
      frame.coeff, frame.gram, frame.hdata, frame.hinjective, frame.hmem,
      frame.hspan, frame.hleft, frame.hrepresentation, frame.hidempotent,
      frame.hHform, frame.hsymmH, frame.hpsd, frame.hker, frame.hexchange,
      Or.inl frame.htrace, privateSlot, pinAtom, sharedAtom, hthree,
      hmultOne, hatomMem, hslotNe, hprivate, hpin, hsharedMem, hsharedMult⟩

/-- **THE RANK-FIVE BRIDGE.**  The generic kill discharges the
shared-private closure of the rank-five rung. -/
theorem rankFiveSharedPrivateClosed_of_killed
    (hkill : SharedPrivateKilled) : RankFiveSharedPrivateClosed := by
  intro crux frame privateSlot pinAtom sharedAtom hthree hmultOne hatomMem
    hslotNe hprivate hpin hsharedMem hsharedMult
  exact hkill crux
    ⟨5, frame.activeIndex, frame.activeSet, frame.activeSubset,
      frame.reducedWeight, frame.tightDir, frame.basisLabel, frame.leftInv,
      frame.coeff, frame.gram, frame.hdata, frame.hinjective, frame.hmem,
      frame.hspan, frame.hleft, frame.hrepresentation, frame.hidempotent,
      frame.hHform, frame.hsymmH, frame.hpsd, frame.hker, frame.hexchange,
      frame.htrace, privateSlot, pinAtom, sharedAtom, hthree, hmultOne,
      hatomMem, hslotNe, hprivate, hpin, hsharedMem, hsharedMult⟩

/-- **THE RANK-SIX BRIDGE.**  The generic kill discharges the
shared-private closure of the rank-six rung. -/
theorem rankSixSharedPrivateClosed_of_killed
    (hkill : SharedPrivateKilled) : RankSixSharedPrivateClosed := by
  intro crux frame privateSlot pinAtom sharedAtom hthree hmultOne hatomMem
    hslotNe hprivate hpin hsharedMem hsharedMult
  exact hkill crux
    ⟨6, frame.activeIndex, frame.activeSet, frame.activeSubset,
      frame.reducedWeight, frame.tightDir, frame.basisLabel, frame.leftInv,
      frame.coeff, frame.gram, frame.hdata, frame.hinjective, frame.hmem,
      frame.hspan, frame.hleft, frame.hrepresentation, frame.hidempotent,
      frame.hHform, frame.hsymmH, frame.hpsd, frame.hker, frame.hexchange,
      Or.inr frame.htrace, privateSlot, pinAtom, sharedAtom, hthree,
      hmultOne, hatomMem, hslotNe, hprivate, hpin, hsharedMem, hsharedMult⟩

end Gtz

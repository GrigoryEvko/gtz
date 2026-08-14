import Gtz.Wave.CaptureLineWideKill
import Gtz.Wave.AtomTrineCutBand
import Gtz.Wave.AtomShadowTransfer
import Gtz.Wave.DenseCeilingCollapse
import Gtz.Reduction.ChartPointFactorisation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The atom form of the wide spectral residue

`Gtz.WideSpectralSelectionClosed` is a statement about two matrices of
size six and one vector.  This module gives it its NORMAL FORM and orders
it against the atom lane.

The normal form is the orthonormal frame of the projection.  A symmetric
idempotent of trace three factors as `E Eᵀ` with `Eᵀ E = 1`, thus its
rows are six atoms of three-space that carry a Parseval frame law, its
entries are the atom Gram, and the chart energy of a probe is the squared
norm of the atom blend.  The price matrix then reads as a quadratic form
of the atoms through a positive semidefinite three-by-three form that the
frame reading of the fixed vector kills.

Two laws price that form.  Its trace is the price total, thus the SCALE
MASS OF THE NORMALIZED READS IS EXACTLY ONE.  And a positive semidefinite
form never exceeds its own trace, thus each scale plus the squared free
coordinate never exceeds the atom diagonal.  The second law is the whole
supply of the rank-two structure, and the first law places the residue at
the BOUNDARY of the atom triple ceiling, not below it.

That boundary is not a weaker place.  The scaled strict form and the
weak boundary form are EQUIVALENT: a finite carrier count turns a
one-parameter family of strict statements into one weak statement, and
the normalization turns the weak statement back into the strict one.
Thus the atom triple ceiling discharges the wide residue, the whole
rank-four rung and the cell.

Three unconditional pieces come with the normal form.  The PAIR at the
boundary always exists, because the plane pair ceiling is landed and the
shadow of a Parseval frame is a Parseval frame of the plane.  The FREE
PIVOT always exists, because the squared free coordinates and the scales
both sum to one.  And a POSITIVE PARITY TRIPLE always exists, because
atom signs are free and five vectors of three-space are never pairwise
strictly obtuse.  The last piece is the real-only ingredient: over the
complex field the entry products are not real, there is no sign, and the
complex two-trine satisfies every hypothesis of the residue and refutes
its conclusion.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.wideFrameAtom`, `Gtz.wideFrameAtom_dot`, `Gtz.wideFrameAtom_gram`,
  `Gtz.wideFrameAtom_frameLaw`, `Gtz.wideFrameAtom_blend_energy` — **THE
  FRAME DICTIONARY**: the rows of an orthonormal frame are Parseval
  atoms whose Gram is the projection and whose blend energy is the chart
  energy.
* `Gtz.entry_sq_le_diag_mul_diag`, `Gtz.quadratic_le_trace_mul_energy` —
  **THE TRACE CEILING** of a positive semidefinite form.
* `Gtz.price_quadratic_le_trace_mul_shift` — **THE RANK-TWO PRICE
  BOUND**: the price form never exceeds its trace against the chart
  energy less the squared fixed reading.
* `Gtz.WideAtomSelectionClosed` — **THE RESIDUE IN ATOM FORM**, and
  `Gtz.wideSpectralSelectionClosed_of_wideAtomSelection` — the normal
  form reduction.
* `Gtz.AtomTripleBoundaryClosed`,
  `Gtz.atomTripleCeilingClosed_iff_boundary` — **THE BOUNDARY IS THE
  CEILING**, an equivalence.
* `Gtz.wideSpectralSelectionClosed_of_atomTripleCeiling` and the whole
  discharged spine — **THE WIDE RESIDUE IS BELOW THE ATOM CEILING**.
* `Gtz.exists_dominating_pair_of_boundary` — **THE BOUNDARY PAIR IS
  UNCONDITIONAL.**
* `Gtz.exists_freePivot` — **THE FREE PIVOT.**
* `Gtz.exists_nonneg_dot_off_pivot`, `Gtz.exists_positiveParity_triple`,
  `Gtz.exists_nonnegCross_triple` — **THE PARITY ENGINE**, the real-only
  ingredient.
* `Gtz.exists_dominating_triple_of_pair_correction` — the extension
  criterion at the boundary, where the margin factor is exactly zero.

## Vacuity

Every statement of this module is an unconditional matrix statement or a
reduction between two unconditional matrix statements.  Nothing here is
quantified over a crux.
-/

namespace Gtz

open Matrix

/-! ## Layer 0 — the frame dictionary -/

section FrameDictionary

/-- The ATOMS OF A FRAME: the rows of a six-by-three matrix, read as six
vectors of three-space. -/
def wideFrameAtom (frame : Matrix (Fin 6) (Fin 3) ℝ) : Fin 6 → (Fin 3 → ℝ) :=
  fun slot index => frame slot index

theorem wideFrameAtom_apply (frame : Matrix (Fin 6) (Fin 3) ℝ) (slot : Fin 6)
    (index : Fin 3) : wideFrameAtom frame slot index = frame slot index := rfl

/-- The dot product of two frame atoms is the entry of the square of the
frame. -/
theorem wideFrameAtom_dot (frame : Matrix (Fin 6) (Fin 3) ℝ) (rowSlot colSlot : Fin 6) :
    wideFrameAtom frame rowSlot ⬝ᵥ wideFrameAtom frame colSlot
      = (frame * frameᵀ) rowSlot colSlot := by
  rw [Matrix.mul_apply, dotProduct]
  exact Finset.sum_congr rfl fun index _ => by
    rw [Matrix.transpose_apply, wideFrameAtom_apply, wideFrameAtom_apply]

/-- The atom Gram of a frame is the projection that the frame builds. -/
theorem wideFrameAtom_gram {frame : Matrix (Fin 6) (Fin 3) ℝ}
    {proj : Matrix (Fin 6) (Fin 6) ℝ} (hframe : frame * frameᵀ = proj)
    (rowSlot colSlot : Fin 6) :
    atomGram (wideFrameAtom frame) rowSlot colSlot = proj rowSlot colSlot := by
  rw [atomGram, wideFrameAtom_dot, hframe]

/-- **THE FRAME LAW OF AN ORTHONORMAL FRAME.**  The rows of a frame of
orthonormal columns carry the Parseval law of three-space. -/
theorem wideFrameAtom_frameLaw {frame : Matrix (Fin 6) (Fin 3) ℝ}
    (hortho : frameᵀ * frame = 1) (probe direction : Fin 3 → ℝ) :
    (∑ slot, (wideFrameAtom frame slot ⬝ᵥ probe)
        * (wideFrameAtom frame slot ⬝ᵥ direction))
      = probe ⬝ᵥ direction := by
  classical
  have hcolumn : ∀ rowIndex colIndex : Fin 3,
      (∑ slot, frame slot rowIndex * frame slot colIndex)
        = (1 : Matrix (Fin 3) (Fin 3) ℝ) rowIndex colIndex := by
    intro rowIndex colIndex
    rw [← hortho, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun slot _ => by rw [Matrix.transpose_apply]
  have hexpand : ∀ slot : Fin 6,
      (wideFrameAtom frame slot ⬝ᵥ probe) * (wideFrameAtom frame slot ⬝ᵥ direction)
        = ∑ rowIndex, ∑ colIndex,
            (frame slot rowIndex * frame slot colIndex)
              * (probe rowIndex * direction colIndex) := by
    intro slot
    rw [dotProduct, dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun rowIndex _ =>
      Finset.sum_congr rfl fun colIndex _ => by
        rw [wideFrameAtom_apply, wideFrameAtom_apply]; ring
  rw [Finset.sum_congr rfl fun slot _ => hexpand slot, Finset.sum_comm]
  have hinner : ∀ rowIndex : Fin 3,
      (∑ slot, ∑ colIndex,
          (frame slot rowIndex * frame slot colIndex) * (probe rowIndex * direction colIndex))
        = probe rowIndex * direction rowIndex := by
    intro rowIndex
    rw [Finset.sum_comm]
    have hstep : ∀ colIndex : Fin 3,
        (∑ slot, (frame slot rowIndex * frame slot colIndex)
            * (probe rowIndex * direction colIndex))
          = (1 : Matrix (Fin 3) (Fin 3) ℝ) rowIndex colIndex
            * (probe rowIndex * direction colIndex) := by
      intro colIndex
      rw [← Finset.sum_mul, hcolumn rowIndex colIndex]
    rw [Finset.sum_congr rfl fun colIndex _ => hstep colIndex]
    simp only [Matrix.one_apply, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl fun rowIndex _ => hinner rowIndex, dotProduct]

/-- The blend energy of a frame atom family is the chart energy of the
projection that the frame builds. -/
theorem wideFrameAtom_blend_energy {frame : Matrix (Fin 6) (Fin 3) ℝ}
    {proj : Matrix (Fin 6) (Fin 6) ℝ} (hframe : frame * frameᵀ = proj)
    (probe : Fin 6 → ℝ) :
    atomBlend (wideFrameAtom frame) probe ⬝ᵥ atomBlend (wideFrameAtom frame) probe
      = probe ⬝ᵥ (proj *ᵥ probe) := by
  classical
  rw [atomBlend_energy_eq_gram, dotProduct]
  refine Finset.sum_congr rfl fun rowSlot _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun colSlot _ => by
    rw [wideFrameAtom_gram hframe rowSlot colSlot]; ring

end FrameDictionary

/-! ## Layer 1 — the trace ceiling of a positive semidefinite form -/

section TraceCeiling

variable {size : ℕ}

/-- A matrix against a one-hot vector reads one column. -/
theorem mulVec_oneHot_apply (form : Matrix (Fin size) (Fin size) ℝ)
    (rowSlot colSlot : Fin size) :
    (form *ᵥ Pi.single colSlot (1 : ℝ)) rowSlot = form rowSlot colSlot := by
  classical
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single colSlot]
  · rw [Pi.single_eq_same, mul_one]
  · intro slot _ hslot
    rw [Pi.single_eq_of_ne hslot, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_univ colSlot) hnot

/-- The quadratic form of a one-hot vector is one diagonal entry. -/
theorem oneHot_quadratic (form : Matrix (Fin size) (Fin size) ℝ) (slot : Fin size) :
    Pi.single slot (1 : ℝ) ⬝ᵥ (form *ᵥ Pi.single slot (1 : ℝ)) = form slot slot := by
  rw [single_dotProduct, one_mul, mulVec_oneHot_apply]

/-- **THE TWO-BY-TWO MINOR OF A POSITIVE SEMIDEFINITE FORM.**  The square
of an entry never exceeds the product of the two diagonal entries.  The
proof is the discriminant of the quadratic that a two-slot probe reads. -/
theorem entry_sq_le_diag_mul_diag {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymmetric : formᵀ = form) (hpsd : ∀ vec : Fin size → ℝ, 0 ≤ vec ⬝ᵥ (form *ᵥ vec))
    (rowSlot colSlot : Fin size) :
    form rowSlot colSlot ^ 2 ≤ form rowSlot rowSlot * form colSlot colSlot := by
  classical
  have hcross : ∀ left right : Fin size, form left right = form right left := by
    intro left right
    have hentry := congrFun (congrFun hsymmetric left) right
    rw [Matrix.transpose_apply] at hentry
    exact hentry.symm
  rcases eq_or_ne rowSlot colSlot with heq | hne
  · subst heq
    exact le_of_eq (pow_two _)
  have hquadratic : ∀ step : ℝ,
      0 ≤ form rowSlot rowSlot * (step * step)
        + (2 * form rowSlot colSlot) * step + form colSlot colSlot := by
    intro step
    set probeVec : Fin size → ℝ := fun index =>
      if index = rowSlot then step else if index = colSlot then 1 else 0 with hprobeDef
    have hprobeRow : probeVec rowSlot = step := by rw [hprobeDef]; simp
    have hprobeCol : probeVec colSlot = 1 := by
      rw [hprobeDef]; simp [Ne.symm hne]
    have hprobeOff : ∀ slot ∉ ({rowSlot, colSlot} : Finset (Fin size)), probeVec slot = 0 := by
      intro slot hnot
      rw [Finset.mem_insert, Finset.mem_singleton] at hnot
      push Not at hnot
      rw [hprobeDef]
      simp [hnot.1, hnot.2]
    have hrow : ∀ index : Fin size,
        (form *ᵥ probeVec) index = form index rowSlot * step + form index colSlot * 1 := by
      intro index
      rw [Matrix.mulVec, dotProduct,
        sum_eq_pair_of_support hne (value := fun slot => form index slot * probeVec slot)
          fun slot hnot => by rw [hprobeOff slot hnot, mul_zero],
        hprobeRow, hprobeCol]
    have hvalue := hpsd probeVec
    rw [dotProduct,
      sum_eq_pair_of_support hne (value := fun slot => probeVec slot * (form *ᵥ probeVec) slot)
        fun slot hnot => by rw [hprobeOff slot hnot, zero_mul],
      hprobeRow, hprobeCol, hrow rowSlot, hrow colSlot, hcross colSlot rowSlot] at hvalue
    nlinarith [hvalue]
  have hdiscrim := discrim_le_zero hquadratic
  rw [discrim] at hdiscrim
  nlinarith [hdiscrim]

/-- The pointwise absorption of a cross term against the two diagonal
entries.  It is the arithmetic-geometric bound in a division-free form. -/
theorem two_cross_le_diag_pair {cross diagOne diagTwo valueOne valueTwo : ℝ}
    (hone : 0 ≤ diagOne) (htwo : 0 ≤ diagTwo) (hsq : cross ^ 2 ≤ diagOne * diagTwo) :
    2 * (cross * valueOne * valueTwo)
      ≤ diagOne * valueTwo ^ 2 + diagTwo * valueOne ^ 2 := by
  rcases hone.eq_or_lt with hzero | hpos
  · have hcrossSq : cross ^ 2 ≤ 0 := by rw [← hzero] at hsq; simpa using hsq
    have hcross : cross = 0 := by nlinarith [sq_nonneg cross]
    rw [hcross, ← hzero]
    nlinarith [sq_nonneg valueOne, htwo]
  · nlinarith [sq_nonneg (diagOne * valueTwo - cross * valueOne), sq_nonneg valueOne, hpos]

/-- **THE TRACE CEILING.**  A positive semidefinite form never exceeds its
own trace against the squared norm of the probe.  The proof absorbs each
cross term into the two diagonal entries, and the absorbed total is the
trace against the energy exactly. -/
theorem quadratic_le_trace_mul_energy {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymmetric : formᵀ = form) (hpsd : ∀ vec : Fin size → ℝ, 0 ≤ vec ⬝ᵥ (form *ᵥ vec))
    (probe : Fin size → ℝ) :
    probe ⬝ᵥ (form *ᵥ probe) ≤ Matrix.trace form * (probe ⬝ᵥ probe) := by
  classical
  have hdiagNonneg : ∀ slot : Fin size, 0 ≤ form slot slot := by
    intro slot
    have hvalue := hpsd (Pi.single slot (1 : ℝ))
    rw [Matrix.mulVec_single, single_dotProduct] at hvalue
    simpa using hvalue
  have hcross : ∀ left right : Fin size, form left right = form right left := by
    intro left right
    have hentry := congrFun (congrFun hsymmetric left) right
    rw [Matrix.transpose_apply] at hentry
    exact hentry.symm
  have hpointwise : ∀ rowSlot colSlot : Fin size,
      probe rowSlot * (form rowSlot colSlot * probe colSlot)
          + probe colSlot * (form colSlot rowSlot * probe rowSlot)
        ≤ form rowSlot rowSlot * probe colSlot ^ 2
          + form colSlot colSlot * probe rowSlot ^ 2 := by
    intro rowSlot colSlot
    have hsq := entry_sq_le_diag_mul_diag hsymmetric hpsd rowSlot colSlot
    have habsorb := two_cross_le_diag_pair (cross := form rowSlot colSlot)
      (diagOne := form rowSlot rowSlot) (diagTwo := form colSlot colSlot)
      (valueOne := probe rowSlot) (valueTwo := probe colSlot) (hdiagNonneg rowSlot)
      (hdiagNonneg colSlot) hsq
    rw [hcross colSlot rowSlot]
    nlinarith [habsorb]
  have hexpandLeft : probe ⬝ᵥ (form *ᵥ probe)
      = ∑ rowSlot, ∑ colSlot, probe rowSlot * (form rowSlot colSlot * probe colSlot) := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun rowSlot _ => by
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  have hexpandRight : Matrix.trace form * (probe ⬝ᵥ probe)
      = ∑ rowSlot, ∑ colSlot, form rowSlot rowSlot * probe colSlot ^ 2 := by
    rw [Matrix.trace, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun rowSlot _ => ?_
    rw [Matrix.diag, Finset.mul_sum]
    exact Finset.sum_congr rfl fun colSlot _ => by rw [pow_two]
  have hswapLeft : (∑ rowSlot, ∑ colSlot,
        probe colSlot * (form colSlot rowSlot * probe rowSlot))
      = ∑ rowSlot, ∑ colSlot, probe rowSlot * (form rowSlot colSlot * probe colSlot) :=
    Finset.sum_comm
  have hswapRight : (∑ rowSlot, ∑ colSlot, form colSlot colSlot * probe rowSlot ^ 2)
      = ∑ rowSlot, ∑ colSlot, form rowSlot rowSlot * probe colSlot ^ 2 :=
    Finset.sum_comm
  have hsumBound : (∑ rowSlot, ∑ colSlot,
        (probe rowSlot * (form rowSlot colSlot * probe colSlot)
          + probe colSlot * (form colSlot rowSlot * probe rowSlot)))
      ≤ ∑ rowSlot, ∑ colSlot,
        (form rowSlot rowSlot * probe colSlot ^ 2
          + form colSlot colSlot * probe rowSlot ^ 2) :=
    Finset.sum_le_sum fun rowSlot _ =>
      Finset.sum_le_sum fun colSlot _ => hpointwise rowSlot colSlot
  have hsplitLeft : (∑ rowSlot, ∑ colSlot,
        (probe rowSlot * (form rowSlot colSlot * probe colSlot)
          + probe colSlot * (form colSlot rowSlot * probe rowSlot)))
      = (∑ rowSlot, ∑ colSlot, probe rowSlot * (form rowSlot colSlot * probe colSlot))
        + ∑ rowSlot, ∑ colSlot, probe colSlot * (form colSlot rowSlot * probe rowSlot) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun rowSlot _ => by rw [← Finset.sum_add_distrib]
  have hsplitRight : (∑ rowSlot, ∑ colSlot,
        (form rowSlot rowSlot * probe colSlot ^ 2
          + form colSlot colSlot * probe rowSlot ^ 2))
      = (∑ rowSlot, ∑ colSlot, form rowSlot rowSlot * probe colSlot ^ 2)
        + ∑ rowSlot, ∑ colSlot, form colSlot colSlot * probe rowSlot ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun rowSlot _ => by rw [← Finset.sum_add_distrib]
  rw [hsplitLeft, hsplitRight, hswapLeft, hswapRight] at hsumBound
  rw [hexpandLeft, hexpandRight]
  linarith [hsumBound]

end TraceCeiling

/-! ## Layer 2 — the rank-two price bound -/

section PriceBound

/-- **THE RANK-TWO PRICE BOUND.**  A positive semidefinite price that the
projection absorbs and that kills a unit fixed vector never exceeds its
own trace against the chart energy less the squared fixed reading.  This
is the whole supply of the rank-two structure: the price is blind in the
fixed direction, and a positive semidefinite form never exceeds its own
trace. -/
theorem price_quadratic_le_trace_mul_shift {size : ℕ}
    {proj price : Matrix (Fin size) (Fin size) ℝ} {unitFixed : Fin size → ℝ}
    (hprojSym : projᵀ = proj) (hprojIdem : proj * proj = proj)
    (hpriceSym : priceᵀ = price)
    (hpricePsd : ∀ vec : Fin size → ℝ, 0 ≤ vec ⬝ᵥ (price *ᵥ vec))
    (habsorb : proj * price = price) (hunit : unitFixed ⬝ᵥ unitFixed = 1)
    (hfix : proj *ᵥ unitFixed = unitFixed) (hkill : price *ᵥ unitFixed = 0)
    (probe : Fin size → ℝ) :
    probe ⬝ᵥ (price *ᵥ probe)
      ≤ Matrix.trace price
        * (probe ⬝ᵥ (proj *ᵥ probe) - (unitFixed ⬝ᵥ probe) ^ 2) := by
  classical
  have hright : price * proj = price := by
    have htrans : (proj * price)ᵀ = priceᵀ := by rw [habsorb]
    rw [Matrix.transpose_mul, hprojSym, hpriceSym] at htrans
    exact htrans
  set shift := proj *ᵥ probe - (unitFixed ⬝ᵥ probe) • unitFixed with hshiftDef
  have hpriceShift : price *ᵥ shift = price *ᵥ probe := by
    rw [hshiftDef, Matrix.mulVec_sub, Matrix.mulVec_smul, hkill, smul_zero, sub_zero,
      Matrix.mulVec_mulVec, hright]
  have hunitPrice : unitFixed ⬝ᵥ (price *ᵥ probe) = 0 := by
    have hadjoint := dotProduct_mulVec_transpose price unitFixed probe
    rw [hpriceSym, hkill] at hadjoint
    rw [← hadjoint, zero_dotProduct]
  have hprojPrice : (proj *ᵥ probe) ⬝ᵥ (price *ᵥ probe) = probe ⬝ᵥ (price *ᵥ probe) := by
    have hadjoint := dotProduct_mulVec_transpose proj probe (price *ᵥ probe)
    rw [hprojSym] at hadjoint
    rw [hadjoint, Matrix.mulVec_mulVec, habsorb]
  have hshiftEnergy : shift ⬝ᵥ (price *ᵥ shift) = probe ⬝ᵥ (price *ᵥ probe) := by
    rw [hpriceShift, hshiftDef, sub_dotProduct, smul_dotProduct, hunitPrice, hprojPrice]
    ring
  have hunitProj : unitFixed ⬝ᵥ (proj *ᵥ probe) = unitFixed ⬝ᵥ probe := by
    have hadjoint := dotProduct_mulVec_transpose proj unitFixed probe
    rw [hprojSym, hfix] at hadjoint
    exact hadjoint.symm
  have hprojEnergy : (proj *ᵥ probe) ⬝ᵥ (proj *ᵥ probe) = probe ⬝ᵥ (proj *ᵥ probe) := by
    have hadjoint := dotProduct_mulVec_transpose proj probe (proj *ᵥ probe)
    rw [hprojSym] at hadjoint
    rw [hadjoint, Matrix.mulVec_mulVec, hprojIdem]
  have hshiftNorm : shift ⬝ᵥ shift
      = probe ⬝ᵥ (proj *ᵥ probe) - (unitFixed ⬝ᵥ probe) ^ 2 := by
    have hsymDot : (proj *ᵥ probe) ⬝ᵥ unitFixed = unitFixed ⬝ᵥ probe := by
      rw [dotProduct_comm, hunitProj]
    rw [hshiftDef]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hprojEnergy, hunitProj, hsymDot, hunit]
    ring
  have hceiling := quadratic_le_trace_mul_energy hpriceSym hpricePsd shift
  rw [hshiftEnergy, hshiftNorm] at hceiling
  exact hceiling

end PriceBound

/-! ## Layer 3 — the residue in atom form -/

section AtomForm

/-- **THE WIDE RESIDUE IN ATOM FORM.**  Six Parseval atoms of three-space,
six positive scales of mass exactly one, one free unit direction, and the
rank-two law that each scale plus its squared free reading never exceeds
the atom diagonal.  The conclusion is a card-three carrier that dominates
weakly.

The mass is exactly one and not less: the price total on the right of the
matrix conclusion normalizes it.  Thus this residue sits at the BOUNDARY
of the atom triple ceiling.  Its extra supply against the free-scale
ceiling is the free direction, whose squared readings also sum to one. -/
def WideAtomSelectionClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) (free : Fin 3 → ℝ),
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    free ⬝ᵥ free = 1 →
    (∀ slot, scale slot + (atom slot ⬝ᵥ free) ^ 2 ≤ atomGram atom slot slot) →
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe

/-- **THE NORMAL FORM REDUCTION.**  The matrix residue follows from the
atom residue.  The frame of the projection supplies the atoms, the price
diagonal over the price total supplies the scales, the frame reading of
the normalized fixed vector supplies the free direction, and the rank-two
price bound supplies the law of the free direction. -/
theorem wideSpectralSelectionClosed_of_wideAtomSelection
    (hatom : WideAtomSelectionClosed) : WideSpectralSelectionClosed := by
  classical
  intro proj price fixedVec hprojSym hprojIdem hprojTrace hpriceSym hpricePsd habsorb
    hdiagPos hfixNe hfix hkill
  obtain ⟨frame, hortho, hframe⟩ :=
    exists_orthonormalFrame_of_symmetric_idempotent (rank := 3) proj hprojSym hprojIdem
      (by rw [hprojTrace]; norm_num)
  set atom := wideFrameAtom frame with hatomDef
  have hframeLaw : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction :=
    wideFrameAtom_frameLaw hortho
  have hgram : ∀ rowSlot colSlot : Fin 6,
      atomGram atom rowSlot colSlot = proj rowSlot colSlot :=
    wideFrameAtom_gram hframe
  have hblend : ∀ probe : Fin 6 → ℝ,
      atomBlend atom probe ⬝ᵥ atomBlend atom probe = probe ⬝ᵥ (proj *ᵥ probe) :=
    wideFrameAtom_blend_energy hframe
  -- the price total is positive
  set total := ∑ atomIndex, 6 * price atomIndex atomIndex with htotalDef
  have htotalPos : 0 < total := by
    rw [htotalDef]
    refine Finset.sum_pos (fun atomIndex _ => by nlinarith [hdiagPos atomIndex]) ?_
    exact ⟨0, Finset.mem_univ 0⟩
  set scale := fun atomIndex : Fin 6 => (6 * price atomIndex atomIndex) / total with hscaleDef
  have hscalePos : ∀ slot, 0 < scale slot := fun slot => by
    rw [hscaleDef]
    exact div_pos (by nlinarith [hdiagPos slot]) htotalPos
  have hscaleMass : (∑ slot, scale slot) = 1 := by
    rw [hscaleDef, ← Finset.sum_div, ← htotalDef, div_self (ne_of_gt htotalPos)]
  -- the normalized fixed vector
  have hfixEnergy : 0 < fixedVec ⬝ᵥ fixedVec := by
    rcases (dotProduct_self_nonneg fixedVec).eq_or_lt with hzero | hpos
    · exact absurd (dotProduct_self_eq_zero.mp hzero.symm) hfixNe
    · exact hpos
  set fixNorm := Real.sqrt (fixedVec ⬝ᵥ fixedVec) with hfixNormDef
  have hfixNormPos : 0 < fixNorm := Real.sqrt_pos.mpr hfixEnergy
  have hfixNormNe : fixNorm ≠ 0 := ne_of_gt hfixNormPos
  set unitFixed := fixNorm⁻¹ • fixedVec with hunitDef
  have hunitEnergy : unitFixed ⬝ᵥ unitFixed = 1 := by
    have hsquare : fixedVec ⬝ᵥ fixedVec = fixNorm * fixNorm := by
      rw [hfixNormDef, Real.mul_self_sqrt (le_of_lt hfixEnergy)]
    rw [hunitDef]
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hsquare]
    field_simp
  have hunitFix : proj *ᵥ unitFixed = unitFixed := by
    rw [hunitDef, Matrix.mulVec_smul, hfix]
  have hunitKill : price *ᵥ unitFixed = 0 := by
    rw [hunitDef, Matrix.mulVec_smul, hkill, smul_zero]
  -- the free direction of three-space
  set free := frameᵀ *ᵥ unitFixed with hfreeDef
  have hfreeRead : ∀ slot : Fin 6, atom slot ⬝ᵥ free = unitFixed slot := by
    intro slot
    have hstep : atom slot ⬝ᵥ free = (frame *ᵥ free) slot := rfl
    rw [hstep, hfreeDef, Matrix.mulVec_mulVec, hframe, hunitFix]
  have hfreeUnit : free ⬝ᵥ free = 1 := by
    have hstep : free ⬝ᵥ free = ∑ slot, (atom slot ⬝ᵥ free) * (atom slot ⬝ᵥ free) := by
      rw [hframeLaw free free]
    rw [hstep]
    rw [Finset.sum_congr rfl fun slot _ => by rw [hfreeRead slot]]
    rw [← dotProduct]
    exact hunitEnergy
  -- the rank-two law
  have hrankTwo : ∀ slot, scale slot + (atom slot ⬝ᵥ free) ^ 2
      ≤ atomGram atom slot slot := by
    intro slot
    have hbound := price_quadratic_le_trace_mul_shift hprojSym hprojIdem hpriceSym
      hpricePsd habsorb hunitEnergy hunitFix hunitKill (Pi.single slot (1 : ℝ))
    rw [oneHot_quadratic, oneHot_quadratic, dotProduct_single, mul_one] at hbound
    have htraceSum : Matrix.trace price = ∑ atomIndex, price atomIndex atomIndex := rfl
    have htrace : total = 6 * Matrix.trace price := by
      rw [htotalDef, htraceSum, ← Finset.mul_sum]
    have hscaleVal : scale slot = 6 * price slot slot / total := by rw [hscaleDef]
    have hmain : 6 * price slot slot ≤ (proj slot slot - unitFixed slot ^ 2) * total := by
      rw [htrace]; nlinarith [hbound]
    rw [hgram slot slot, hfreeRead slot, hscaleVal, div_add' _ _ _ (ne_of_gt htotalPos),
      div_le_iff₀ htotalPos]
    nlinarith [hmain]
  obtain ⟨car, hcard, hdom⟩ := hatom atom scale free hframeLaw hscalePos hscaleMass
    hfreeUnit hrankTwo
  refine ⟨car, hcard, fun probe hsupport => ?_⟩
  have hstep := hdom probe hsupport
  rw [hblend probe] at hstep
  have hscaled : (∑ atomIndex, (6 * price atomIndex atomIndex) * probe atomIndex ^ 2)
      = total * ∑ slot, scale slot * probe slot ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun slot _ => ?_
    rw [hscaleDef]
    field_simp
  rw [hscaled]
  exact mul_le_mul_of_nonneg_left hstep (le_of_lt htotalPos)

end AtomForm

/-! ## Layer 4 — the boundary of the atom triple ceiling -/

section Boundary

/-- **THE SCALED STRICT FORM GIVES THE WEAK FORM.**  A one-parameter
family of strict carriers collapses to one weak carrier, because there
are finitely many carriers: the largest failure ratio over the finitely
many carriers is below one, and any factor above it refutes the strict
statement at its own carrier. -/
theorem exists_weakCarrier_of_scaled_strict {cardTarget : ℕ}
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hstep : ∀ factor : ℝ, 0 < factor → factor < 1 →
      ∃ car : Finset (Fin 6), car.card = cardTarget
        ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
            (∑ slot, (factor * scale slot) * probe slot ^ 2)
              < atomBlend atom probe ⬝ᵥ atomBlend atom probe) :
    ∃ car : Finset (Fin 6), car.card = cardTarget
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  by_contra hcontra
  push Not at hcontra
  have hchoice : ∀ car : Finset (Fin 6), ∃ probe : Fin 6 → ℝ,
      car.card = cardTarget →
        ((∀ slot ∉ car, probe slot = 0)
          ∧ atomBlend atom probe ⬝ᵥ atomBlend atom probe
            < ∑ slot, scale slot * probe slot ^ 2) := by
    intro car
    by_cases hcard : car.card = cardTarget
    · obtain ⟨probe, hsupport, hlt⟩ := hcontra car hcard
      exact ⟨probe, fun _ => ⟨hsupport, hlt⟩⟩
    · exact ⟨0, fun hcardEq => absurd hcardEq hcard⟩
  choose witness hwitness using hchoice
  set cars := (Finset.univ : Finset (Finset (Fin 6))).filter
    fun car => car.card = cardTarget with hcarsDef
  have hmemCars : ∀ car : Finset (Fin 6), car ∈ cars ↔ car.card = cardTarget := by
    intro car
    rw [hcarsDef, Finset.mem_filter]
    exact ⟨fun hboth => hboth.2, fun hcard => ⟨Finset.mem_univ _, hcard⟩⟩
  obtain ⟨seedCar, hseedCard, _⟩ := hstep (1 / 2) (by norm_num) (by norm_num)
  have hcarsNe : cars.Nonempty := ⟨seedCar, (hmemCars seedCar).mpr hseedCard⟩
  set ratio := fun car : Finset (Fin 6) =>
    (atomBlend atom (witness car) ⬝ᵥ atomBlend atom (witness car))
      / ∑ slot, scale slot * witness car slot ^ 2 with hratioDef
  have hmassPos : ∀ car ∈ cars, 0 < ∑ slot, scale slot * witness car slot ^ 2 := by
    intro car hmem
    have hcard : car.card = cardTarget := (hmemCars car).mp hmem
    have hlt := (hwitness car hcard).2
    have hnonneg : 0 ≤ atomBlend atom (witness car) ⬝ᵥ atomBlend atom (witness car) :=
      dotProduct_self_nonneg _
    linarith [hlt, hnonneg]
  have hratioLt : ∀ car ∈ cars, ratio car < 1 := by
    intro car hmem
    have hcard : car.card = cardTarget := (hmemCars car).mp hmem
    rw [hratioDef]
    exact (div_lt_one (hmassPos car hmem)).mpr (hwitness car hcard).2
  have hratioNonneg : ∀ car ∈ cars, 0 ≤ ratio car := by
    intro car hmem
    rw [hratioDef]
    exact div_nonneg (dotProduct_self_nonneg _) (le_of_lt (hmassPos car hmem))
  set top := cars.sup' hcarsNe ratio with htopDef
  have htopLt : top < 1 := by
    rw [htopDef, Finset.sup'_lt_iff]
    exact hratioLt
  have htopNonneg : 0 ≤ top := by
    obtain ⟨car, hmem⟩ := hcarsNe
    exact le_trans (hratioNonneg car hmem) (by rw [htopDef]; exact Finset.le_sup' ratio hmem)
  set factor := (top + 1) / 2 with hfactorDef
  have hfactorPos : 0 < factor := by rw [hfactorDef]; linarith
  have hfactorLt : factor < 1 := by rw [hfactorDef]; linarith
  have hfactorTop : top < factor := by rw [hfactorDef]; linarith
  obtain ⟨car, hcard, hstrict⟩ := hstep factor hfactorPos hfactorLt
  have hmem : car ∈ cars := (hmemCars car).mpr hcard
  obtain ⟨hsupport, hlt⟩ := hwitness car hcard
  have hprobeNe : witness car ≠ 0 := by
    intro hzero
    rw [hzero] at hlt
    simp only [Pi.zero_apply] at hlt
    rw [show atomBlend atom (0 : Fin 6 → ℝ) = 0 by
      funext index; simp [atomBlend]] at hlt
    simp at hlt
  have hstrictWitness := hstrict (witness car) hsupport hprobeNe
  have hpull : (∑ slot, (factor * scale slot) * witness car slot ^ 2)
      = factor * ∑ slot, scale slot * witness car slot ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun slot _ => by ring
  rw [hpull] at hstrictWitness
  have hratioEq : atomBlend atom (witness car) ⬝ᵥ atomBlend atom (witness car)
      = ratio car * ∑ slot, scale slot * witness car slot ^ 2 := by
    rw [hratioDef, div_mul_cancel₀ _ (ne_of_gt (hmassPos car hmem))]
  rw [hratioEq] at hstrictWitness
  have hratioLeTop : ratio car ≤ top := by
    rw [htopDef]; exact Finset.le_sup' ratio hmem
  nlinarith [hstrictWitness, hmassPos car hmem, hratioLeTop, hfactorTop]

/-- **THE BOUNDARY FORM OF THE ATOM TRIPLE CEILING.**  The scale mass is
exactly one, and the dominating triple dominates WEAKLY. -/
def AtomTripleBoundaryClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe

/-- The ceiling gives the boundary: scale the mass below one and collapse
the family of strict carriers. -/
theorem atomTripleBoundaryClosed_of_atomTripleCeiling
    (hceiling : AtomTripleCeilingClosed) : AtomTripleBoundaryClosed := by
  intro atom scale hpos hmass hframe
  refine exists_weakCarrier_of_scaled_strict fun factor hfactorPos hfactorLt => ?_
  refine hceiling atom (fun slot => factor * scale slot)
    (fun slot => mul_pos hfactorPos (hpos slot)) ?_ hframe
  rw [← Finset.mul_sum, hmass, mul_one]
  exact hfactorLt

/-- The boundary gives the ceiling: normalize the scale mass to one and
read the strictness off the mass deficit. -/
theorem atomTripleCeilingClosed_of_atomTripleBoundary
    (hboundary : AtomTripleBoundaryClosed) : AtomTripleCeilingClosed := by
  intro atom scale hpos hsmall hframe
  have hmassPos : 0 < ∑ slot, scale slot :=
    Finset.sum_pos (fun slot _ => hpos slot) ⟨0, Finset.mem_univ 0⟩
  obtain ⟨car, hcard, hdom⟩ := hboundary atom (fun slot => scale slot / ∑ z, scale z)
    (fun slot => div_pos (hpos slot) hmassPos)
    (by rw [← Finset.sum_div, div_self (ne_of_gt hmassPos)]) hframe
  refine ⟨car, hcard, fun probe hsupport hprobeNe => ?_⟩
  have hstep := hdom probe hsupport
  have hnormalized : (∑ slot, scale slot / (∑ z, scale z) * probe slot ^ 2)
      = (∑ slot, scale slot * probe slot ^ 2) / ∑ z, scale z := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun slot _ => by ring
  rw [hnormalized, div_le_iff₀ hmassPos] at hstep
  obtain ⟨liveSlot, hlive⟩ := Function.ne_iff.mp hprobeNe
  have hliveNe : probe liveSlot ≠ 0 := by simpa using hlive
  have hscaleEnergyPos : 0 < ∑ slot, scale slot * probe slot ^ 2 :=
    Finset.sum_pos'
      (fun slot _ => mul_nonneg (hpos slot).le (sq_nonneg _))
      ⟨liveSlot, Finset.mem_univ liveSlot,
        mul_pos (hpos liveSlot) ((sq_nonneg (probe liveSlot)).lt_of_ne
          (Ne.symm (pow_ne_zero 2 hliveNe)))⟩
  nlinarith [hstep, hscaleEnergyPos, hsmall, hmassPos]

/-- **THE BOUNDARY IS THE CEILING.**  The two residues are equivalent. -/
theorem atomTripleCeilingClosed_iff_boundary :
    AtomTripleCeilingClosed ↔ AtomTripleBoundaryClosed :=
  ⟨atomTripleBoundaryClosed_of_atomTripleCeiling, atomTripleCeilingClosed_of_atomTripleBoundary⟩

/-- The wide atom residue is below the boundary residue: it carries the
free direction and the rank-two law as EXTRA hypotheses, thus its
hypothesis class is smaller. -/
theorem wideAtomSelectionClosed_of_atomTripleBoundary
    (hboundary : AtomTripleBoundaryClosed) : WideAtomSelectionClosed := by
  intro atom scale free hframe hpos hmass _hunit _hrankTwo
  exact hboundary atom scale hpos hmass hframe

/-- **THE WIDE RESIDUE IS BELOW THE ATOM TRIPLE CEILING.** -/
theorem wideSpectralSelectionClosed_of_atomTripleCeiling
    (hceiling : AtomTripleCeilingClosed) : WideSpectralSelectionClosed :=
  wideSpectralSelectionClosed_of_wideAtomSelection
    (wideAtomSelectionClosed_of_atomTripleBoundary
      (atomTripleBoundaryClosed_of_atomTripleCeiling hceiling))

end Boundary

/-! ## Layer 5 — the discharged spine from the atom triple ceiling -/

section Spine

/-- The wide capture line residue from the atom triple ceiling. -/
theorem rankFourCaptureLineWideFlooredClosed_of_atomTripleCeiling
    (hceiling : AtomTripleCeilingClosed) : RankFourCaptureLineWideFlooredClosed :=
  rankFourCaptureLineWideFlooredClosed_of_wideSpectralSelection
    (wideSpectralSelectionClosed_of_atomTripleCeiling hceiling)

/-- The unfloored rank-four residue from the atom triple ceiling. -/
theorem rankFourChartNullBasisNullClosed_of_atomTripleCeiling
    (hceiling : AtomTripleCeilingClosed) : RankFourChartNullBasisNullClosed :=
  rankFourChartNullBasisNullClosed_of_wideSpectralSelection
    (wideSpectralSelectionClosed_of_atomTripleCeiling hceiling)

/-- The floored rank-four residue from the atom triple ceiling. -/
theorem rankFourChartNullBasisNullFlooredClosed_of_atomTripleCeiling
    (hceiling : AtomTripleCeilingClosed) : RankFourChartNullBasisNullFlooredClosed :=
  rankFourChartNullBasisNullFlooredClosed_of_wideSpectralSelection
    (wideSpectralSelectionClosed_of_atomTripleCeiling hceiling)

/-- The unfloored rank-four rung from the atom triple ceiling, with NO
interiority hypothesis. -/
theorem isSixThreeAssemblyRankExcluded_four_of_atomTripleCeiling
    (hceiling : AtomTripleCeilingClosed) : IsSixThreeAssemblyRankExcluded 4 :=
  isSixThreeAssemblyRankExcluded_four_of_wideSpectralSelection
    (wideSpectralSelectionClosed_of_atomTripleCeiling hceiling)

/-- The floored rank-four rung from the atom triple ceiling. -/
theorem isSixThreeAssemblyRankExcludedFloored_four_of_atomTripleCeiling
    (hceiling : AtomTripleCeilingClosed) : IsSixThreeAssemblyRankExcludedFloored 4 :=
  isSixThreeAssemblyRankExcludedFloored_four_of_wideSpectralSelection
    (wideSpectralSelectionClosed_of_atomTripleCeiling hceiling)

/-- **THE CELL FROM THE ATOM TRIPLE CEILING AND THE SIX UPPER
CLOSURES**, through the wide spectral route. -/
theorem gtzWeighted_six_three_of_atomTripleCeiling_of_upperClosures
    (hceiling : AtomTripleCeilingClosed)
    (hfiveOne : RankFiveSupportTwoClosed)
    (hfiveTwo : RankFiveSharedPrivateClosed)
    (hfiveDense : RankFiveDenseClosed)
    (hsixOne : RankSixSupportTwoClosed)
    (hsixTwo : RankSixSharedPrivateClosed)
    (hsixDense : RankSixDenseClosed) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_wideSpectralSelection_of_upperClosures
    (wideSpectralSelectionClosed_of_atomTripleCeiling hceiling)
    hfiveOne hfiveTwo hfiveDense hsixOne hsixTwo hsixDense

end Spine

/-! ## Layer 6 — the boundary pair is unconditional -/

section BoundaryPair

/-- The SHADOW of an atom family in the plane orthogonal to a unit axis. -/
def wideShadow (atom : Fin 6 → (Fin 3 → ℝ)) (axis : Fin 3 → ℝ) : Fin 6 → (Fin 3 → ℝ) :=
  fun slot => atom slot - (atom slot ⬝ᵥ axis) • axis

theorem wideShadow_dot_axis {atom : Fin 6 → (Fin 3 → ℝ)} {axis : Fin 3 → ℝ}
    (haxis : axis ⬝ᵥ axis = 1) (slot : Fin 6) :
    wideShadow atom axis slot ⬝ᵥ axis = 0 := by
  rw [wideShadow, sub_dotProduct, smul_dotProduct, smul_eq_mul, haxis, mul_one, sub_self]

/-- In the plane the shadow reads exactly as the atom. -/
theorem wideShadow_dot_plane {atom : Fin 6 → (Fin 3 → ℝ)} {axis probe : Fin 3 → ℝ}
    (hplane : probe ⬝ᵥ axis = 0) (slot : Fin 6) :
    wideShadow atom axis slot ⬝ᵥ probe = atom slot ⬝ᵥ probe := by
  have haxisProbe : axis ⬝ᵥ probe = 0 := by rw [dotProduct_comm]; exact hplane
  rw [wideShadow, sub_dotProduct, smul_dotProduct, smul_eq_mul, haxisProbe, mul_zero, sub_zero]

/-- The shadow of a Parseval frame is a Parseval frame of the plane. -/
theorem wideShadow_frameLaw {atom : Fin 6 → (Fin 3 → ℝ)} {axis : Fin 3 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (probe direction : Fin 3 → ℝ) (hprobe : probe ⬝ᵥ axis = 0)
    (hdirection : direction ⬝ᵥ axis = 0) :
    (∑ slot, (wideShadow atom axis slot ⬝ᵥ probe)
        * (wideShadow atom axis slot ⬝ᵥ direction))
      = probe ⬝ᵥ direction := by
  rw [Finset.sum_congr rfl fun slot _ => by
    rw [wideShadow_dot_plane hprobe slot, wideShadow_dot_plane hdirection slot]]
  exact hframe probe direction

/-- The shadow blend never carries more energy than the atom blend: the
axis component is exactly what the shadow drops. -/
theorem wideShadow_blend_le {atom : Fin 6 → (Fin 3 → ℝ)} {axis : Fin 3 → ℝ}
    (haxis : axis ⬝ᵥ axis = 1) (probe : Fin 6 → ℝ) :
    atomBlend (wideShadow atom axis) probe ⬝ᵥ atomBlend (wideShadow atom axis) probe
      ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  set drop := ∑ slot, probe slot * (atom slot ⬝ᵥ axis) with hdropDef
  have hsplit : atomBlend (wideShadow atom axis) probe
      = atomBlend atom probe - drop • axis := by
    funext index
    rw [atomBlend_apply, Pi.sub_apply, atomBlend_apply, Pi.smul_apply, smul_eq_mul,
      hdropDef, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun slot _ => by
      rw [wideShadow, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have haxisBlend : atomBlend atom probe ⬝ᵥ axis = drop := by
    rw [atomBlend_dot, hdropDef]
  have hcomm : axis ⬝ᵥ atomBlend atom probe = drop := by
    rw [dotProduct_comm]; exact haxisBlend
  rw [hsplit]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [haxisBlend, hcomm, haxis]
  nlinarith [sq_nonneg drop]

/-- **THE BOUNDARY PAIR IS UNCONDITIONAL.**  At scale mass exactly one a
Parseval frame of three-space always carries a dominating PAIR.  The
proof shadows the atoms into a plane, where the landed plane pair ceiling
supplies a strictly dominating pair at every mass below one, and the
finite carrier collapse turns that family into one weak pair.  The axis
component of the blend is dropped by the shadow, thus the plane
conclusion lifts to the ambient one. -/
theorem exists_dominating_pair_of_boundary {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) (hmass : (∑ slot, scale slot) = 1) :
    ∃ car : Finset (Fin 6), car.card = 2
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  set axis : Fin 3 → ℝ := Pi.single 0 1 with haxisDef
  have haxisUnit : axis ⬝ᵥ axis = 1 := by
    rw [haxisDef, single_dotProduct, Pi.single_eq_same, mul_one]
  have haxisPos : (0 : ℝ) < axis ⬝ᵥ axis := by rw [haxisUnit]; norm_num
  refine exists_weakCarrier_of_scaled_strict fun factor hfactorPos hfactorLt => ?_
  obtain ⟨car, hcard, hdom⟩ := atomPairCeilingClosed_holds (wideShadow atom axis)
    (fun slot => factor * scale slot) axis haxisPos
    (wideShadow_dot_axis haxisUnit)
    (fun slot => mul_nonneg hfactorPos.le (hscale slot))
    (by rw [← Finset.mul_sum, hmass, mul_one]; exact hfactorLt)
    (fun probe direction hprobe hdirection =>
      wideShadow_frameLaw hframe probe direction hprobe hdirection)
  exact ⟨car, hcard, fun probe hsupport hprobeNe =>
    lt_of_lt_of_le (hdom probe hsupport hprobeNe) (wideShadow_blend_le haxisUnit probe)⟩

end BoundaryPair

/-! ## Layer 7 — the free pivot -/

section FreePivot

/-- The squared free readings of a Parseval frame sum to the free energy. -/
theorem sum_free_read_sq {atom : Fin 6 → (Fin 3 → ℝ)} {free : Fin 3 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ slot, (atom slot ⬝ᵥ free) ^ 2) = free ⬝ᵥ free := by
  rw [Finset.sum_congr rfl fun slot _ => (pow_two (atom slot ⬝ᵥ free))]
  exact hframe free free

/-- **THE FREE PIVOT.**  The squared free readings sum to one and so do
the scales, thus some slot reads its own scale or more in the free
direction.  This is the pigeonhole that the rank-two structure supplies
and the free-scale ceiling does not have. -/
theorem exists_freePivot {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ} {free : Fin 3 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hmass : (∑ slot, scale slot) = 1) (hfree : free ⬝ᵥ free = 1) :
    ∃ pivot : Fin 6, scale pivot ≤ (atom pivot ⬝ᵥ free) ^ 2 := by
  classical
  by_contra hcontra
  push Not at hcontra
  have hstrict : (∑ slot, (atom slot ⬝ᵥ free) ^ 2) < ∑ slot, scale slot :=
    Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ fun slot _ => hcontra slot
  rw [sum_free_read_sq hframe, hfree, hmass] at hstrict
  exact lt_irrefl 1 hstrict

/-- **THE FREE PIVOT CARRIES ITS OWN SCALE IN THE SHIFTED DIAGONAL.**  At
a wide atom datum the free pivot has a shifted diagonal at least its own
scale, thus a strictly positive one. -/
theorem exists_freePivot_shiftedDiag {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    {free : Fin 3 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) = 1)
    (hfree : free ⬝ᵥ free = 1)
    (hrankTwo : ∀ slot, scale slot + (atom slot ⬝ᵥ free) ^ 2 ≤ atomGram atom slot slot) :
    ∃ pivot : Fin 6, scale pivot ≤ atomShiftedDiag atom scale pivot
      ∧ 0 < atomShiftedDiag atom scale pivot := by
  obtain ⟨pivot, hpivot⟩ := exists_freePivot hframe hmass hfree
  have hshift : scale pivot ≤ atomShiftedDiag atom scale pivot := by
    rw [atomShiftedDiag]
    linarith [hrankTwo pivot, hpivot]
  exact ⟨pivot, hshift, lt_of_lt_of_le (hpos pivot) hshift⟩

end FreePivot

/-! ## Layer 8 — the sign gauge -/

section SignGauge

/-- The SIGN FLIP of an atom family. -/
def wideSignFlip (sign : Fin 6 → ℝ) (atom : Fin 6 → (Fin 3 → ℝ)) : Fin 6 → (Fin 3 → ℝ) :=
  fun slot => sign slot • atom slot

theorem wideSignFlip_gram (sign : Fin 6 → ℝ) (atom : Fin 6 → (Fin 3 → ℝ))
    (rowSlot colSlot : Fin 6) :
    atomGram (wideSignFlip sign atom) rowSlot colSlot
      = sign rowSlot * sign colSlot * atomGram atom rowSlot colSlot := by
  simp only [atomGram, wideSignFlip, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem wideSignFlip_gram_diag {sign : Fin 6 → ℝ} (hsign : ∀ slot, sign slot * sign slot = 1)
    (atom : Fin 6 → (Fin 3 → ℝ)) (slot : Fin 6) :
    atomGram (wideSignFlip sign atom) slot slot = atomGram atom slot slot := by
  rw [wideSignFlip_gram, hsign slot, one_mul]

/-- The frame law survives a sign flip. -/
theorem wideSignFlip_frameLaw {sign : Fin 6 → ℝ} (hsign : ∀ slot, sign slot * sign slot = 1)
    {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (probe direction : Fin 3 → ℝ) :
    (∑ slot, (wideSignFlip sign atom slot ⬝ᵥ probe)
        * (wideSignFlip sign atom slot ⬝ᵥ direction))
      = probe ⬝ᵥ direction := by
  rw [Finset.sum_congr rfl fun slot _ => by
    rw [wideSignFlip, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      show sign slot * (atom slot ⬝ᵥ probe) * (sign slot * (atom slot ⬝ᵥ direction))
        = sign slot * sign slot * ((atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) by ring,
      hsign slot, one_mul]]
  exact hframe probe direction

/-- The blend of a flipped family is the blend of the family against the
flipped probe. -/
theorem wideSignFlip_blend (sign : Fin 6 → ℝ) (atom : Fin 6 → (Fin 3 → ℝ))
    (probe : Fin 6 → ℝ) :
    atomBlend (wideSignFlip sign atom) probe
      = atomBlend atom (fun slot => sign slot * probe slot) := by
  funext index
  rw [atomBlend_apply, atomBlend_apply]
  exact Finset.sum_congr rfl fun slot _ => by
    rw [wideSignFlip, Pi.smul_apply, smul_eq_mul]; ring

/-- The scale energy of a probe survives a sign flip. -/
theorem wideSignFlip_scale_energy {sign : Fin 6 → ℝ}
    (hsign : ∀ slot, sign slot * sign slot = 1) (scale probe : Fin 6 → ℝ) :
    (∑ slot, scale slot * (sign slot * probe slot) ^ 2)
      = ∑ slot, scale slot * probe slot ^ 2 :=
  Finset.sum_congr rfl fun slot _ => by
    rw [mul_pow, show sign slot ^ 2 = sign slot * sign slot from (pow_two _), hsign slot,
      one_mul]

end SignGauge

/-! ## Layer 9 — the parity engine, the real-only ingredient -/

section Parity

/-- **FIVE VECTORS OF THREE-SPACE ARE NEVER PAIRWISE STRICTLY OBTUSE.**
Stated at six slots with one excluded: among the five slots away from any
chosen slot, some pair has a nonnegative dot product.

The proof is a dependency.  Three coordinate rows, two rows that force
two chosen coefficients to vanish, and one zero row make a square system
of vanishing determinant, thus a nonzero dependency exists that kills two
chosen coefficients.  Its absolute value is again a dependency, because
every cross term of the energy only decreases.  The row of the second
killed slot then forces every remaining coefficient to vanish, and the
dependency is zero — a contradiction.

Over the complex field the entry products are not real, the absolute
value of a coefficient is not a coefficient, and this argument has no
analogue.  It is the real-only ingredient of the wide residue. -/
theorem exists_nonneg_dot_off_pivot (vec : Fin 6 → (Fin 3 → ℝ)) (pivot : Fin 6) :
    ∃ slotOne slotTwo : Fin 6, slotOne ≠ pivot ∧ slotTwo ≠ pivot ∧ slotOne ≠ slotTwo
      ∧ 0 ≤ vec slotOne ⬝ᵥ vec slotTwo := by
  classical
  by_contra hcontra
  push Not at hcontra
  obtain ⟨witness, hwitnessNe⟩ : ∃ slot : Fin 6, slot ≠ pivot := by
    by_cases hzero : pivot = 0
    · exact ⟨1, by rw [hzero]; decide⟩
    · exact ⟨0, fun heq => hzero heq.symm⟩
  set sysMatrix : Matrix (Fin 6) (Fin 6) ℝ := Matrix.of fun row col =>
    ![vec col 0, vec col 1, vec col 2, (if col = pivot then (1 : ℝ) else 0),
      (if col = witness then (1 : ℝ) else 0), 0] row with hsysDef
  have hentryZero : ∀ col : Fin 6, sysMatrix 0 col = vec col 0 := by
    intro col; rw [hsysDef]; simp
  have hentryOne : ∀ col : Fin 6, sysMatrix 1 col = vec col 1 := by
    intro col; rw [hsysDef]; simp
  have hentryTwo : ∀ col : Fin 6, sysMatrix 2 col = vec col 2 := by
    intro col; rw [hsysDef]; simp
  have hentryThree : ∀ col : Fin 6,
      sysMatrix 3 col = (if col = pivot then (1 : ℝ) else 0) := by
    intro col; rw [hsysDef]; simp
  have hentryFour : ∀ col : Fin 6,
      sysMatrix 4 col = (if col = witness then (1 : ℝ) else 0) := by
    intro col; rw [hsysDef]; simp
  have hentryFive : ∀ col : Fin 6, sysMatrix 5 col = 0 := by
    intro col; rw [hsysDef]; simp
  have hdet : sysMatrix.det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero 5 hentryFive
  obtain ⟨coeff, hcoeffNe, hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hrowRead : ∀ row : Fin 6, (∑ col, sysMatrix row col * coeff col) = 0 := by
    intro row
    have hentry := congrFun hkernel row
    rw [Matrix.mulVec, dotProduct] at hentry
    simpa using hentry
  have hpivotZero : coeff pivot = 0 := by
    have hrow := hrowRead 3
    rw [Finset.sum_congr rfl fun col _ => by
      rw [hentryThree col, ite_mul, one_mul, zero_mul]] at hrow
    rw [Finset.sum_ite_eq' Finset.univ pivot coeff] at hrow
    simpa using hrow
  have hwitnessZero : coeff witness = 0 := by
    have hrow := hrowRead 4
    rw [Finset.sum_congr rfl fun col _ => by
      rw [hentryFour col, ite_mul, one_mul, zero_mul]] at hrow
    rw [Finset.sum_ite_eq' Finset.univ witness coeff] at hrow
    simpa using hrow
  have hblendZero : atomBlend vec coeff = 0 := by
    funext index
    rw [atomBlend_apply, Pi.zero_apply]
    have hcoord : ∀ row : Fin 6, (∀ col : Fin 6, sysMatrix row col = vec col index) →
        (∑ slot, coeff slot * vec slot index) = 0 := by
      intro row hmatch
      rw [← hrowRead row]
      exact Finset.sum_congr rfl fun col _ => by rw [hmatch col]; ring
    fin_cases index
    · exact hcoord 0 hentryZero
    · exact hcoord 1 hentryOne
    · exact hcoord 2 hentryTwo
  set mass : Fin 6 → ℝ := fun slot => |coeff slot| with hmassDef
  have hmassNonneg : ∀ slot, 0 ≤ mass slot := fun slot => abs_nonneg _
  have hmassPivot : mass pivot = 0 := by
    simp only [hmassDef]; rw [hpivotZero, abs_zero]
  have hmassWitness : mass witness = 0 := by
    simp only [hmassDef]; rw [hwitnessZero, abs_zero]
  have hterm : ∀ rowSlot colSlot : Fin 6,
      mass rowSlot * mass colSlot * atomGram vec rowSlot colSlot
        ≤ coeff rowSlot * coeff colSlot * atomGram vec rowSlot colSlot := by
    intro rowSlot colSlot
    rcases eq_or_ne rowSlot colSlot with heq | hne
    · subst heq
      simp only [hmassDef, abs_mul_abs_self]
      exact le_refl _
    · by_cases hrowPivot : rowSlot = pivot
      · rw [hrowPivot, hmassPivot, hpivotZero]; simp
      · by_cases hcolPivot : colSlot = pivot
        · rw [hcolPivot, hmassPivot, hpivotZero]; simp
        · have hneg : vec rowSlot ⬝ᵥ vec colSlot < 0 :=
            hcontra rowSlot colSlot hrowPivot hcolPivot hne
          have habs : coeff rowSlot * coeff colSlot ≤ mass rowSlot * mass colSlot := by
            simp only [hmassDef]
            rw [← abs_mul]
            exact le_abs_self _
          rw [atomGram]
          exact mul_le_mul_of_nonpos_right habs hneg.le
  have hmassEnergy : atomBlend vec mass ⬝ᵥ atomBlend vec mass ≤ 0 := by
    rw [atomBlend_energy_eq_gram]
    have hcoeffEnergy : (∑ rowSlot, ∑ colSlot,
        coeff rowSlot * coeff colSlot * atomGram vec rowSlot colSlot) = 0 := by
      rw [← atomBlend_energy_eq_gram, hblendZero]
      simp [dotProduct]
    rw [← hcoeffEnergy]
    exact Finset.sum_le_sum fun rowSlot _ =>
      Finset.sum_le_sum fun colSlot _ => hterm rowSlot colSlot
  have hmassBlend : atomBlend vec mass = 0 :=
    eq_zero_of_dotProduct_self_eq_zero
      (le_antisymm hmassEnergy (dotProduct_self_nonneg _))
  have hkill : (∑ slot, mass slot * (vec witness ⬝ᵥ vec slot)) = 0 := by
    have hstep : (∑ slot, mass slot * (vec slot ⬝ᵥ vec witness)) = 0 := by
      rw [← atomBlend_dot vec mass (vec witness), hmassBlend, zero_dotProduct]
    rw [← hstep]
    exact Finset.sum_congr rfl fun slot _ => by rw [dotProduct_comm]
  have hnonpos : ∀ slot ∈ (Finset.univ : Finset (Fin 6)),
      mass slot * (vec witness ⬝ᵥ vec slot) ≤ 0 := by
    intro slot _
    by_cases hslotPivot : slot = pivot
    · rw [hslotPivot, hmassPivot, zero_mul]
    · by_cases hslotWitness : slot = witness
      · rw [hslotWitness, hmassWitness, zero_mul]
      · have hneg : vec witness ⬝ᵥ vec slot < 0 :=
          hcontra witness slot hwitnessNe hslotPivot fun heq => hslotWitness heq.symm
        exact mul_nonpos_of_nonneg_of_nonpos (hmassNonneg slot) hneg.le
  have hzeroAll := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hkill
  have hmassZero : mass = 0 := by
    funext slot
    by_cases hslotPivot : slot = pivot
    · rw [hslotPivot]; exact hmassPivot
    · by_cases hslotWitness : slot = witness
      · rw [hslotWitness]; exact hmassWitness
      · have hneg : vec witness ⬝ᵥ vec slot < 0 :=
          hcontra witness slot hwitnessNe hslotPivot fun heq => hslotWitness heq.symm
        have hterm := hzeroAll slot (Finset.mem_univ slot)
        rcases mul_eq_zero.mp hterm with hleft | hright
        · exact hleft
        · exact absurd hright (ne_of_lt hneg)
  refine hcoeffNe (funext fun slot => ?_)
  have hslot := congrFun hmassZero slot
  simp only [hmassDef, Pi.zero_apply, abs_eq_zero] at hslot
  simpa using hslot

/-- **THE POSITIVE PARITY TRIPLE.**  Every atom family carries, at every
chosen pivot, a triple whose three Gram entries multiply nonnegatively.
The parity of a triple is invariant under sign flips, thus the flip that
makes the pivot row nonnegative reduces the claim to the obtuse bound. -/
theorem exists_positiveParity_triple (atom : Fin 6 → (Fin 3 → ℝ)) (pivot : Fin 6) :
    ∃ slotOne slotTwo : Fin 6, slotOne ≠ pivot ∧ slotTwo ≠ pivot ∧ slotOne ≠ slotTwo
      ∧ 0 ≤ atomGram atom pivot slotOne * atomGram atom pivot slotTwo
            * atomGram atom slotOne slotTwo := by
  classical
  set sign : Fin 6 → ℝ := fun slot => if 0 ≤ atomGram atom pivot slot then 1 else -1
    with hsignDef
  have hsignSq : ∀ slot, sign slot * sign slot = 1 := by
    intro slot
    rw [hsignDef]
    by_cases hnonneg : 0 ≤ atomGram atom pivot slot <;> simp [hnonneg]
  have hsignRow : ∀ slot, 0 ≤ sign slot * atomGram atom pivot slot := by
    intro slot
    rw [hsignDef]
    by_cases hnonneg : 0 ≤ atomGram atom pivot slot
    · simp [hnonneg]
    · simp only [hnonneg, if_false]
      push Not at hnonneg
      nlinarith [hnonneg]
  obtain ⟨slotOne, slotTwo, honeNe, htwoNe, hpairNe, hcross⟩ :=
    exists_nonneg_dot_off_pivot (wideSignFlip sign atom) pivot
  refine ⟨slotOne, slotTwo, honeNe, htwoNe, hpairNe, ?_⟩
  have hcrossGram : 0 ≤ sign slotOne * sign slotTwo * atomGram atom slotOne slotTwo := by
    rw [← wideSignFlip_gram sign atom slotOne slotTwo]
    exact hcross
  have hproduct := mul_nonneg (mul_nonneg (hsignRow slotOne) (hsignRow slotTwo)) hcrossGram
  have hexpand : sign slotOne * atomGram atom pivot slotOne
        * (sign slotTwo * atomGram atom pivot slotTwo)
        * (sign slotOne * sign slotTwo * atomGram atom slotOne slotTwo)
      = (sign slotOne * sign slotOne) * (sign slotTwo * sign slotTwo)
        * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo
          * atomGram atom slotOne slotTwo) := by ring
  rw [hexpand, hsignSq slotOne, hsignSq slotTwo, one_mul, one_mul] at hproduct
  exact hproduct

/-- **THE NONNEGATIVE CROSS TRIPLE.**  The positive parity triple, in its
gauged form: one sign flip makes all three Gram entries of the triple
nonnegative at once, and the flip preserves the frame law, the diagonal
and the domination test. -/
theorem exists_nonnegCross_triple (atom : Fin 6 → (Fin 3 → ℝ)) (pivot : Fin 6) :
    ∃ (sign : Fin 6 → ℝ) (slotOne slotTwo : Fin 6),
      (∀ slot, sign slot * sign slot = 1)
        ∧ slotOne ≠ pivot ∧ slotTwo ≠ pivot ∧ slotOne ≠ slotTwo
        ∧ 0 ≤ atomGram (wideSignFlip sign atom) pivot slotOne
        ∧ 0 ≤ atomGram (wideSignFlip sign atom) pivot slotTwo
        ∧ 0 ≤ atomGram (wideSignFlip sign atom) slotOne slotTwo := by
  classical
  set sign : Fin 6 → ℝ := fun slot => if 0 ≤ atomGram atom pivot slot then 1 else -1
    with hsignDef
  have hsignSq : ∀ slot, sign slot * sign slot = 1 := by
    intro slot
    rw [hsignDef]
    by_cases hnonneg : 0 ≤ atomGram atom pivot slot <;> simp [hnonneg]
  have hsignPivot : sign pivot = 1 := by
    rw [hsignDef]
    have hdiag : 0 ≤ atomGram atom pivot pivot := atomGram_diag_nonneg atom pivot
    simp [hdiag]
  have hsignRow : ∀ slot, 0 ≤ sign slot * atomGram atom pivot slot := by
    intro slot
    rw [hsignDef]
    by_cases hnonneg : 0 ≤ atomGram atom pivot slot
    · simp [hnonneg]
    · simp only [hnonneg, if_false]
      push Not at hnonneg
      nlinarith [hnonneg]
  obtain ⟨slotOne, slotTwo, honeNe, htwoNe, hpairNe, hcross⟩ :=
    exists_nonneg_dot_off_pivot (wideSignFlip sign atom) pivot
  refine ⟨sign, slotOne, slotTwo, hsignSq, honeNe, htwoNe, hpairNe, ?_, ?_, hcross⟩
  · rw [wideSignFlip_gram, hsignPivot, one_mul]
    exact hsignRow slotOne
  · rw [wideSignFlip_gram, hsignPivot, one_mul]
    exact hsignRow slotTwo

end Parity

/-! ## Layer 10 — the extension criterion at the boundary -/

section Extension

/-- **AT THE BOUNDARY THE EXTENSION MARGIN IS EXACTLY ZERO.**  The pair
extension total of a rank-three Parseval frame is the rank minus two
minus the scale mass, against the pair minor, minus the pair correction.
At scale mass one the first factor vanishes, thus a pair of negative
correction always extends to a dominating triple, with no estimate. -/
theorem exists_dominating_triple_of_pair_correction {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hmass : (∑ slot, scale slot) = 1) {slotOne slotTwo : Fin 6} (hne : slotOne ≠ slotTwo)
    (hdiag : 0 < atomShiftedDiag atom scale slotOne)
    (hminor : 0 < atomPairMinor atom scale slotOne slotTwo)
    (hcorrection : atomPairCorrection atom scale slotOne slotTwo < 0) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
          (∑ slot, scale slot * probe slot ^ 2)
            < atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  have hmargin : atomPairCorrection atom scale slotOne slotTwo
      < (((3 : ℕ) : ℝ) - 2 - ∑ slot, scale slot)
        * atomPairMinor atom scale slotOne slotTwo := by
    rw [hmass]
    norm_num
    exact hcorrection
  obtain ⟨slotThree, honeTwo, honeThree, htwoThree, hdiagOut, hminorOut, hdet⟩ :=
    exists_sylvester_chain_of_pair_margin hframe scale hne hdiag hminor hmargin
  exact ⟨{slotOne, slotTwo, slotThree}, card_triple_slots honeTwo honeThree htwoThree,
    fun probe hvanish hprobeNe =>
      dominates_of_triple_minors honeTwo honeThree htwoThree hdiagOut hminorOut hdet
        hvanish hprobeNe⟩

/-- The wide reading of the extension criterion: a pair of negative
correction closes the wide atom residue at that datum. -/
theorem exists_weakCarrier_of_pair_correction {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hmass : (∑ slot, scale slot) = 1) {slotOne slotTwo : Fin 6} (hne : slotOne ≠ slotTwo)
    (hdiag : 0 < atomShiftedDiag atom scale slotOne)
    (hminor : 0 < atomPairMinor atom scale slotOne slotTwo)
    (hcorrection : atomPairCorrection atom scale slotOne slotTwo < 0) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  obtain ⟨car, hcard, hdom⟩ := exists_dominating_triple_of_pair_correction hframe hmass hne
    hdiag hminor hcorrection
  refine ⟨car, hcard, fun probe hsupport => ?_⟩
  by_cases hprobeNe : probe = 0
  · rw [hprobeNe]
    simp only [Pi.zero_apply]
    rw [show atomBlend atom (0 : Fin 6 → ℝ) = 0 by funext index; simp [atomBlend]]
    simp [dotProduct]
  · exact (hdom probe hsupport hprobeNe).le

end Extension

end Gtz

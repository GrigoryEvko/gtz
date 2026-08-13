import Gtz.Wave.OuterTraceThreeInterior
import Gtz.Wave.SharedPrivateKernelResidue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The outer column-Gram fold — the commuting read Gram of the third rung

The conjugated frame of the block-degree dispatch reads the coefficient
matrix as a symmetric idempotent `S` whose block corners carry the six
hat rows at the shifted weights.  This module adds the layer that the
vertex reduction of the outer campaign named essential and that no
landed file carries: the COLUMN Gram of the basis directions commutes
with `S`.

The mechanism is one exchange chain.  The diagonal core exchange gives
`M D = D Mᵀ`, and the representation with a symmetric chart gives
`N M = Mᵀ N` for the column Gram `N = Bᵀ B`.  The two together make
`N M` symmetric, and the read Gram `Θ`, whose entries are the dot
products of the hat rows, is the diagonal conjugate of `N`.  Thus `S`
and `Θ` commute.

Three laws follow at once.  The cone identity of the stationary datum
prices every hat row at square norm one sixth, so the read Gram has
trace one.  The carried rows price the capture energy of each hat row
at the shifted weight, so the capture trace `tr (S Θ)` is
`(6 value + 1) / 6`, which is less than one sixth at a negative value.
And the commutation makes `S Θ S = S Θ`, which prices the column self
energy of the whole hat family slot by slot: at every slot the squared
capture column sums to the shifted-weight-weighted hat squares.  The
leak form of that identity prices the off-carrier leak mass of a slot
by the on-carrier hat mass at the parabola `d (1 - d)`.

The last section turns the rank-six profile kill into a closed lattice.
The block-carrier cards of a rank-six frame sum to eighteen, and the
pin set and the pair set of a frame are the card-one and card-two
carriers.  The landed profile kill fires at mass four, thus the whole
rank-six outer kill reduces to TWO named residues: the circuit residue
and the low-profile residue.  The support-two closure of the third rung
discharges through the landed bridge from those two.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.exists_commuting_read_frame` — **THE COMMUTING FRAME PACKAGE.**
* `Gtz.read_energy_eq` — the capture energy of a hat row.
* `Gtz.readGram_trace_eq_one` — the read Gram has trace one.
* `Gtz.capture_trace_eq` — **THE CAPTURE TRACE.**
* `Gtz.read_column_self_energy` — **THE COLUMN SELF-ENERGY LAW.**
* `Gtz.read_column_leak_identity` — the leak form of that law.
* `Gtz.RankSixFrame.exists_commuting_read_frame` — the rank-six frame
  package.
* `Gtz.RankSixFrame.capture_trace_lt_inv_size` — **THE RANK-SIX
  CAPTURE CEILING.**
* `Gtz.RankSixOuterLowProfileClosed` — the low-profile residue.
* `Gtz.rankSixOuterKilled_of_circuit_and_lowProfile` — **THE RANK-SIX
  KILL LATTICE.**
* `Gtz.rankSixSupportTwoClosed_of_circuit_and_lowProfile` — **THE
  RANK-SIX DISCHARGE.**

## Vacuity

The frame statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no
crux exists, thus no frame exists.  The matrix statements of layer two
are unconditional.
-/

namespace Gtz

open Matrix

variable {activeIndex : Type*} {basisCount : ℕ}
variable {projection : Matrix (Fin 6) (Fin 6) ℝ} {weight : Fin 6 → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin 6)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin 6 → ℝ)}

/-! ## Layer 1 — the commuting read-Gram package -/

/-- **THE COMMUTING FRAME PACKAGE.**  A diagonal kernel-free Gram core
conjugates the coefficient matrix into a symmetric idempotent with the
same trace, the hat rows read its block corners at the shifted weights,
each hat row has square norm one sixth, and the Gram of the hat rows
COMMUTES with the conjugate.  The commutation is the diagonal conjugate
of the column-Gram exchange `N M = Mᵀ N`. -/
theorem exists_commuting_read_frame
    (hdata : IsChartStationaryData 3 projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    (hmemActive : ∀ slot, basisLabel slot ∈ activeSet)
    {leftInv : Matrix (Fin basisCount) (Fin 6) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (hspan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    {coeff gram : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    (hidempotent : coeff * coeff = coeff)
    (hexchange : coeff * gram = gram * coeffᵀ)
    (hHform : tightBasisColumns tightDir basisLabel * gram
        * (tightBasisColumns tightDir basisLabel)ᵀ
      = chartMultiplierAssembly activeSet activeWeight tightDir)
    (hpsd : gram.PosSemidef)
    (hker : ∀ coeffVec : Fin basisCount → ℝ, gram *ᵥ coeffVec = 0 →
      coeffVec = 0)
    {gramDiag : Fin basisCount → ℝ}
    (hdiag : gram = Matrix.diagonal gramDiag) :
    ∃ (S readGram : Matrix (Fin basisCount) (Fin basisCount) ℝ)
      (readVecs : Fin 6 → Fin basisCount → ℝ),
      Sᵀ = S ∧ S * S = S ∧ Matrix.trace S = Matrix.trace coeff
      ∧ (∀ atomIndex : Fin 6,
          ∀ slot ∉ blockCarrier activeSubset basisLabel atomIndex,
          readVecs atomIndex slot = 0)
      ∧ (∀ atomIndex : Fin 6, readVecs atomIndex ≠ 0)
      ∧ (∀ atomIndex : Fin 6,
          ∀ slot ∈ blockCarrier activeSubset basisLabel atomIndex,
          (S *ᵥ readVecs atomIndex) slot
            = (value + weight atomIndex) * readVecs atomIndex slot)
      ∧ (∀ atomIndex : Fin 6,
          readVecs atomIndex ⬝ᵥ readVecs atomIndex = ((6 : ℕ) : ℝ)⁻¹)
      ∧ (∀ rowSlot colSlot, readGram rowSlot colSlot
          = ∑ atomIndex : Fin 6,
              readVecs atomIndex rowSlot * readVecs atomIndex colSlot)
      ∧ S * readGram = readGram * S := by
  classical
  -- the positive square roots of the diagonal core
  have hpsdD := hpsd
  have hkerD := hker
  rw [hdiag] at hpsdD hkerD
  have hg : ∀ slot, 0 < gramDiag slot := by
    intro slot
    have h := posSemidef_diagonal_pos_of_kernel_free hpsdD hkerD slot
    rwa [Matrix.diagonal_apply_eq] at h
  set sq : Fin basisCount → ℝ := fun slot => Real.sqrt (gramDiag slot)
    with hsqdef
  have hsq : ∀ slot, 0 < sq slot := fun slot => Real.sqrt_pos.mpr (hg slot)
  have hsqsq : ∀ slot, sq slot * sq slot = gramDiag slot :=
    fun slot => Real.mul_self_sqrt (hg slot).le
  -- the exchange entries under the diagonal core
  have hexchangeD := hexchange
  rw [hdiag] at hexchangeD
  have hx : ∀ rowSlot colSlot, coeff rowSlot colSlot * gramDiag colSlot
      = gramDiag rowSlot * coeff colSlot rowSlot := by
    intro rowSlot colSlot
    have h := congrFun (congrFun hexchangeD rowSlot) colSlot
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.transpose_apply] at h
  -- the conjugated coefficient matrix
  set S : Matrix (Fin basisCount) (Fin basisCount) ℝ :=
    Matrix.of fun rowSlot colSlot =>
      (sq rowSlot)⁻¹ * (coeff rowSlot colSlot * sq colSlot) with hSdef
  have hSapply : ∀ rowSlot colSlot, S rowSlot colSlot
      = (sq rowSlot)⁻¹ * (coeff rowSlot colSlot * sq colSlot) :=
    fun _ _ => rfl
  have hSsymm : Sᵀ = S := by
    ext rowSlot colSlot
    rw [Matrix.transpose_apply, hSapply, hSapply]
    refine mul_left_cancel₀
      (mul_ne_zero (hsq rowSlot).ne' (hsq colSlot).ne') ?_
    have hci : sq rowSlot * (sq rowSlot)⁻¹ = 1 :=
      mul_inv_cancel₀ (hsq rowSlot).ne'
    have hcj : sq colSlot * (sq colSlot)⁻¹ = 1 :=
      mul_inv_cancel₀ (hsq colSlot).ne'
    have hgi := hsqsq rowSlot
    have hgj := hsqsq colSlot
    have hxi := hx rowSlot colSlot
    linear_combination
      (coeff colSlot rowSlot * sq rowSlot * sq rowSlot) * hcj
      - (coeff rowSlot colSlot * sq colSlot * sq colSlot) * hci
      + coeff colSlot rowSlot * hgi
      - coeff rowSlot colSlot * hgj
      - hxi
  have hSidem : S * S = S := by
    ext rowSlot colSlot
    rw [Matrix.mul_apply]
    have hterm : ∀ midSlot, S rowSlot midSlot * S midSlot colSlot
        = (sq rowSlot)⁻¹
          * (coeff rowSlot midSlot * coeff midSlot colSlot)
          * sq colSlot := by
      intro midSlot
      rw [hSapply, hSapply]
      have hck : sq midSlot * (sq midSlot)⁻¹ = 1 :=
        mul_inv_cancel₀ (hsq midSlot).ne'
      linear_combination ((sq rowSlot)⁻¹ * coeff rowSlot midSlot
        * coeff midSlot colSlot * sq colSlot) * hck
    rw [Finset.sum_congr rfl fun midSlot _ => hterm midSlot,
      ← Finset.sum_mul, ← Finset.mul_sum]
    have hMM : ∑ midSlot, coeff rowSlot midSlot
        * coeff midSlot colSlot = coeff rowSlot colSlot := by
      have h := congrFun (congrFun hidempotent rowSlot) colSlot
      rwa [Matrix.mul_apply] at h
    rw [hMM, hSapply]
    ring
  have hStrace : Matrix.trace S = Matrix.trace coeff := by
    rw [Matrix.trace, Matrix.trace]
    refine Finset.sum_congr rfl fun slot _ => ?_
    have h : S slot slot = (sq slot)⁻¹ * (coeff slot slot * sq slot) :=
      rfl
    have hinv : (sq slot)⁻¹ * sq slot = 1 :=
      inv_mul_cancel₀ (hsq slot).ne'
    show S slot slot = coeff slot slot
    rw [h]
    linear_combination coeff slot slot * hinv
  -- the hat rows
  set readVecs : Fin 6 → Fin basisCount → ℝ := fun atomIndex slot =>
    sq slot * tightDir (basisLabel slot) atomIndex with hreadVecs
  have hsupp : ∀ atomIndex : Fin 6,
      ∀ slot ∉ blockCarrier activeSubset basisLabel atomIndex,
      readVecs atomIndex slot = 0 := by
    intro atomIndex slot hslot
    rw [blockCarrier_mem] at hslot
    show sq slot * tightDir (basisLabel slot) atomIndex = 0
    rw [hdata.tightDir_support (basisLabel slot) (hmemActive slot)
      atomIndex hslot, mul_zero]
  have hnz : ∀ atomIndex : Fin 6, readVecs atomIndex ≠ 0 := by
    intro atomIndex hzero
    obtain ⟨slot, hslot⟩ := exists_basisIndex_datumTightSupport hdata
      basisLabel hspan leftInv hleft atomIndex
    have hq := mem_datumTightSupport.mp hslot
    have hv : readVecs atomIndex slot = 0 := congrFun hzero slot
    exact mul_ne_zero (hsq slot).ne' hq hv
  have hread : ∀ atomIndex : Fin 6,
      ∀ slot ∈ blockCarrier activeSubset basisLabel atomIndex,
      (S *ᵥ readVecs atomIndex) slot
        = (value + weight atomIndex) * readVecs atomIndex slot := by
    intro atomIndex slot hslot
    have hmemSubset : atomIndex ∈ activeSubset (basisLabel slot) :=
      blockCarrier_mem.mp hslot
    have hcarried : ∑ colSlot, tightDir (basisLabel colSlot) atomIndex
        * coeff colSlot slot
        = (value + weight atomIndex)
          * tightDir (basisLabel slot) atomIndex := by
      have hrep := congrFun (congrFun hrepresentation atomIndex) slot
      rw [Matrix.mul_apply, Matrix.mul_apply] at hrep
      have hproj := projection_mulVec_tightDir_of_mem hdata
        (hmemActive slot) hmemSubset
      have hlhs : ∑ x, projection atomIndex x
          * tightBasisColumns tightDir basisLabel x slot
          = (projection *ᵥ tightDir (basisLabel slot)) atomIndex := rfl
      rw [hlhs, hproj] at hrep
      exact hrep.symm
    have hterm : ∀ colSlot, S slot colSlot * readVecs atomIndex colSlot
        = ((sq slot)⁻¹ * gramDiag slot)
          * (tightDir (basisLabel colSlot) atomIndex
              * coeff colSlot slot) := by
      intro colSlot
      rw [hSapply]
      show (sq slot)⁻¹ * (coeff slot colSlot * sq colSlot)
          * (sq colSlot * tightDir (basisLabel colSlot) atomIndex)
        = ((sq slot)⁻¹ * gramDiag slot)
          * (tightDir (basisLabel colSlot) atomIndex
              * coeff colSlot slot)
      have hgj := hsqsq colSlot
      have hxj := hx slot colSlot
      linear_combination ((sq slot)⁻¹ * coeff slot colSlot
          * tightDir (basisLabel colSlot) atomIndex) * hgj
        + ((sq slot)⁻¹
            * tightDir (basisLabel colSlot) atomIndex) * hxj
    have hmul : (S *ᵥ readVecs atomIndex) slot
        = ∑ colSlot, S slot colSlot * readVecs atomIndex colSlot := rfl
    rw [hmul, Finset.sum_congr rfl fun colSlot _ => hterm colSlot,
      ← Finset.mul_sum, hcarried]
    have hsimp : (sq slot)⁻¹ * gramDiag slot = sq slot := by
      rw [← hsqsq slot, ← mul_assoc, inv_mul_cancel₀ (hsq slot).ne', one_mul]
    show ((sq slot)⁻¹ * gramDiag slot)
        * ((value + weight atomIndex)
          * tightDir (basisLabel slot) atomIndex)
      = (value + weight atomIndex)
        * (sq slot * tightDir (basisLabel slot) atomIndex)
    rw [hsimp]
    ring
  -- the cone identity prices the hat row norms
  have hnorm : ∀ atomIndex : Fin 6,
      readVecs atomIndex ⬝ᵥ readVecs atomIndex = ((6 : ℕ) : ℝ)⁻¹ := by
    intro atomIndex
    have hentry : (tightBasisColumns tightDir basisLabel * gram
          * (tightBasisColumns tightDir basisLabel)ᵀ) atomIndex atomIndex
        = ∑ slot, gramDiag slot
            * (tightDir (basisLabel slot) atomIndex
              * tightDir (basisLabel slot) atomIndex) := by
      rw [hdiag, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun slot _ => ?_
      rw [Matrix.mul_diagonal, Matrix.transpose_apply]
      show tightDir (basisLabel slot) atomIndex * gramDiag slot
          * tightDir (basisLabel slot) atomIndex
        = gramDiag slot * (tightDir (basisLabel slot) atomIndex
            * tightDir (basisLabel slot) atomIndex)
      ring
    have hcone := hdata.assembly_diagonal atomIndex
    rw [← hHform, hentry] at hcone
    rw [dotProduct, ← hcone]
    refine Finset.sum_congr rfl fun slot _ => ?_
    show sq slot * tightDir (basisLabel slot) atomIndex
        * (sq slot * tightDir (basisLabel slot) atomIndex)
      = gramDiag slot * (tightDir (basisLabel slot) atomIndex
          * tightDir (basisLabel slot) atomIndex)
    have := hsqsq slot
    nlinarith [this]
  -- the read Gram and the column-Gram exchange
  refine ⟨S, Matrix.of fun rowSlot colSlot =>
    ∑ atomIndex : Fin 6, readVecs atomIndex rowSlot
      * readVecs atomIndex colSlot, readVecs, hSsymm, hSidem, hStrace,
    hsupp, hnz, hread, hnorm, fun _ _ => rfl, ?_⟩
  set columnGram := (tightBasisColumns tightDir basisLabel)ᵀ
    * tightBasisColumns tightDir basisLabel with hcolumnGram
  have hcolumnSymm : columnGramᵀ = columnGram := by
    rw [hcolumnGram, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hNM : columnGram * coeff = coeffᵀ * columnGram :=
    columnGram_exchange_of_representation hdata.isSymmetric hrepresentation
  have hNMsymm : (columnGram * coeff)ᵀ = columnGram * coeff := by
    rw [Matrix.transpose_mul, hcolumnSymm, hNM]
  have hgramEntry : ∀ rowSlot colSlot,
      (∑ atomIndex : Fin 6, readVecs atomIndex rowSlot
        * readVecs atomIndex colSlot)
      = sq rowSlot * sq colSlot * columnGram rowSlot colSlot := by
    intro rowSlot colSlot
    rw [hcolumnGram, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [Matrix.transpose_apply]
    show sq rowSlot * tightDir (basisLabel rowSlot) atomIndex
        * (sq colSlot * tightDir (basisLabel colSlot) atomIndex)
      = sq rowSlot * sq colSlot
        * (tightDir (basisLabel rowSlot) atomIndex
          * tightDir (basisLabel colSlot) atomIndex)
    ring
  ext rowSlot colSlot
  have hleftEntry : (S * Matrix.of fun a b =>
        ∑ atomIndex : Fin 6, readVecs atomIndex a * readVecs atomIndex b)
      rowSlot colSlot
      = sq rowSlot * sq colSlot * (columnGram * coeff) colSlot rowSlot := by
    rw [Matrix.mul_apply]
    have hterm : ∀ midSlot, S rowSlot midSlot
        * (Matrix.of fun a b => ∑ atomIndex : Fin 6,
            readVecs atomIndex a * readVecs atomIndex b) midSlot colSlot
        = sq rowSlot * sq colSlot
          * (columnGram colSlot midSlot * coeff midSlot rowSlot) := by
      intro midSlot
      rw [Matrix.of_apply, hgramEntry, hSapply]
      have hgm := hsqsq midSlot
      have hxm := hx rowSlot midSlot
      have hinv : (sq rowSlot)⁻¹ * sq rowSlot = 1 :=
        inv_mul_cancel₀ (hsq rowSlot).ne'
      have hsymEntry : columnGram midSlot colSlot
          = columnGram colSlot midSlot := by
        have h := congrFun (congrFun hcolumnSymm colSlot) midSlot
        rwa [Matrix.transpose_apply] at h
      rw [hsymEntry]
      have hstep : coeff rowSlot midSlot * (sq midSlot * sq midSlot)
          = (sq rowSlot * sq rowSlot) * coeff midSlot rowSlot := by
        rw [hgm, hsqsq rowSlot]; exact hxm
      have hgoal : (sq rowSlot)⁻¹ * (coeff rowSlot midSlot * sq midSlot)
            * (sq midSlot * sq colSlot * columnGram colSlot midSlot)
          = ((sq rowSlot)⁻¹ * sq rowSlot)
            * (sq rowSlot * sq colSlot
              * (columnGram colSlot midSlot * coeff midSlot rowSlot)) := by
        linear_combination ((sq rowSlot)⁻¹ * sq colSlot
          * columnGram colSlot midSlot) * hstep
      rw [hgoal, hinv, one_mul]
    rw [Finset.sum_congr rfl fun midSlot _ => hterm midSlot, ← Finset.mul_sum,
      Matrix.mul_apply]
  have hrightEntry : ((Matrix.of fun a b =>
        ∑ atomIndex : Fin 6, readVecs atomIndex a * readVecs atomIndex b)
      * S) rowSlot colSlot
      = sq rowSlot * sq colSlot * (columnGram * coeff) rowSlot colSlot := by
    rw [Matrix.mul_apply]
    have hterm : ∀ midSlot, (Matrix.of fun a b => ∑ atomIndex : Fin 6,
          readVecs atomIndex a * readVecs atomIndex b) rowSlot midSlot
        * S midSlot colSlot
        = sq rowSlot * sq colSlot
          * (columnGram rowSlot midSlot * coeff midSlot colSlot) := by
      intro midSlot
      rw [Matrix.of_apply, hgramEntry, hSapply]
      have hinv : sq midSlot * (sq midSlot)⁻¹ = 1 :=
        mul_inv_cancel₀ (hsq midSlot).ne'
      have hgoal : sq rowSlot * sq midSlot * columnGram rowSlot midSlot
            * ((sq midSlot)⁻¹ * (coeff midSlot colSlot * sq colSlot))
          = (sq midSlot * (sq midSlot)⁻¹)
            * (sq rowSlot * sq colSlot
              * (columnGram rowSlot midSlot * coeff midSlot colSlot)) := by
        ring
      rw [hgoal, hinv, one_mul]
    rw [Finset.sum_congr rfl fun midSlot _ => hterm midSlot, ← Finset.mul_sum,
      Matrix.mul_apply]
  rw [hleftEntry, hrightEntry]
  have hsym := congrFun (congrFun hNMsymm rowSlot) colSlot
  rw [Matrix.transpose_apply] at hsym
  rw [hsym]

/-! ## Layer 2 — the trace calculus of a commuting read frame -/

variable {slotCount : ℕ} {S readGram : Matrix (Fin slotCount) (Fin slotCount) ℝ}
variable {readVecs : Fin 6 → Fin slotCount → ℝ} {readVal : Fin 6 → ℝ}
variable {car : Fin 6 → Finset (Fin slotCount)}

/-- The capture energy of a hat row is its read value times its square
norm.  The support law kills every off-carrier slot, and the carried
rows price the rest. -/
theorem read_energy_eq
    (hsupp : ∀ atomIndex, ∀ slot ∉ car atomIndex, readVecs atomIndex slot = 0)
    (hread : ∀ atomIndex, ∀ slot ∈ car atomIndex,
      (S *ᵥ readVecs atomIndex) slot = readVal atomIndex * readVecs atomIndex slot)
    (atomIndex : Fin 6) :
    readVecs atomIndex ⬝ᵥ (S *ᵥ readVecs atomIndex)
      = readVal atomIndex * (readVecs atomIndex ⬝ᵥ readVecs atomIndex) := by
  classical
  rw [dotProduct, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun slot _ => ?_
  by_cases hslot : slot ∈ car atomIndex
  · rw [hread atomIndex slot hslot]; ring
  · rw [hsupp atomIndex slot hslot]; ring

/-- The read Gram has trace one: the diagonal collects the hat row
square norms, and the cone identity prices each one at one sixth. -/
theorem readGram_trace_eq_one
    (hgram : ∀ rowSlot colSlot, readGram rowSlot colSlot
      = ∑ atomIndex : Fin 6, readVecs atomIndex rowSlot
          * readVecs atomIndex colSlot)
    (hnorm : ∀ atomIndex : Fin 6,
      readVecs atomIndex ⬝ᵥ readVecs atomIndex = ((6 : ℕ) : ℝ)⁻¹) :
    Matrix.trace readGram = 1 := by
  classical
  have hswap : Matrix.trace readGram
      = ∑ atomIndex : Fin 6, readVecs atomIndex ⬝ᵥ readVecs atomIndex := by
    simp only [Matrix.trace, Matrix.diag_apply]
    rw [Finset.sum_congr rfl fun slot _ => hgram slot slot, Finset.sum_comm]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rfl
  rw [hswap, Finset.sum_congr rfl fun atomIndex _ => hnorm atomIndex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **THE CAPTURE TRACE.**  The trace of the capture product is the
read-value-weighted sum of the hat row square norms. -/
theorem capture_trace_eq
    (hgram : ∀ rowSlot colSlot, readGram rowSlot colSlot
      = ∑ atomIndex : Fin 6, readVecs atomIndex rowSlot
          * readVecs atomIndex colSlot)
    (hsupp : ∀ atomIndex, ∀ slot ∉ car atomIndex, readVecs atomIndex slot = 0)
    (hread : ∀ atomIndex, ∀ slot ∈ car atomIndex,
      (S *ᵥ readVecs atomIndex) slot = readVal atomIndex * readVecs atomIndex slot) :
    Matrix.trace (S * readGram)
      = ∑ atomIndex : Fin 6,
          readVal atomIndex * (readVecs atomIndex ⬝ᵥ readVecs atomIndex) := by
  classical
  have hentry : ∀ slot : Fin slotCount, (S * readGram) slot slot
      = ∑ atomIndex : Fin 6,
          readVecs atomIndex slot * (S *ᵥ readVecs atomIndex) slot := by
    intro slot
    rw [Matrix.mul_apply]
    have hstep : ∀ midSlot, S slot midSlot * readGram midSlot slot
        = ∑ atomIndex : Fin 6,
            readVecs atomIndex slot * (S slot midSlot * readVecs atomIndex midSlot) := by
      intro midSlot
      rw [hgram, Finset.mul_sum]
      refine Finset.sum_congr rfl fun atomIndex _ => ?_
      ring
    rw [Finset.sum_congr rfl fun midSlot _ => hstep midSlot, Finset.sum_comm]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [← Finset.mul_sum]
    rfl
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Finset.sum_congr rfl fun slot _ => hentry slot, Finset.sum_comm]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [show (∑ slot, readVecs atomIndex slot * (S *ᵥ readVecs atomIndex) slot)
      = readVecs atomIndex ⬝ᵥ (S *ᵥ readVecs atomIndex) from rfl]
  exact read_energy_eq hsupp hread atomIndex

/-- **THE COLUMN SELF-ENERGY LAW.**  When the read Gram commutes with
the conjugate, the squared capture column of a slot sums to the
read-value-weighted hat squares of that slot.  The commutation makes
`S Θ S = S Θ`, and the two diagonals of that product are the two
sides. -/
theorem read_column_self_energy (hsymm : Sᵀ = S) (hidem : S * S = S)
    (hgram : ∀ rowSlot colSlot, readGram rowSlot colSlot
      = ∑ atomIndex : Fin 6, readVecs atomIndex rowSlot
          * readVecs atomIndex colSlot)
    (hcomm : S * readGram = readGram * S)
    (hsupp : ∀ atomIndex, ∀ slot ∉ car atomIndex, readVecs atomIndex slot = 0)
    (hread : ∀ atomIndex, ∀ slot ∈ car atomIndex,
      (S *ᵥ readVecs atomIndex) slot = readVal atomIndex * readVecs atomIndex slot)
    (slot : Fin slotCount) :
    ∑ atomIndex : Fin 6, (S *ᵥ readVecs atomIndex) slot
        * (S *ᵥ readVecs atomIndex) slot
      = ∑ atomIndex : Fin 6,
          readVal atomIndex * (readVecs atomIndex slot * readVecs atomIndex slot) := by
  classical
  -- the commutation collapses the triple product
  have hcollapse : S * readGram * S = S * readGram := by
    rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hidem]
  -- the hat family as one matrix
  set readMat : Matrix (Fin slotCount) (Fin 6) ℝ :=
    Matrix.of fun rowSlot atomIndex => readVecs atomIndex rowSlot with hreadMat
  have hgramMat : readGram = readMat * readMatᵀ := by
    ext rowSlot colSlot
    rw [hgram, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [Matrix.transpose_apply]
    rfl
  have hcap : ∀ (rowSlot : Fin slotCount) (atomIndex : Fin 6),
      (S * readMat) rowSlot atomIndex = (S *ᵥ readVecs atomIndex) rowSlot := by
    intro rowSlot atomIndex
    rw [Matrix.mul_apply]
    rfl
  have hfac : S * readGram * S = (S * readMat) * (S * readMat)ᵀ := by
    rw [hgramMat, Matrix.transpose_mul, hsymm]
    simp only [Matrix.mul_assoc]
  have hleftDiag : (S * readGram * S) slot slot
      = ∑ atomIndex : Fin 6, (S *ᵥ readVecs atomIndex) slot
          * (S *ᵥ readVecs atomIndex) slot := by
    rw [hfac, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [Matrix.transpose_apply, hcap]
  have hrightDiag : (S * readGram) slot slot
      = ∑ atomIndex : Fin 6,
          readVal atomIndex * (readVecs atomIndex slot * readVecs atomIndex slot) := by
    rw [hgramMat, ← Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [Matrix.transpose_apply, hcap]
    show (S *ᵥ readVecs atomIndex) slot * readVecs atomIndex slot
      = readVal atomIndex * (readVecs atomIndex slot * readVecs atomIndex slot)
    by_cases hslot : slot ∈ car atomIndex
    · rw [hread atomIndex slot hslot]; ring
    · rw [hsupp atomIndex slot hslot]; ring
  rw [← hleftDiag, hcollapse, hrightDiag]

/-- The leak form of the column self-energy law: the off-carrier leak
mass of a slot equals the on-carrier hat mass at the parabola
`readVal * (1 - readVal)`. -/
theorem read_column_leak_identity (hsymm : Sᵀ = S) (hidem : S * S = S)
    (hgram : ∀ rowSlot colSlot, readGram rowSlot colSlot
      = ∑ atomIndex : Fin 6, readVecs atomIndex rowSlot
          * readVecs atomIndex colSlot)
    (hcomm : S * readGram = readGram * S)
    (hsupp : ∀ atomIndex, ∀ slot ∉ car atomIndex, readVecs atomIndex slot = 0)
    (hread : ∀ atomIndex, ∀ slot ∈ car atomIndex,
      (S *ᵥ readVecs atomIndex) slot = readVal atomIndex * readVecs atomIndex slot)
    (slot : Fin slotCount) :
    ∑ atomIndex ∈ Finset.univ.filter (fun atom : Fin 6 => slot ∉ car atom),
        (S *ᵥ readVecs atomIndex) slot * (S *ᵥ readVecs atomIndex) slot
      = ∑ atomIndex ∈ Finset.univ.filter (fun atom : Fin 6 => slot ∈ car atom),
          readVal atomIndex * (1 - readVal atomIndex)
            * (readVecs atomIndex slot * readVecs atomIndex slot) := by
  classical
  have hself := read_column_self_energy hsymm hidem hgram hcomm hsupp hread slot
  set carried := Finset.univ.filter (fun atom : Fin 6 => slot ∈ car atom)
    with hcarried
  have hcompl : Finset.univ.filter (fun atom : Fin 6 => slot ∉ car atom)
      = carriedᶜ := by
    ext atom
    simp [hcarried]
  have hsplitLeft : ∑ atomIndex ∈ carried, (S *ᵥ readVecs atomIndex) slot
        * (S *ᵥ readVecs atomIndex) slot
      + ∑ atomIndex ∈ carriedᶜ, (S *ᵥ readVecs atomIndex) slot
        * (S *ᵥ readVecs atomIndex) slot
      = ∑ atomIndex : Fin 6, (S *ᵥ readVecs atomIndex) slot
        * (S *ᵥ readVecs atomIndex) slot :=
    Finset.sum_add_sum_compl carried _
  have hsplitRight : ∑ atomIndex ∈ carried,
        readVal atomIndex * (readVecs atomIndex slot * readVecs atomIndex slot)
      + ∑ atomIndex ∈ carriedᶜ,
        readVal atomIndex * (readVecs atomIndex slot * readVecs atomIndex slot)
      = ∑ atomIndex : Fin 6,
        readVal atomIndex * (readVecs atomIndex slot * readVecs atomIndex slot) :=
    Finset.sum_add_sum_compl carried _
  have hzeroRight : ∑ atomIndex ∈ carriedᶜ,
      readVal atomIndex * (readVecs atomIndex slot * readVecs atomIndex slot) = 0 := by
    refine Finset.sum_eq_zero fun atomIndex hatom => ?_
    have hnot : slot ∉ car atomIndex := by
      have := Finset.mem_compl.mp hatom
      simpa [hcarried] using this
    rw [hsupp atomIndex slot hnot]
    ring
  have hcarriedLeft : ∑ atomIndex ∈ carried, (S *ᵥ readVecs atomIndex) slot
        * (S *ᵥ readVecs atomIndex) slot
      = ∑ atomIndex ∈ carried,
          readVal atomIndex * readVal atomIndex
            * (readVecs atomIndex slot * readVecs atomIndex slot) := by
    refine Finset.sum_congr rfl fun atomIndex hatom => ?_
    have hin : slot ∈ car atomIndex := by
      simpa [hcarried] using hatom
    rw [hread atomIndex slot hin]
    ring
  have hgoal : ∑ atomIndex ∈ carried,
      readVal atomIndex * (1 - readVal atomIndex)
        * (readVecs atomIndex slot * readVecs atomIndex slot)
      = ∑ atomIndex ∈ carried,
          readVal atomIndex * (readVecs atomIndex slot * readVecs atomIndex slot)
        - ∑ atomIndex ∈ carried,
          readVal atomIndex * readVal atomIndex
            * (readVecs atomIndex slot * readVecs atomIndex slot) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    ring
  rw [hcompl, hgoal]
  linarith [hsplitLeft, hsplitRight, hzeroRight, hcarriedLeft, hself]

/-! ## Layer 3 — the rank-six commuting frame -/

/-- **THE RANK-SIX FRAME PACKAGE.**  A rank-six frame with a diagonal
Gram core carries the commuting read frame. -/
theorem RankSixFrame.exists_commuting_read_frame {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {gramDiag : Fin 6 → ℝ}
    (hdiag : frame.gram = Matrix.diagonal gramDiag) :
    ∃ (S readGram : Matrix (Fin 6) (Fin 6) ℝ)
      (readVecs : Fin 6 → Fin 6 → ℝ),
      Sᵀ = S ∧ S * S = S ∧ Matrix.trace S = 3
      ∧ (∀ atomIndex : Fin 6,
          ∀ slot ∉ blockCarrier frame.activeSubset frame.basisLabel atomIndex,
          readVecs atomIndex slot = 0)
      ∧ (∀ atomIndex : Fin 6, readVecs atomIndex ≠ 0)
      ∧ (∀ atomIndex : Fin 6,
          ∀ slot ∈ blockCarrier frame.activeSubset frame.basisLabel atomIndex,
          (S *ᵥ readVecs atomIndex) slot
            = (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomIndex)
              * readVecs atomIndex slot)
      ∧ (∀ atomIndex : Fin 6,
          readVecs atomIndex ⬝ᵥ readVecs atomIndex = ((6 : ℕ) : ℝ)⁻¹)
      ∧ (∀ rowSlot colSlot, readGram rowSlot colSlot
          = ∑ atomIndex : Fin 6,
              readVecs atomIndex rowSlot * readVecs atomIndex colSlot)
      ∧ S * readGram = readGram * S := by
  obtain ⟨S, readGram, readVecs, hSsymm, hSidem, hStrace, hsupp, hnz, hread,
      hnorm, hgram, hcomm⟩ :=
    _root_.Gtz.exists_commuting_read_frame frame.hdata frame.hmemAll frame.hleft
      frame.hspan frame.hrepresentation frame.hidempotent frame.hexchange
      frame.hHform frame.hpsd frame.hker hdiag
  exact ⟨S, readGram, readVecs, hSsymm, hSidem, hStrace.trans frame.htrace,
    hsupp, hnz, hread, hnorm, hgram, hcomm⟩

/-- **THE RANK-SIX CAPTURE CEILING.**  At a rank-six frame with a
diagonal Gram core the capture trace is `(6 value + 1) / 6`, thus it is
strictly less than one sixth while the read Gram has trace one.  The
whole rank-six wall is this one inequality on a commuting pair. -/
theorem RankSixFrame.capture_trace_lt_inv_size {crux : SixThreeCrux}
    (frame : RankSixFrame crux)
    {S readGram : Matrix (Fin 6) (Fin 6) ℝ} {readVecs : Fin 6 → Fin 6 → ℝ}
    (hsupp : ∀ atomIndex : Fin 6,
      ∀ slot ∉ blockCarrier frame.activeSubset frame.basisLabel atomIndex,
      readVecs atomIndex slot = 0)
    (hread : ∀ atomIndex : Fin 6,
      ∀ slot ∈ blockCarrier frame.activeSubset frame.basisLabel atomIndex,
      (S *ᵥ readVecs atomIndex) slot
        = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
          * readVecs atomIndex slot)
    (hnorm : ∀ atomIndex : Fin 6,
      readVecs atomIndex ⬝ᵥ readVecs atomIndex = ((6 : ℕ) : ℝ)⁻¹)
    (hgram : ∀ rowSlot colSlot, readGram rowSlot colSlot
      = ∑ atomIndex : Fin 6,
          readVecs atomIndex rowSlot * readVecs atomIndex colSlot) :
    Matrix.trace (S * readGram)
        = (6 * chartObjective (chartPointOfDesign crux.design) + 1)
          * ((6 : ℕ) : ℝ)⁻¹
      ∧ Matrix.trace (S * readGram) < Matrix.trace readGram := by
  classical
  have htrace := capture_trace_eq hgram hsupp hread
  have hshift : ∑ atomIndex : Fin 6,
      (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
      = 6 * chartObjective (chartPointOfDesign crux.design) + 1 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, frame.hdata.weight_sum_one, nsmul_eq_mul]
    norm_num
  have hcollapse : (∑ atomIndex : Fin 6,
        (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * (readVecs atomIndex ⬝ᵥ readVecs atomIndex))
      = ∑ atomIndex : Fin 6,
          (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
          * ((6 : ℕ) : ℝ)⁻¹ :=
    Finset.sum_congr rfl fun atomIndex _ => by rw [hnorm atomIndex]
  have hvalue : Matrix.trace (S * readGram)
      = (6 * chartObjective (chartPointOfDesign crux.design) + 1)
        * ((6 : ℕ) : ℝ)⁻¹ := by
    rw [htrace, hcollapse, ← Finset.sum_mul, hshift]
  refine ⟨hvalue, ?_⟩
  rw [hvalue, readGram_trace_eq_one hgram hnorm]
  have hneg := frame.hvalueNeg
  have hsix : (0 : ℝ) < ((6 : ℕ) : ℝ)⁻¹ := by norm_num
  nlinarith [hneg, hsix]

/-! ## Layer 4 — the rank-six profile lattice -/

/-- The pin set of a rank-six frame: the atoms whose block carrier is a
single slot. -/
def RankSixFrame.pinSet {crux : SixThreeCrux} (frame : RankSixFrame crux) :
    Finset (Fin 6) :=
  Finset.univ.filter fun atomIndex =>
    (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card = 1

/-- The pair set of a rank-six frame: the atoms whose block carrier is a
slot pair. -/
def RankSixFrame.pairSet {crux : SixThreeCrux} (frame : RankSixFrame crux) :
    Finset (Fin 6) :=
  Finset.univ.filter fun atomIndex =>
    (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card = 2

/-- The pin set and the pair set are disjoint. -/
theorem RankSixFrame.pin_pair_disjoint {crux : SixThreeCrux}
    (frame : RankSixFrame crux) : Disjoint frame.pinSet frame.pairSet := by
  classical
  rw [Finset.disjoint_left]
  intro atomIndex hpin hpair
  rw [RankSixFrame.pinSet, Finset.mem_filter] at hpin
  rw [RankSixFrame.pairSet, Finset.mem_filter] at hpair
  omega

/-- Every pin-set atom carries a singleton block carrier. -/
theorem RankSixFrame.pinSet_singleton {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {atomIndex : Fin 6}
    (hmem : atomIndex ∈ frame.pinSet) :
    ∃ pinSlot, blockCarrier frame.activeSubset frame.basisLabel atomIndex
      = {pinSlot} := by
  classical
  rw [RankSixFrame.pinSet, Finset.mem_filter] at hmem
  exact Finset.card_eq_one.mp hmem.2

/-- Every pair-set atom carries a two-slot block carrier. -/
theorem RankSixFrame.pairSet_pair {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {atomIndex : Fin 6}
    (hmem : atomIndex ∈ frame.pairSet) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo ∧
      blockCarrier frame.activeSubset frame.basisLabel atomIndex
        = {slotOne, slotTwo} := by
  classical
  rw [RankSixFrame.pairSet, Finset.mem_filter] at hmem
  obtain ⟨slotOne, slotTwo, hne, hset⟩ := Finset.card_eq_two.mp hmem.2
  exact ⟨slotOne, slotTwo, hne, hset⟩

/-- **THE LOW-PROFILE RESIDUE.**  No rank-six outer datum has a pin and
pair profile of mass three or less. -/
def RankSixOuterLowProfileClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankSixOuterData crux),
    2 * data.frame.pinSet.card + data.frame.pairSet.card ≤ 3 → False

/-- **THE RANK-SIX KILL LATTICE.**  With the circuit residue and the
low-profile residue closed, no rank-six outer datum exists.  The
profile mass is four or more, thus the landed profile kill fires, or
the mass is three or less, thus the low-profile residue fires. -/
theorem rankSixOuterKilled_of_circuit_and_lowProfile
    (hcirc : RankSixOuterCircuitClosed)
    (hlow : RankSixOuterLowProfileClosed) : RankSixOuterKilled := by
  classical
  intro crux data
  by_cases hmass : 4 ≤ 2 * data.frame.pinSet.card + data.frame.pairSet.card
  · exact data.false_of_circuitClosed_profile hcirc data.frame.pinSet
      data.frame.pairSet data.frame.pin_pair_disjoint
      (fun atom hatom => data.frame.pinSet_singleton hatom)
      (fun atom hatom => data.frame.pairSet_pair hatom) hmass
  · exact hlow crux data (by omega)

/-- **THE RANK-SIX DISCHARGE.**  The support-two closure of the third
rung follows from the circuit residue and the low-profile residue. -/
theorem rankSixSupportTwoClosed_of_circuit_and_lowProfile
    (hcirc : RankSixOuterCircuitClosed)
    (hlow : RankSixOuterLowProfileClosed) : RankSixSupportTwoClosed :=
  rankSixSupportTwoClosed_of_outer_killed
    (rankSixOuterKilled_of_circuit_and_lowProfile hcirc hlow)

end Gtz

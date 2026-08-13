import Gtz.Wave.OuterResidueCollapse
import Gtz.Wave.SharedPrivateComplementTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The outer block-pin budget — the diagonal-Gram pin branch at three ranks

The vertex extraction of this session reduces the extras-free outer
kill to pure coefficient algebra: the carried rows, the idempotency,
the trace, the exchange law, the Gram self-adjointness, the cone
identity, and the shifted-weight floors.  Under a diagonal Gram core
the conjugated coefficient matrix is an orthogonal projection, the hat
rows are unit eigenvectors of its block corners, and the landed
carrier-budget kills apply.  The carrier here is the BLOCK carrier:
the slots whose card-3 block contains the atom.  Each slot meets
exactly three atoms, thus the incidence count is three at every rank,
and one block-pinned atom kills a trace-two coefficient matrix.  A
trace-three coefficient matrix needs two pinned atoms.

This file lands the generic core and the three frame wrappers.  The
rank-four wrapper consumes one pin, the rank-five wrapper consumes one
pin and a conditional second pin, and the rank-six wrapper consumes
two pins.  The dense branch, where no block pin exists, and the
boundary strata, where a shifted weight vanishes, stay open.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.blockCarrier_mem` — the carrier membership reading.
* `Gtz.false_of_diagonal_coefficient_block_pins` — **THE GENERIC
  CORE.**
* `Gtz.RankFourFrame.false_of_diagonal_gram_block_pin` — **THE
  RANK-FOUR PIN KILL.**
* `Gtz.RankFiveFrame.false_of_diagonal_gram_block_pin` — **THE
  RANK-FIVE PIN KILL.**
* `Gtz.RankSixFrame.false_of_diagonal_gram_block_pin` — **THE
  RANK-SIX PIN KILL.**

## Vacuity

The frame wrappers are vacuous if `Gtz.GtzWeighted 6 3` holds: no crux
exists, thus no frame exists.
-/

namespace Gtz

open Matrix

variable {activeIndex : Type*} {basisCount : ℕ}

/-- **THE BLOCK CARRIER.**  The basis slots whose block contains the
atom.  The carried rows hold at every atom of a block, thus the block
carrier is the carrier of the conjugated corner reads. -/
def blockCarrier (activeSubset : activeIndex → Finset (Fin 6))
    (basisLabel : Fin basisCount → activeIndex) (atomIndex : Fin 6) :
    Finset (Fin basisCount) :=
  Finset.univ.filter fun slot => atomIndex ∈ activeSubset (basisLabel slot)

/-- The carrier membership reading. -/
theorem blockCarrier_mem {activeSubset : activeIndex → Finset (Fin 6)}
    {basisLabel : Fin basisCount → activeIndex} {atomIndex : Fin 6}
    {slot : Fin basisCount} :
    slot ∈ blockCarrier activeSubset basisLabel atomIndex
      ↔ atomIndex ∈ activeSubset (basisLabel slot) := by
  simp [blockCarrier]

/-- **THE GENERIC CORE.**  A stationary datum with a basis, a
coefficient representation, a DIAGONAL kernel-free Gram core, interior
shifted weights, and enough block-pinned atoms dies.  The diagonal
conjugation of the coefficient matrix is an orthogonal projection, the
hat rows are unit eigenvectors of its block corners, and the landed
carrier budget closes.  A trace-two coefficient matrix needs one pin,
a trace-three coefficient matrix needs two. -/
theorem false_of_diagonal_coefficient_block_pins
    {projection : Matrix (Fin 6) (Fin 6) ℝ} {weight : Fin 6 → ℝ}
    {value : ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin 6 → ℝ)}
    (hdata : IsChartStationaryData 3 projection weight value activeSet
      activeSubset activeWeight tightDir)
    (hneg : value < 0)
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
    (hpsd : gram.PosSemidef)
    (hker : ∀ coeffVec : Fin basisCount → ℝ, gram *ᵥ coeffVec = 0 →
      coeffVec = 0)
    {gramDiag : Fin basisCount → ℝ}
    (hdiag : gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace coeff = 2 ∨ Matrix.trace coeff = 3)
    (hint : ∀ atomIndex : Fin 6, 0 < value + weight atomIndex)
    {pinAtom : Fin 6} {pinSlot : Fin basisCount}
    (hpin : blockCarrier activeSubset basisLabel pinAtom = {pinSlot})
    (hsecond : Matrix.trace coeff = 3 →
      ∃ atomTwo : Fin 6, atomTwo ≠ pinAtom ∧
        ∃ slotTwo : Fin basisCount,
          blockCarrier activeSubset basisLabel atomTwo = {slotTwo}) :
    False := by
  classical
  -- the positive diagonal of the Gram core
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
  -- the conjugate is symmetric
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
  -- the conjugate is idempotent
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
  -- the conjugate keeps the trace
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
  -- the carrier system: the BLOCK carrier and the hat rows
  set car : Fin 6 → Finset (Fin basisCount) := fun atomIndex =>
    blockCarrier activeSubset basisLabel atomIndex with hcardef
  set readVecs : Fin 6 → Fin basisCount → ℝ := fun atomIndex slot =>
    sq slot * tightDir (basisLabel slot) atomIndex with hreadVecs
  set shifted : Fin 6 → ℝ := fun atomIndex =>
    value + weight atomIndex with hshifted
  have hcarmem : ∀ atomIndex slot, slot ∈ car atomIndex ↔
      atomIndex ∈ activeSubset (basisLabel slot) := by
    intro atomIndex slot
    simp [hcardef, blockCarrier]
  -- the support law
  have hsupp : ∀ atomIndex, ∀ slot ∉ car atomIndex,
      readVecs atomIndex slot = 0 := by
    intro atomIndex slot hslot
    rw [hcarmem] at hslot
    show sq slot * tightDir (basisLabel slot) atomIndex = 0
    rw [hdata.tightDir_support (basisLabel slot) (hmemActive slot)
      atomIndex hslot, mul_zero]
  -- the coverage law
  have hnz : ∀ atomIndex, readVecs atomIndex ≠ 0 := by
    intro atomIndex hzero
    obtain ⟨slot, hslot⟩ := exists_basisIndex_datumTightSupport hdata
      basisLabel hspan leftInv hleft atomIndex
    have hq := mem_datumTightSupport.mp hslot
    have hv : readVecs atomIndex slot = 0 := congrFun hzero slot
    exact mul_ne_zero (hsq slot).ne' hq hv
  -- the carried rows at the block atoms
  have hcarried : ∀ slot, ∀ atomIndex ∈ activeSubset (basisLabel slot),
      ∑ colSlot, tightDir (basisLabel colSlot) atomIndex
        * coeff colSlot slot
      = shifted atomIndex * tightDir (basisLabel slot) atomIndex := by
    intro slot atomIndex hmemSubset
    have hrep := congrFun (congrFun hrepresentation atomIndex) slot
    rw [Matrix.mul_apply, Matrix.mul_apply] at hrep
    have hproj := projection_mulVec_tightDir_of_mem hdata
      (hmemActive slot) hmemSubset
    have hlhs : ∑ x, projection atomIndex x
        * tightBasisColumns tightDir basisLabel x slot
        = (projection *ᵥ tightDir (basisLabel slot)) atomIndex := rfl
    rw [hlhs, hproj] at hrep
    exact hrep.symm
  -- the corner reads
  have hread : ∀ atomIndex, ∀ slot ∈ car atomIndex,
      (S *ᵥ readVecs atomIndex) slot
        = shifted atomIndex * readVecs atomIndex slot := by
    intro atomIndex slot hslot
    have hmemSubset : atomIndex ∈ activeSubset (basisLabel slot) :=
      (hcarmem atomIndex slot).mp hslot
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
      ← Finset.mul_sum, hcarried slot atomIndex hmemSubset]
    have hsimp : (sq slot)⁻¹ * gramDiag slot = sq slot := by
      rw [← hsqsq slot, ← mul_assoc, inv_mul_cancel₀ (hsq slot).ne', one_mul]
    show ((sq slot)⁻¹ * gramDiag slot)
        * (shifted atomIndex * tightDir (basisLabel slot) atomIndex)
      = shifted atomIndex
        * (sq slot * tightDir (basisLabel slot) atomIndex)
    rw [hsimp]
    ring
  -- the incidence count: each slot's block has exactly three atoms
  have hinc : ∀ slot : Fin basisCount,
      (Finset.univ.filter fun atomIndex => slot ∈ car atomIndex).card
        = 3 := by
    intro slot
    have hpred : (Finset.univ.filter fun atomIndex => slot ∈ car atomIndex)
        = activeSubset (basisLabel slot) := by
      have hcongr : (Finset.univ.filter fun atomIndex =>
          slot ∈ car atomIndex)
          = Finset.univ.filter fun atomIndex =>
              atomIndex ∈ activeSubset (basisLabel slot) :=
        Finset.filter_congr fun atomIndex _ => by
          rw [hcarmem]
      rw [hcongr, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hpred]
    exact hdata.activeSubset_card (basisLabel slot) (hmemActive slot)
  -- the interior windows
  have hd0 : ∀ atomIndex, 0 < shifted atomIndex := hint
  have hd1 : ∀ atomIndex, shifted atomIndex < 1 := by
    intro atomIndex
    have hwle : weight atomIndex ≤ 1 := by
      have hsum := hdata.weight_sum_one
      have hle : weight atomIndex ≤ ∑ y, weight y :=
        Finset.single_le_sum (f := weight)
          (fun y _ => (hdata.weight_pos y).le) (Finset.mem_univ atomIndex)
      rwa [hsum] at hle
    have : shifted atomIndex = value + weight atomIndex := rfl
    rw [this]
    linarith
  have hsum : ∑ atomIndex, shifted atomIndex = 6 * value + 1 := by
    have hexpand : ∑ atomIndex : Fin 6, shifted atomIndex
        = ∑ atomIndex : Fin 6, (value + weight atomIndex) := rfl
    rw [hexpand, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, hdata.weight_sum_one, nsmul_eq_mul]
    norm_num
  -- the pins in carrier form
  have hpinOne : car pinAtom = {pinSlot} := hpin
  -- dispatch on the trace
  rcases htrace with htrace2 | htrace3
  · have hStrace2 : Matrix.trace S = 2 := by rw [hStrace, htrace2]
    exact false_of_interior_budget_trace_two hSsymm hSidem hStrace2 car
      readVecs shifted hinc hsupp hnz hread hd0 hd1 hsum hneg hpinOne
  · obtain ⟨atomTwo, hneq, slotTwo, hpinTwo⟩ := hsecond htrace3
    have hStrace3 : Matrix.trace S = 3 := by rw [hStrace, htrace3]
    exact false_of_interior_budget_trace_three hSsymm hSidem hStrace3 car
      readVecs shifted hinc hsupp hnz hread hd0 hd1 hsum hneg hneq.symm
      hpinOne hpinTwo

/-- **THE RANK-FOUR PIN KILL.**  A rank-four frame with a diagonal Gram
core, interior shifted weights, and one block-pinned atom dies.  The
coefficient trace is two, thus one pin closes the budget. -/
theorem RankFourFrame.false_of_diagonal_gram_block_pin
    {crux : SixThreeCrux} (frame : RankFourFrame crux)
    {gramDiag : Fin 4 → ℝ}
    (hdiag : frame.gram = Matrix.diagonal gramDiag)
    (hint : ∀ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
    {pinAtom : Fin 6} {pinSlot : Fin 4}
    (hpin : blockCarrier frame.activeSubset frame.basisLabel pinAtom
      = {pinSlot}) :
    False :=
  false_of_diagonal_coefficient_block_pins frame.hdata frame.hvalueNeg
    frame.hmemAll frame.hleft frame.hspan frame.hrepresentation
    frame.hidempotent frame.hexchange frame.hpsd frame.hker hdiag
    (Or.inl frame.htrace) hint hpin
    (fun htrace3 => absurd (frame.htrace ▸ htrace3) (by norm_num))

/-- **THE RANK-FIVE PIN KILL.**  A rank-five frame with a diagonal
Gram core, interior shifted weights, one block-pinned atom, and a
second pin at captured rank three dies. -/
theorem RankFiveFrame.false_of_diagonal_gram_block_pin
    {crux : SixThreeCrux} (frame : RankFiveFrame crux)
    {gramDiag : Fin 5 → ℝ}
    (hdiag : frame.gram = Matrix.diagonal gramDiag)
    (hint : ∀ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
    {pinAtom : Fin 6} {pinSlot : Fin 5}
    (hpin : blockCarrier frame.activeSubset frame.basisLabel pinAtom
      = {pinSlot})
    (hsecond : Matrix.trace frame.coeff = 3 →
      ∃ atomTwo : Fin 6, atomTwo ≠ pinAtom ∧
        ∃ slotTwo : Fin 5,
          blockCarrier frame.activeSubset frame.basisLabel atomTwo
            = {slotTwo}) :
    False :=
  false_of_diagonal_coefficient_block_pins frame.hdata frame.hvalueNeg
    frame.hmemAll frame.hleft frame.hspan frame.hrepresentation
    frame.hidempotent frame.hexchange frame.hpsd frame.hker hdiag
    frame.htrace hint hpin hsecond

/-- **THE RANK-SIX PIN KILL.**  A rank-six frame with a diagonal Gram
core, interior shifted weights, and two distinct block-pinned atoms
dies.  The coefficient trace is three, thus the budget needs the
second pin. -/
theorem RankSixFrame.false_of_diagonal_gram_block_pin
    {crux : SixThreeCrux} (frame : RankSixFrame crux)
    {gramDiag : Fin 6 → ℝ}
    (hdiag : frame.gram = Matrix.diagonal gramDiag)
    (hint : ∀ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
    {pinAtom atomTwo : Fin 6} {pinSlot slotTwo : Fin 6}
    (hne : atomTwo ≠ pinAtom)
    (hpin : blockCarrier frame.activeSubset frame.basisLabel pinAtom
      = {pinSlot})
    (hpinTwo : blockCarrier frame.activeSubset frame.basisLabel atomTwo
      = {slotTwo}) :
    False :=
  false_of_diagonal_coefficient_block_pins frame.hdata frame.hvalueNeg
    frame.hmemAll frame.hleft frame.hspan frame.hrepresentation
    frame.hidempotent frame.hexchange frame.hpsd frame.hker hdiag
    (Or.inr frame.htrace) hint hpin
    (fun _ => ⟨atomTwo, hne, slotTwo, hpinTwo⟩)

end Gtz

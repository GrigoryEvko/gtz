import Gtz.Wave.OuterBlockPinBudget
import Gtz.Wave.SharedPrivateStrataDispatch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The outer block-degree dispatch — the pin branch dies, the dense branch remains

The block-pin budget kills a diagonal-Gram frame with pinned atoms.
This file supplies the dispatch that finds the pins.  The block
carriers of the six atoms count the block incidences: each slot's
block has three atoms, thus the carrier cards sum to three times the
basis count.  At rank four the sum is twelve over six nonempty
carriers, thus either some atom carries one slot, or every atom
carries exactly two.  The refined budget of the strata dispatch
consumes the pin with interiority only at the atoms that carry three
or more slots, because the two-carrier trace cap is unconditional.
Thus the rank-four narrowing holds: a diagonal-Gram frame is either
dead or fully two-carrier.  The dense branch is the three-regular
multigraph geometry of the corner dichotomies.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.blockCarrier_nonempty` — the coverage of the block carriers.
* `Gtz.blockCarrier_fiber`, `Gtz.blockCarrier_incidence` — the fiber
  law and the incidence count.
* `Gtz.blockCarrier_double_count` — **THE DEGREE CENSUS.**
* `Gtz.exists_diagonal_conjugated_frame` — **THE CONJUGATED FRAME
  PACKAGE.**
* `Gtz.false_of_diagonal_coefficient_refined` — **THE REFINED GENERIC
  KILL.**
* `Gtz.RankFourFrame.blockPin_or_all_two` — **THE RANK-FOUR
  DICHOTOMY.**
* `Gtz.RankFourFrame.dense_of_diagonal_gram` — **THE RANK-FOUR
  NARROWING.**
* `Gtz.RankFiveFrame.false_of_diagonal_gram_refined`,
  `Gtz.RankSixFrame.false_of_diagonal_gram_refined` — the refined
  profile kills at the two other ranks.

## Vacuity

The frame statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no
crux exists, thus no frame exists.
-/

namespace Gtz

open Matrix

variable {activeIndex : Type*} {basisCount : ℕ}
variable {projection : Matrix (Fin 6) (Fin 6) ℝ} {weight : Fin 6 → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin 6)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin 6 → ℝ)}

/-! ## Layer 1 — the block-carrier census -/

/-- **THE COVERAGE.**  Every atom's block carrier is nonempty: some
basis support contains the atom, and supports sit inside blocks. -/
theorem blockCarrier_nonempty
    (hdata : IsChartStationaryData 3 projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    (hmemActive : ∀ slot, basisLabel slot ∈ activeSet)
    (hspan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    {leftInv : Matrix (Fin basisCount) (Fin 6) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (atomIndex : Fin 6) :
    (blockCarrier activeSubset basisLabel atomIndex).Nonempty := by
  obtain ⟨slot, hslot⟩ := exists_basisIndex_datumTightSupport hdata
    basisLabel hspan leftInv hleft atomIndex
  exact ⟨slot, blockCarrier_mem.mpr
    (datumTightSupport_subset hdata (hmemActive slot) hslot)⟩

/-- The fiber law: the atoms whose carrier holds a slot are exactly the
atoms of that slot's block. -/
theorem blockCarrier_fiber {basisLabel : Fin basisCount → activeIndex}
    (slot : Fin basisCount) :
    (Finset.univ.filter fun atomIndex : Fin 6 =>
      slot ∈ blockCarrier activeSubset basisLabel atomIndex)
    = activeSubset (basisLabel slot) := by
  have hcongr : (Finset.univ.filter fun atomIndex : Fin 6 =>
      slot ∈ blockCarrier activeSubset basisLabel atomIndex)
      = Finset.univ.filter fun atomIndex =>
          atomIndex ∈ activeSubset (basisLabel slot) :=
    Finset.filter_congr fun atomIndex _ => by rw [blockCarrier_mem]
  rw [hcongr, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- The incidence count: each slot sits in exactly three carriers. -/
theorem blockCarrier_incidence
    (hdata : IsChartStationaryData 3 projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    (hmemActive : ∀ slot, basisLabel slot ∈ activeSet)
    (slot : Fin basisCount) :
    (Finset.univ.filter fun atomIndex : Fin 6 =>
      slot ∈ blockCarrier activeSubset basisLabel atomIndex).card = 3 := by
  rw [blockCarrier_fiber]
  exact hdata.activeSubset_card (basisLabel slot) (hmemActive slot)

/-- **THE DEGREE CENSUS.**  The carrier cards sum to three times the
basis count. -/
theorem blockCarrier_double_count
    (hdata : IsChartStationaryData 3 projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    (hmemActive : ∀ slot, basisLabel slot ∈ activeSet) :
    ∑ atomIndex : Fin 6,
        (blockCarrier activeSubset basisLabel atomIndex).card
      = 3 * basisCount := by
  classical
  have hswap : ∑ atomIndex : Fin 6,
        (blockCarrier activeSubset basisLabel atomIndex).card
      = ∑ slot : Fin basisCount, ∑ atomIndex : Fin 6,
          if slot ∈ blockCarrier activeSubset basisLabel atomIndex
          then 1 else 0 := by
    rw [← Finset.sum_comm]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.card_eq_sum_ones]
  have hinner : ∀ slot : Fin basisCount,
      (∑ atomIndex : Fin 6,
        if slot ∈ blockCarrier activeSubset basisLabel atomIndex
        then 1 else 0) = 3 := by
    intro slot
    calc (∑ atomIndex : Fin 6,
          if slot ∈ blockCarrier activeSubset basisLabel atomIndex
          then 1 else 0)
        = ∑ atomIndex ∈ Finset.univ.filter fun atomIndex : Fin 6 =>
            slot ∈ blockCarrier activeSubset basisLabel atomIndex, 1 :=
          (Finset.sum_filter _ _).symm
      _ = (Finset.univ.filter fun atomIndex : Fin 6 =>
            slot ∈ blockCarrier activeSubset basisLabel atomIndex).card :=
          (Finset.card_eq_sum_ones _).symm
      _ = 3 := blockCarrier_incidence hdata hmemActive slot
  rw [hswap, Finset.sum_congr rfl fun slot _ => hinner slot,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_comm]

/-! ## Layer 2 — the conjugated frame package -/

/-- **THE CONJUGATED FRAME PACKAGE.**  A diagonal kernel-free Gram core
conjugates the coefficient matrix into a symmetric idempotent with the
same trace, and the hat rows read its block corners at the shifted
weights.  The package feeds every carrier-budget consumer. -/
theorem exists_diagonal_conjugated_frame
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
    (hpsd : gram.PosSemidef)
    (hker : ∀ coeffVec : Fin basisCount → ℝ, gram *ᵥ coeffVec = 0 →
      coeffVec = 0)
    {gramDiag : Fin basisCount → ℝ}
    (hdiag : gram = Matrix.diagonal gramDiag) :
    ∃ (S : Matrix (Fin basisCount) (Fin basisCount) ℝ)
      (readVecs : Fin 6 → Fin basisCount → ℝ),
      Sᵀ = S ∧ S * S = S ∧ Matrix.trace S = Matrix.trace coeff
      ∧ (∀ atomIndex : Fin 6,
          ∀ slot ∉ blockCarrier activeSubset basisLabel atomIndex,
          readVecs atomIndex slot = 0)
      ∧ (∀ atomIndex : Fin 6, readVecs atomIndex ≠ 0)
      ∧ (∀ atomIndex : Fin 6,
          ∀ slot ∈ blockCarrier activeSubset basisLabel atomIndex,
          (S *ᵥ readVecs atomIndex) slot
            = (value + weight atomIndex) * readVecs atomIndex slot) := by
  classical
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
  have hexchangeD := hexchange
  rw [hdiag] at hexchangeD
  have hx : ∀ rowSlot colSlot, coeff rowSlot colSlot * gramDiag colSlot
      = gramDiag rowSlot * coeff colSlot rowSlot := by
    intro rowSlot colSlot
    have h := congrFun (congrFun hexchangeD rowSlot) colSlot
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.transpose_apply] at h
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
  set readVecs : Fin 6 → Fin basisCount → ℝ := fun atomIndex slot =>
    sq slot * tightDir (basisLabel slot) atomIndex with hreadVecs
  refine ⟨S, readVecs, hSsymm, hSidem, hStrace, ?_, ?_, ?_⟩
  · intro atomIndex slot hslot
    rw [blockCarrier_mem] at hslot
    show sq slot * tightDir (basisLabel slot) atomIndex = 0
    rw [hdata.tightDir_support (basisLabel slot) (hmemActive slot)
      atomIndex hslot, mul_zero]
  · intro atomIndex hzero
    obtain ⟨slot, hslot⟩ := exists_basisIndex_datumTightSupport hdata
      basisLabel hspan leftInv hleft atomIndex
    have hq := mem_datumTightSupport.mp hslot
    have hv : readVecs atomIndex slot = 0 := congrFun hzero slot
    exact mul_ne_zero (hsq slot).ne' hq hv
  · intro atomIndex slot hslot
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

/-! ## Layer 3 — the refined generic kill -/

/-- **THE REFINED GENERIC KILL.**  The conjugated frame dies at the
refined budget: pins and two-carrier atoms need no interiority, and
the profile mass prices the trace.  Trace two needs one pin, trace
three needs profile mass four. -/
theorem false_of_diagonal_coefficient_refined
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
    (pinSet pairSet : Finset (Fin 6)) (hdisjoint : Disjoint pinSet pairSet)
    (hpinSet : ∀ atom ∈ pinSet, ∃ pinSlot,
      blockCarrier activeSubset basisLabel atom = {pinSlot})
    (hpairSet : ∀ atom ∈ pairSet, ∃ slotOne slotTwo, slotOne ≠ slotTwo ∧
      blockCarrier activeSubset basisLabel atom = {slotOne, slotTwo})
    (hint : ∀ atom, atom ∉ pinSet → atom ∉ pairSet →
      0 < value + weight atom)
    (hprofileTwo : Matrix.trace coeff = 2 → 1 ≤ pinSet.card)
    (hprofileThree : Matrix.trace coeff = 3 →
      4 ≤ 2 * pinSet.card + pairSet.card) :
    False := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsupp, hnz, hread⟩ :=
    exists_diagonal_conjugated_frame hdata hmemActive hleft hspan
      hrepresentation hidempotent hexchange hpsd hker hdiag
  have hinc : ∀ slot : Fin basisCount,
      (Finset.univ.filter fun atomIndex : Fin 6 =>
        slot ∈ blockCarrier activeSubset basisLabel atomIndex).card = 3 :=
    blockCarrier_incidence hdata hmemActive
  have hd1 : ∀ atom, atom ∉ pinSet → atom ∉ pairSet →
      value + weight atom < 1 := by
    intro atom _ _
    have hwle : weight atom ≤ 1 := by
      have hsum := hdata.weight_sum_one
      have hle : weight atom ≤ ∑ y, weight y :=
        Finset.single_le_sum (f := weight)
          (fun y _ => (hdata.weight_pos y).le) (Finset.mem_univ atom)
      rwa [hsum] at hle
    linarith
  have hsum : ∑ atom : Fin 6, (value + weight atom) = 6 * value + 1 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, hdata.weight_sum_one, nsmul_eq_mul]
    norm_num
  rcases htrace with htrace2 | htrace3
  · exact false_of_refined_budget_trace_two hSsymm hSidem
      (hStrace.trans htrace2) (blockCarrier activeSubset basisLabel)
      readVecs (fun atom => value + weight atom) hinc hsupp hnz hread
      pinSet pairSet hdisjoint hpinSet hpairSet hint hd1 hsum hneg
      (hprofileTwo htrace2)
  · exact false_of_refined_budget_trace_three hSsymm hSidem
      (hStrace.trans htrace3) (blockCarrier activeSubset basisLabel)
      readVecs (fun atom => value + weight atom) hinc hsupp hnz hread
      pinSet pairSet hdisjoint hpinSet hpairSet hint hd1 hsum hneg
      (hprofileThree htrace3)

/-! ## Layer 4 — the rank-four dichotomy and narrowing -/

/-- **THE RANK-FOUR DICHOTOMY.**  Twelve incidences over six nonempty
carriers: either some atom carries one slot, or every atom carries
exactly two. -/
theorem RankFourFrame.blockPin_or_all_two {crux : SixThreeCrux}
    (frame : RankFourFrame crux) :
    (∃ (pinAtom : Fin 6) (pinSlot : Fin 4),
      blockCarrier frame.activeSubset frame.basisLabel pinAtom
        = {pinSlot})
    ∨ ∀ atomIndex : Fin 6,
        (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card
          = 2 := by
  classical
  by_cases hone : ∃ atomIndex : Fin 6,
      (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card = 1
  · left
    obtain ⟨pinAtom, hcard⟩ := hone
    obtain ⟨pinSlot, hpin⟩ := Finset.card_eq_one.mp hcard
    exact ⟨pinAtom, pinSlot, hpin⟩
  · right
    push Not at hone
    have hlow : ∀ atomIndex : Fin 6, 2 ≤ (blockCarrier frame.activeSubset
        frame.basisLabel atomIndex).card := by
      intro atomIndex
      have hpos : 0 < (blockCarrier frame.activeSubset frame.basisLabel
          atomIndex).card :=
        Finset.card_pos.mpr (blockCarrier_nonempty frame.hdata
          frame.hmemAll frame.hspan frame.hleft atomIndex)
      have hne := hone atomIndex
      omega
    have hsum := blockCarrier_double_count frame.hdata frame.hmemAll
    intro atomIndex
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun atomOther => (blockCarrier frame.activeSubset frame.basisLabel
        atomOther).card)
      (Finset.mem_univ atomIndex)
    have herase : 5 * 2 ≤ ∑ atomOther ∈ Finset.univ.erase atomIndex,
        (blockCarrier frame.activeSubset frame.basisLabel
          atomOther).card := by
      have hb := Finset.card_nsmul_le_sum (Finset.univ.erase atomIndex)
        (fun atomOther => (blockCarrier frame.activeSubset frame.basisLabel
          atomOther).card) 2 (fun atomOther _ => hlow atomOther)
      rwa [Finset.card_erase_of_mem (Finset.mem_univ atomIndex),
        Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hb
    have hlowSelf := hlow atomIndex
    omega

/-- **THE RANK-FOUR NARROWING.**  A rank-four frame with a diagonal
Gram core and interior shifted weights at every three-plus-carrier
atom is fully two-carrier.  The pin branch dies at the refined budget:
the one-carrier atoms are the pins, the two-carrier atoms price
without interiority, and the trace is two. -/
theorem RankFourFrame.dense_of_diagonal_gram {crux : SixThreeCrux}
    (frame : RankFourFrame crux) {gramDiag : Fin 4 → ℝ}
    (hdiag : frame.gram = Matrix.diagonal gramDiag)
    (hint : ∀ atomIndex : Fin 6,
      2 < (blockCarrier frame.activeSubset frame.basisLabel
        atomIndex).card →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    ∀ atomIndex : Fin 6,
      (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card
        = 2 := by
  classical
  rcases frame.blockPin_or_all_two with ⟨pinAtom, pinSlot, hpin⟩ | hdense
  · exfalso
    refine false_of_diagonal_coefficient_refined frame.hdata
      frame.hvalueNeg frame.hmemAll frame.hleft frame.hspan
      frame.hrepresentation frame.hidempotent frame.hexchange frame.hpsd
      frame.hker hdiag (Or.inl frame.htrace)
      (Finset.univ.filter fun atomIndex : Fin 6 =>
        (blockCarrier frame.activeSubset frame.basisLabel
          atomIndex).card = 1)
      (Finset.univ.filter fun atomIndex : Fin 6 =>
        (blockCarrier frame.activeSubset frame.basisLabel
          atomIndex).card = 2)
      ?_ ?_ ?_ ?_ ?_ ?_
    · rw [Finset.disjoint_left]
      intro atom h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      omega
    · intro atom hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact Finset.card_eq_one.mp hmem
    · intro atom hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact Finset.card_eq_two.mp hmem
    · intro atom h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      have hpos : 0 < (blockCarrier frame.activeSubset frame.basisLabel
          atom).card :=
        Finset.card_pos.mpr (blockCarrier_nonempty frame.hdata
          frame.hmemAll frame.hspan frame.hleft atom)
      exact hint atom (by omega)
    · intro _
      have hmem : pinAtom ∈ Finset.univ.filter fun atomIndex : Fin 6 =>
          (blockCarrier frame.activeSubset frame.basisLabel
            atomIndex).card = 1 := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hpin]
        exact Finset.card_singleton pinSlot
      exact Finset.card_pos.mpr ⟨pinAtom, hmem⟩
    · intro htrace3
      exact absurd (frame.htrace ▸ htrace3) (by norm_num)
  · exact hdense

/-! ## Layer 5 — the refined profile kills at ranks five and six -/

/-- **THE RANK-FIVE REFINED KILL.**  A rank-five frame with a diagonal
Gram core dies at any profile with one pin at trace two, or with
profile mass four at trace three, with interiority only off the pins
and pairs. -/
theorem RankFiveFrame.false_of_diagonal_gram_refined {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {gramDiag : Fin 5 → ℝ}
    (hdiag : frame.gram = Matrix.diagonal gramDiag)
    (pinSet pairSet : Finset (Fin 6)) (hdisjoint : Disjoint pinSet pairSet)
    (hpinSet : ∀ atom ∈ pinSet, ∃ pinSlot,
      blockCarrier frame.activeSubset frame.basisLabel atom = {pinSlot})
    (hpairSet : ∀ atom ∈ pairSet, ∃ slotOne slotTwo, slotOne ≠ slotTwo ∧
      blockCarrier frame.activeSubset frame.basisLabel atom
        = {slotOne, slotTwo})
    (hint : ∀ atom, atom ∉ pinSet → atom ∉ pairSet →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atom)
    (hprofileTwo : Matrix.trace frame.coeff = 2 → 1 ≤ pinSet.card)
    (hprofileThree : Matrix.trace frame.coeff = 3 →
      4 ≤ 2 * pinSet.card + pairSet.card) :
    False :=
  false_of_diagonal_coefficient_refined frame.hdata frame.hvalueNeg
    frame.hmemAll frame.hleft frame.hspan frame.hrepresentation
    frame.hidempotent frame.hexchange frame.hpsd frame.hker hdiag
    frame.htrace pinSet pairSet hdisjoint hpinSet hpairSet hint
    hprofileTwo hprofileThree

/-- **THE RANK-SIX REFINED KILL.**  A rank-six frame with a diagonal
Gram core dies at profile mass four: the coefficient trace is three. -/
theorem RankSixFrame.false_of_diagonal_gram_refined {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {gramDiag : Fin 6 → ℝ}
    (hdiag : frame.gram = Matrix.diagonal gramDiag)
    (pinSet pairSet : Finset (Fin 6)) (hdisjoint : Disjoint pinSet pairSet)
    (hpinSet : ∀ atom ∈ pinSet, ∃ pinSlot,
      blockCarrier frame.activeSubset frame.basisLabel atom = {pinSlot})
    (hpairSet : ∀ atom ∈ pairSet, ∃ slotOne slotTwo, slotOne ≠ slotTwo ∧
      blockCarrier frame.activeSubset frame.basisLabel atom
        = {slotOne, slotTwo})
    (hint : ∀ atom, atom ∉ pinSet → atom ∉ pairSet →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atom)
    (hprofile : 4 ≤ 2 * pinSet.card + pairSet.card) :
    False :=
  false_of_diagonal_coefficient_refined frame.hdata frame.hvalueNeg
    frame.hmemAll frame.hleft frame.hspan frame.hrepresentation
    frame.hidempotent frame.hexchange frame.hpsd frame.hker hdiag
    (Or.inr frame.htrace) pinSet pairSet hdisjoint hpinSet hpairSet hint
    (fun htrace2 => absurd (frame.htrace ▸ htrace2) (by norm_num))
    (fun _ => hprofile)

end Gtz

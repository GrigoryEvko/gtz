import Gtz.Wave.DenseBlockGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The dense heavy-five structure — the block shape and the corner pins

The heavy-five profile of the rank-five dense branch carries a
multiplicity-five atom and five doubles.  The heavy atom sits in every
basis support, thus every support is the heavy atom together with a pair
of doubles, and each double names its exact carrier pair.

Two basis slots on one support then read the corner of the coefficient
matrix exactly.  The shared-block axis kill supplies the nondegeneracy,
the pair laws supply the trace and the determinant, and the shifted
weight sum caps the corner trace below one.  The trace budget pushes the
remaining three diagonal entries above one.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.carrier_pair_eq_of_multiplicity_two` — the carrier pair of a
  double atom is any pair of carriers it has.
* `Gtz.triple_insert_rotate` — the rotated atom triple.
* `Gtz.RankFiveFrame.heavyFive_support_pair` — **THE BLOCK SHAPE.**
* `Gtz.RankFiveFrame.heavyFive_crossDet_ne_zero` — the nondegeneracy at
  a shared support.
* `Gtz.RankFiveFrame.heavyFive_shared_corner_trace`,
  `Gtz.RankFiveFrame.heavyFive_shared_corner_determinant` — **THE CORNER
  PINS.**
* `Gtz.RankFiveFrame.heavyFive_shifted_weight_pair_le` — the shifted
  weight cap of a double pair.
* `Gtz.RankFiveFrame.heavyFive_shared_corner_lt_one` — the corner trace
  is less than one.
* `Gtz.RankFiveFrame.heavyFive_complement_trace_gt_one` — the remaining
  three diagonal entries exceed one.

## Vacuity

The frame statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no crux
exists, thus no frame exists.
-/

namespace Gtz

open Matrix

variable {size : ℕ} {activeIndex : Type*}
variable {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the carrier pair of a double atom -/

/-- Two carriers of a multiplicity-two atom are its only carriers. -/
theorem carrier_pair_eq_of_multiplicity_two
    (basisLabel : Fin basisCount → activeIndex) {atomIndex : Fin size}
    (hmult : basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    {slotOne slotTwo : Fin basisCount} (hslot : slotOne ≠ slotTwo)
    (hcoordOne : tightDir (basisLabel slotOne) atomIndex ≠ 0)
    (hcoordTwo : tightDir (basisLabel slotTwo) atomIndex ≠ 0) :
    ∀ slotIndex, slotIndex ≠ slotOne → slotIndex ≠ slotTwo →
      tightDir (basisLabel slotIndex) atomIndex = 0 := by
  classical
  rw [basisSupportMultiplicity] at hmult
  have hsubset : ({slotOne, slotTwo} : Finset (Fin basisCount))
      ⊆ Finset.univ.filter fun columnIndex =>
        atomIndex ∈ datumTightSupport tightDir (basisLabel columnIndex) := by
    intro slotIndex hmem
    rcases Finset.mem_insert.mp hmem with heq | hlast
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        heq ▸ mem_datumTightSupport.mpr hcoordOne⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_singleton.mp hlast) ▸ mem_datumTightSupport.mpr hcoordTwo⟩
  have hcards : (Finset.univ.filter fun columnIndex =>
      atomIndex ∈ datumTightSupport tightDir (basisLabel columnIndex)).card
      ≤ ({slotOne, slotTwo} : Finset (Fin basisCount)).card := by
    rw [hmult, Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact hslot), Finset.card_singleton]
  have hfilter := Finset.eq_of_subset_of_card_le hsubset hcards
  intro slotIndex hOne hTwo
  by_contra hne
  have hmemFilter : slotIndex ∈ Finset.univ.filter fun columnIndex =>
      atomIndex ∈ datumTightSupport tightDir (basisLabel columnIndex) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_datumTightSupport.mpr hne⟩
  rw [← hfilter] at hmemFilter
  rcases Finset.mem_insert.mp hmemFilter with heq | hlast
  · exact hOne heq
  · exact hTwo (Finset.mem_singleton.mp hlast)

/-- The rotated atom triple. -/
theorem triple_insert_rotate {α : Type*} [DecidableEq α] (first second third : α) :
    ({first, second, third} : Finset α) = {second, third, first} := by
  ext atomIndex
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-! ## Layer 2 — the block shape of the heavy-five profile -/

/-- **THE BLOCK SHAPE.**  At the heavy-five profile every basis support
is the heavy atom together with two distinct double atoms. -/
theorem RankFiveFrame.heavyFive_support_pair {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {heavyAtom : Fin 6}
    (hthree : ∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3)
    (hfive : basisSupportMultiplicity frame.tightDir frame.basisLabel heavyAtom
      = 5) (slotIndex : Fin 5) :
    ∃ atomOne atomTwo : Fin 6, atomOne ≠ atomTwo ∧ atomOne ≠ heavyAtom
      ∧ atomTwo ≠ heavyAtom
      ∧ datumTightSupport frame.tightDir (frame.basisLabel slotIndex)
        = {heavyAtom, atomOne, atomTwo} := by
  classical
  have hheavyMem : heavyAtom ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotIndex) :=
    forall_carrier_of_multiplicity_eq_card hfive slotIndex
  have herase : ((datumTightSupport frame.tightDir
      (frame.basisLabel slotIndex)).erase heavyAtom).card = 2 := by
    rw [Finset.card_erase_of_mem hheavyMem, hthree slotIndex]
  obtain ⟨atomOne, atomTwo, hne, hpair⟩ := Finset.card_eq_two.mp herase
  have hnotOne : atomOne ≠ heavyAtom := by
    have hmem : atomOne ∈ (datumTightSupport frame.tightDir
        (frame.basisLabel slotIndex)).erase heavyAtom := by
      rw [hpair]
      exact Finset.mem_insert_self _ _
    exact (Finset.mem_erase.mp hmem).1
  have hnotTwo : atomTwo ≠ heavyAtom := by
    have hmem : atomTwo ∈ (datumTightSupport frame.tightDir
        (frame.basisLabel slotIndex)).erase heavyAtom := by
      rw [hpair]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact (Finset.mem_erase.mp hmem).1
  refine ⟨atomOne, atomTwo, hne, hnotOne, hnotTwo, ?_⟩
  have hinsert := Finset.insert_erase hheavyMem
  rw [hpair] at hinsert
  exact hinsert.symm

/-! ## Layer 3 — the corner pins at a shared support -/

/-- The nondegeneracy at a shared support: the double pair of the block
has a nonzero cross determinant. -/
theorem RankFiveFrame.heavyFive_crossDet_ne_zero {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {heavyAtom atomOne atomTwo : Fin 6}
    (hpair : atomOne ≠ atomTwo) (hOneHeavy : atomOne ≠ heavyAtom)
    (hTwoHeavy : atomTwo ≠ heavyAtom)
    {slotOne slotTwo : Fin 5} (hslot : slotOne ≠ slotTwo)
    (hsupportOne : datumTightSupport frame.tightDir (frame.basisLabel slotOne)
      = {heavyAtom, atomOne, atomTwo})
    (hsupportTwo : datumTightSupport frame.tightDir (frame.basisLabel slotTwo)
      = {heavyAtom, atomOne, atomTwo}) :
    frame.tightDir (frame.basisLabel slotOne) atomOne
        * frame.tightDir (frame.basisLabel slotTwo) atomTwo
      - frame.tightDir (frame.basisLabel slotOne) atomTwo
        * frame.tightDir (frame.basisLabel slotTwo) atomOne ≠ 0 := by
  intro hcross
  refine frame.false_of_shared_support_cross_zero hslot hpair hOneHeavy
    hTwoHeavy ?_ ?_ hcross
  · rw [hsupportOne, triple_insert_rotate]
  · rw [hsupportTwo, triple_insert_rotate]

/-- **THE CORNER TRACE PIN.**  Two slots on one heavy-five support read
the corner trace of the coefficient matrix as the sum of the two double
shifted weights. -/
theorem RankFiveFrame.heavyFive_shared_corner_trace {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {heavyAtom atomOne atomTwo : Fin 6}
    (hpair : atomOne ≠ atomTwo) (hOneHeavy : atomOne ≠ heavyAtom)
    (hTwoHeavy : atomTwo ≠ heavyAtom)
    (hmultOne : basisSupportMultiplicity frame.tightDir frame.basisLabel atomOne
      = 2)
    (hmultTwo : basisSupportMultiplicity frame.tightDir frame.basisLabel atomTwo
      = 2)
    {slotOne slotTwo : Fin 5} (hslot : slotOne ≠ slotTwo)
    (hsupportOne : datumTightSupport frame.tightDir (frame.basisLabel slotOne)
      = {heavyAtom, atomOne, atomTwo})
    (hsupportTwo : datumTightSupport frame.tightDir (frame.basisLabel slotTwo)
      = {heavyAtom, atomOne, atomTwo}) :
    frame.coeff slotOne slotOne + frame.coeff slotTwo slotTwo
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomOne)
        + (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomTwo) := by
  have hmemOneOne : atomOne ∈ ({heavyAtom, atomOne, atomTwo}
      : Finset (Fin 6)) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hmemTwoTwo : atomTwo ∈ ({heavyAtom, atomOne, atomTwo}
      : Finset (Fin 6)) := Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hcoordOneOne := tightDir_ne_zero_of_support_triple hsupportOne hmemOneOne
  have hcoordOneTwo := tightDir_ne_zero_of_support_triple hsupportTwo hmemOneOne
  have hcoordTwoOne := tightDir_ne_zero_of_support_triple hsupportOne hmemTwoTwo
  have hcoordTwoTwo := tightDir_ne_zero_of_support_triple hsupportTwo hmemTwoTwo
  refine shared_carrier_pair_trace frame.hdata frame.basisLabel
    frame.hrepresentation hslot (frame.hmemAll slotOne) (frame.hmemAll slotTwo)
    (datumTightSupport_subset frame.hdata (frame.hmemAll slotOne)
      (mem_datumTightSupport.mpr hcoordOneOne))
    (datumTightSupport_subset frame.hdata (frame.hmemAll slotTwo)
      (mem_datumTightSupport.mpr hcoordOneTwo))
    (datumTightSupport_subset frame.hdata (frame.hmemAll slotOne)
      (mem_datumTightSupport.mpr hcoordTwoOne))
    (datumTightSupport_subset frame.hdata (frame.hmemAll slotTwo)
      (mem_datumTightSupport.mpr hcoordTwoTwo))
    (carrier_pair_eq_of_multiplicity_two frame.basisLabel hmultOne hslot
      hcoordOneOne hcoordOneTwo)
    (carrier_pair_eq_of_multiplicity_two frame.basisLabel hmultTwo hslot
      hcoordTwoOne hcoordTwoTwo)
    (frame.heavyFive_crossDet_ne_zero hpair hOneHeavy hTwoHeavy hslot
      hsupportOne hsupportTwo)

/-- **THE CORNER DETERMINANT PIN.**  The same corner reads the
determinant as the product of the two double shifted weights. -/
theorem RankFiveFrame.heavyFive_shared_corner_determinant {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {heavyAtom atomOne atomTwo : Fin 6}
    (hpair : atomOne ≠ atomTwo) (hOneHeavy : atomOne ≠ heavyAtom)
    (hTwoHeavy : atomTwo ≠ heavyAtom)
    (hmultOne : basisSupportMultiplicity frame.tightDir frame.basisLabel atomOne
      = 2)
    (hmultTwo : basisSupportMultiplicity frame.tightDir frame.basisLabel atomTwo
      = 2)
    {slotOne slotTwo : Fin 5} (hslot : slotOne ≠ slotTwo)
    (hsupportOne : datumTightSupport frame.tightDir (frame.basisLabel slotOne)
      = {heavyAtom, atomOne, atomTwo})
    (hsupportTwo : datumTightSupport frame.tightDir (frame.basisLabel slotTwo)
      = {heavyAtom, atomOne, atomTwo}) :
    frame.coeff slotOne slotOne * frame.coeff slotTwo slotTwo
        - frame.coeff slotOne slotTwo * frame.coeff slotTwo slotOne
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomOne)
        * (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomTwo) := by
  have hmemOneOne : atomOne ∈ ({heavyAtom, atomOne, atomTwo}
      : Finset (Fin 6)) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hmemTwoTwo : atomTwo ∈ ({heavyAtom, atomOne, atomTwo}
      : Finset (Fin 6)) := Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hcoordOneOne := tightDir_ne_zero_of_support_triple hsupportOne hmemOneOne
  have hcoordOneTwo := tightDir_ne_zero_of_support_triple hsupportTwo hmemOneOne
  have hcoordTwoOne := tightDir_ne_zero_of_support_triple hsupportOne hmemTwoTwo
  have hcoordTwoTwo := tightDir_ne_zero_of_support_triple hsupportTwo hmemTwoTwo
  refine shared_carrier_pair_determinant frame.hdata frame.basisLabel
    frame.hrepresentation hslot (frame.hmemAll slotOne) (frame.hmemAll slotTwo)
    (datumTightSupport_subset frame.hdata (frame.hmemAll slotOne)
      (mem_datumTightSupport.mpr hcoordOneOne))
    (datumTightSupport_subset frame.hdata (frame.hmemAll slotTwo)
      (mem_datumTightSupport.mpr hcoordOneTwo))
    (datumTightSupport_subset frame.hdata (frame.hmemAll slotOne)
      (mem_datumTightSupport.mpr hcoordTwoOne))
    (datumTightSupport_subset frame.hdata (frame.hmemAll slotTwo)
      (mem_datumTightSupport.mpr hcoordTwoTwo))
    (carrier_pair_eq_of_multiplicity_two frame.basisLabel hmultOne hslot
      hcoordOneOne hcoordOneTwo)
    (carrier_pair_eq_of_multiplicity_two frame.basisLabel hmultTwo hslot
      hcoordTwoOne hcoordTwoTwo)
    (frame.heavyFive_crossDet_ne_zero hpair hOneHeavy hTwoHeavy hslot
      hsupportOne hsupportTwo)

/-! ## Layer 4 — the corner trace budget -/

/-- The two double shifted weights of a shared support are capped by the
full shifted sum. -/
theorem RankFiveFrame.heavyFive_shifted_weight_pair_le {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {atomOne atomTwo : Fin 6}
    (hpair : atomOne ≠ atomTwo) :
    (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomOne)
      + (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomTwo)
      ≤ 6 * chartObjective (chartPointOfDesign crux.design) + 1 := by
  classical
  have hsum := frame.shifted_weight_sum
  have hsplitOne := Finset.add_sum_erase Finset.univ
    (fun atomIndex : Fin 6 => chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex)
    (Finset.mem_univ atomOne)
  have hmemTwo : atomTwo ∈ Finset.univ.erase atomOne :=
    Finset.mem_erase.mpr ⟨Ne.symm hpair, Finset.mem_univ _⟩
  have hsplitTwo := Finset.add_sum_erase (Finset.univ.erase atomOne)
    (fun atomIndex : Fin 6 => chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex) hmemTwo
  have hrest : 0 ≤ ∑ atomIndex ∈ (Finset.univ.erase atomOne).erase atomTwo,
      (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :=
    Finset.sum_nonneg fun atomIndex _ =>
      capture_diagonal_nonneg_of_isChartStationaryData frame.hdata atomIndex
  linarith [hsum, hsplitOne, hsplitTwo, hrest]

/-- **THE CORNER TRACE CAP.**  A shared heavy-five support has a corner
trace less than one. -/
theorem RankFiveFrame.heavyFive_shared_corner_lt_one {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {heavyAtom atomOne atomTwo : Fin 6}
    (hpair : atomOne ≠ atomTwo) (hOneHeavy : atomOne ≠ heavyAtom)
    (hTwoHeavy : atomTwo ≠ heavyAtom)
    (hmultOne : basisSupportMultiplicity frame.tightDir frame.basisLabel atomOne
      = 2)
    (hmultTwo : basisSupportMultiplicity frame.tightDir frame.basisLabel atomTwo
      = 2)
    {slotOne slotTwo : Fin 5} (hslot : slotOne ≠ slotTwo)
    (hsupportOne : datumTightSupport frame.tightDir (frame.basisLabel slotOne)
      = {heavyAtom, atomOne, atomTwo})
    (hsupportTwo : datumTightSupport frame.tightDir (frame.basisLabel slotTwo)
      = {heavyAtom, atomOne, atomTwo}) :
    frame.coeff slotOne slotOne + frame.coeff slotTwo slotTwo < 1 := by
  have htrace := frame.heavyFive_shared_corner_trace hpair hOneHeavy hTwoHeavy
    hmultOne hmultTwo hslot hsupportOne hsupportTwo
  have hcap := frame.heavyFive_shifted_weight_pair_le hpair
  have hneg := crux.hasNegativeChartValue
  linarith

/-- **THE COMPLEMENT TRACE.**  The three remaining diagonal entries of
the coefficient matrix exceed one. -/
theorem RankFiveFrame.heavyFive_complement_trace_gt_one {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {heavyAtom atomOne atomTwo : Fin 6}
    (hpair : atomOne ≠ atomTwo) (hOneHeavy : atomOne ≠ heavyAtom)
    (hTwoHeavy : atomTwo ≠ heavyAtom)
    (hmultOne : basisSupportMultiplicity frame.tightDir frame.basisLabel atomOne
      = 2)
    (hmultTwo : basisSupportMultiplicity frame.tightDir frame.basisLabel atomTwo
      = 2)
    (htrace : Matrix.trace frame.coeff = 2)
    {slotOne slotTwo : Fin 5} (hslot : slotOne ≠ slotTwo)
    (hsupportOne : datumTightSupport frame.tightDir (frame.basisLabel slotOne)
      = {heavyAtom, atomOne, atomTwo})
    (hsupportTwo : datumTightSupport frame.tightDir (frame.basisLabel slotTwo)
      = {heavyAtom, atomOne, atomTwo}) :
    1 < ∑ slotIndex ∈ (Finset.univ.erase slotOne).erase slotTwo,
      frame.coeff slotIndex slotIndex := by
  classical
  have hcorner := frame.heavyFive_shared_corner_lt_one hpair hOneHeavy hTwoHeavy
    hmultOne hmultTwo hslot hsupportOne hsupportTwo
  have hdiagSum : ∑ slotIndex : Fin 5, frame.coeff slotIndex slotIndex = 2 := by
    rw [← htrace, Matrix.trace]
    rfl
  have hsplitOne := Finset.add_sum_erase Finset.univ
    (fun slotIndex : Fin 5 => frame.coeff slotIndex slotIndex)
    (Finset.mem_univ slotOne)
  have hmemTwo : slotTwo ∈ Finset.univ.erase slotOne :=
    Finset.mem_erase.mpr ⟨Ne.symm hslot, Finset.mem_univ _⟩
  have hsplitTwo := Finset.add_sum_erase (Finset.univ.erase slotOne)
    (fun slotIndex : Fin 5 => frame.coeff slotIndex slotIndex) hmemTwo
  linarith [hdiagSum, hsplitOne, hsplitTwo]

end Gtz

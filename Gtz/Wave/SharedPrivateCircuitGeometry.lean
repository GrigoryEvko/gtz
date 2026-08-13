import Gtz.Wave.SharedPrivateSpectralSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The circuit geometry — the extras residue narrows to the wide circuits

The extras fold turned the non-diagonal Gram stratum into one residue:
a positive label parallel to no basis column.  This module reads that
residue in the coefficient frame and narrows it.

The coefficient frame.  Every positive label reconstructs from the
basis columns through the left inverse, thus it carries a coefficient
vector.  A coefficient vector on one slot IS a parallel label, thus the
circuit residue carries at least two nonzero coefficients.  Outside the
label block the reconstruction vanishes, thus the coefficients solve one
linear equation per outside atom.

The pin.  The pin atom sits in one basis support only.  Thus the outside
equation at the pin atom kills the private coefficient whenever the pin
atom sits outside the label block, and the label reads the private
coefficient at the pin atom otherwise.

The pair circuits.  A circuit on exactly two slots pins the two outside
parts to be proportional.  Thus the two supports agree outside the label
block.  Either the two supports are the whole label block, and then the
pin atom cannot sit in that block, or the two slots share an atom.  The
first branch dies at the pin, thus every pair circuit makes its two
slots share an atom.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.SharedPrivateData.labelCoeff` with
  `Gtz.SharedPrivateData.reconstruction_apply` and
  `Gtz.SharedPrivateData.circuit_equation` — the coefficient frame.
* `Gtz.SharedPrivateData.parallel_of_labelCoeff_single` — **A ONE-SLOT
  COEFFICIENT IS A PARALLEL LABEL.**
* `Gtz.SharedPrivateData.exists_two_slots_of_circuit` — the circuit
  residue carries two slots.
* `Gtz.SharedPrivateData.labelCoeff_privateSlot_eq_zero` — **THE PIN
  PRIVACY LAW.**
* `Gtz.SharedPrivateData.outside_proportional_of_pair` — **THE OUTSIDE
  PROPORTION LAW.**
* `Gtz.SharedPrivateData.false_of_pair_inside_pin` — **THE PAIR KILL AT
  THE PIN BLOCK.**
* `Gtz.SharedPrivateData.share_atom_of_pair_circuit` — **THE PAIR
  CIRCUITS SHARE AN ATOM.**
* `Gtz.SharedPrivateCircuitPairClosed`,
  `Gtz.SharedPrivateCircuitWideClosed` — the two circuit residues.
* `Gtz.sharedPrivateCircuitClosed_of_width`,
  `Gtz.sharedPrivateExtrasClosed_of_width` — the circuit dispatch.

## Vacuity

The statements quantify over shared-private data, and no datum exists if
`Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the coefficient frame of a positive label -/

/-- The coefficient vector of a label against the basis columns. -/
noncomputable def SharedPrivateData.labelCoeff {crux : SixThreeCrux}
    (data : SharedPrivateData crux) (label : data.activeIndex) :
    Fin data.basisCount → ℝ :=
  data.leftInv *ᵥ data.tightDir label

/-- The reconstruction of a positive label at one atom. -/
theorem SharedPrivateData.reconstruction_apply {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {label : data.activeIndex}
    (hmem : label ∈ data.activeSet) (hpos : 0 < data.reducedWeight label)
    (atomIndex : Fin 6) :
    data.tightDir label atomIndex
      = ∑ slot, data.labelCoeff label slot
          * data.tightDir (data.basisLabel slot) atomIndex := by
  classical
  have hpositive : label ∈ positiveActiveSet data.activeSet data.reducedWeight :=
    Finset.mem_filter.mpr ⟨hmem, hpos⟩
  exact reconstruction_apply_of_mem_positive data.hdata data.basisLabel data.hspan
    data.leftInv data.hleft hpositive atomIndex

/-- **THE CIRCUIT EQUATION.**  Outside the label block the coefficient
combination of the basis columns vanishes. -/
theorem SharedPrivateData.circuit_equation {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {label : data.activeIndex}
    (hmem : label ∈ data.activeSet) (hpos : 0 < data.reducedWeight label)
    {atomIndex : Fin 6} (hout : atomIndex ∉ data.activeSubset label) :
    ∑ slot, data.labelCoeff label slot
        * data.tightDir (data.basisLabel slot) atomIndex = 0 := by
  classical
  have hpositive : label ∈ positiveActiveSet data.activeSet data.reducedWeight :=
    Finset.mem_filter.mpr ⟨hmem, hpos⟩
  exact circuit_equation_of_mem_positive_of_notMem data.hdata data.basisLabel
    data.hspan data.leftInv data.hleft hpositive hout

/-- **A ONE-SLOT COEFFICIENT IS A PARALLEL LABEL.**  If every coefficient
outside one slot vanishes, the label is a multiple of that basis
column. -/
theorem SharedPrivateData.parallel_of_labelCoeff_single {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {label : data.activeIndex}
    (hmem : label ∈ data.activeSet) (hpos : 0 < data.reducedWeight label)
    {pivot : Fin data.basisCount}
    (hsingle : ∀ slot, slot ≠ pivot → data.labelCoeff label slot = 0) :
    data.tightDir label
      = data.labelCoeff label pivot • data.tightDir (data.basisLabel pivot) := by
  classical
  funext atomIndex
  rw [Pi.smul_apply, smul_eq_mul, data.reconstruction_apply hmem hpos atomIndex]
  exact Finset.sum_eq_single pivot
    (fun slot _ hne => by rw [hsingle slot hne, zero_mul])
    (fun hnot => absurd (Finset.mem_univ _) hnot)

/-- The circuit residue carries two distinct slots with nonzero
coefficients. -/
theorem SharedPrivateData.exists_two_slots_of_circuit {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {label : data.activeIndex}
    (hmem : label ∈ data.activeSet) (hpos : 0 < data.reducedWeight label)
    (hcircuit : ∀ (slot : Fin data.basisCount) (scale : ℝ),
      data.tightDir label ≠ scale • data.tightDir (data.basisLabel slot)) :
    ∃ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo
      ∧ data.labelCoeff label slotOne ≠ 0
      ∧ data.labelCoeff label slotTwo ≠ 0 := by
  classical
  by_contra hnot
  push Not at hnot
  -- at most one slot carries a nonzero coefficient
  by_cases hall : ∀ slot, data.labelCoeff label slot = 0
  · exact hcircuit data.privateSlot 0
      (data.parallel_of_labelCoeff_single hmem hpos
        (fun slot _ => hall slot) |>.trans (by rw [hall data.privateSlot]))
  · push Not at hall
    obtain ⟨pivot, hpivot⟩ := hall
    have hsingle : ∀ slot, slot ≠ pivot → data.labelCoeff label slot = 0 :=
      fun slot hne => hnot pivot slot (Ne.symm hne) hpivot
    exact hcircuit pivot (data.labelCoeff label pivot)
      (data.parallel_of_labelCoeff_single hmem hpos hsingle)

/-! ## Layer 2 — the pin privacy law -/

/-- The label reads the private coefficient at the pin atom: every other
basis column dies there. -/
theorem SharedPrivateData.tightDir_pinAtom_eq {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {label : data.activeIndex}
    (hmem : label ∈ data.activeSet) (hpos : 0 < data.reducedWeight label) :
    data.tightDir label data.pinAtom
      = data.labelCoeff label data.privateSlot
        * data.tightDir (data.basisLabel data.privateSlot) data.pinAtom := by
  classical
  rw [data.reconstruction_apply hmem hpos data.pinAtom]
  exact Finset.sum_eq_single data.privateSlot
    (fun slot _ hne => by rw [data.hprivate slot hne, mul_zero])
    (fun hnot => absurd (Finset.mem_univ _) hnot)

/-- **THE PIN PRIVACY LAW.**  A positive label whose block misses the pin
atom has a zero private coefficient. -/
theorem SharedPrivateData.labelCoeff_privateSlot_eq_zero {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {label : data.activeIndex}
    (hmem : label ∈ data.activeSet) (hpos : 0 < data.reducedWeight label)
    (hout : data.pinAtom ∉ data.activeSubset label) :
    data.labelCoeff label data.privateSlot = 0 := by
  classical
  have hcircuit := data.circuit_equation hmem hpos hout
  have hcollapse : ∑ slot, data.labelCoeff label slot
      * data.tightDir (data.basisLabel slot) data.pinAtom
      = data.labelCoeff label data.privateSlot
        * data.tightDir (data.basisLabel data.privateSlot) data.pinAtom :=
    Finset.sum_eq_single data.privateSlot
      (fun slot _ hne => by rw [data.hprivate slot hne, mul_zero])
      (fun hnot => absurd (Finset.mem_univ _) hnot)
  rw [hcollapse] at hcircuit
  exact (mul_eq_zero.mp hcircuit).resolve_right data.hpinNe

/-! ## Layer 3 — the pair circuits -/

/-- **THE OUTSIDE PROPORTION LAW.**  A circuit on exactly two slots pins
the two outside parts against each other at every atom outside the label
block. -/
theorem SharedPrivateData.outside_proportional_of_pair {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {label : data.activeIndex}
    (hmem : label ∈ data.activeSet) (hpos : 0 < data.reducedWeight label)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hpair : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      data.labelCoeff label slot = 0)
    {atomIndex : Fin 6} (hout : atomIndex ∉ data.activeSubset label) :
    data.labelCoeff label slotOne
        * data.tightDir (data.basisLabel slotOne) atomIndex
      + data.labelCoeff label slotTwo
        * data.tightDir (data.basisLabel slotTwo) atomIndex = 0 := by
  classical
  have hcircuit := data.circuit_equation hmem hpos hout
  have hcollapse : ∑ slot, data.labelCoeff label slot
      * data.tightDir (data.basisLabel slot) atomIndex
      = data.labelCoeff label slotOne
          * data.tightDir (data.basisLabel slotOne) atomIndex
        + data.labelCoeff label slotTwo
          * data.tightDir (data.basisLabel slotTwo) atomIndex := by
    have hrestrict : ∑ slot, data.labelCoeff label slot
        * data.tightDir (data.basisLabel slot) atomIndex
        = ∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin data.basisCount)),
            data.labelCoeff label slot
              * data.tightDir (data.basisLabel slot) atomIndex := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro slot _ hnot
      have honeNe : slot ≠ slotOne := fun heq =>
        hnot (heq ▸ Finset.mem_insert_self _ _)
      have htwoNe : slot ≠ slotTwo := fun heq =>
        hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rw [hpair slot honeNe htwoNe, zero_mul]
    rw [hrestrict, Finset.sum_pair hne]
  rw [hcollapse] at hcircuit
  exact hcircuit

/-- **THE PAIR KILL AT THE PIN BLOCK.**  Two distinct basis supports
cannot both sit inside a label block that holds the pin atom: the pin
atom would then sit in two basis supports. -/
theorem SharedPrivateData.false_of_pair_inside_pin {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {label : data.activeIndex}
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hpin : data.pinAtom ∈ data.activeSubset label)
    (hcardLabel : (data.activeSubset label).card = 3)
    (hinsideOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      ⊆ data.activeSubset label)
    (hinsideTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      ⊆ data.activeSubset label) :
    False := by
  classical
  have heqOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = data.activeSubset label :=
    Finset.eq_of_subset_of_card_le hinsideOne
      (by rw [hcardLabel, data.hthree slotOne])
  have heqTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = data.activeSubset label :=
    Finset.eq_of_subset_of_card_le hinsideTwo
      (by rw [hcardLabel, data.hthree slotTwo])
  have hpinOne : data.tightDir (data.basisLabel slotOne) data.pinAtom ≠ 0 :=
    mem_datumTightSupport.mp (by rw [heqOne]; exact hpin)
  have hpinTwo : data.tightDir (data.basisLabel slotTwo) data.pinAtom ≠ 0 :=
    mem_datumTightSupport.mp (by rw [heqTwo]; exact hpin)
  have hslotOne : slotOne = data.privateSlot := by
    by_contra hcontra
    exact hpinOne (data.hprivate slotOne hcontra)
  have hslotTwo : slotTwo = data.privateSlot := by
    by_contra hcontra
    exact hpinTwo (data.hprivate slotTwo hcontra)
  exact hne (hslotOne.trans hslotTwo.symm)

/-- **THE PAIR CIRCUITS SHARE AN ATOM.**  A circuit on exactly two slots
whose label block holds the pin atom makes the two basis supports share
an atom.  Either some support reaches outside the block, and then the
outside proportion law puts the other one there too, or both supports
fill the block and the pin kill fires. -/
theorem SharedPrivateData.share_atom_of_pair_circuit {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {label : data.activeIndex}
    (hmem : label ∈ data.activeSet) (hpos : 0 < data.reducedWeight label)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hcoeffOne : data.labelCoeff label slotOne ≠ 0)
    (hcoeffTwo : data.labelCoeff label slotTwo ≠ 0)
    (hpair : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      data.labelCoeff label slot = 0)
    (hpin : data.pinAtom ∈ data.activeSubset label) :
    ∃ atomIndex : Fin 6,
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne)
      ∧ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
  classical
  have hcardLabel : (data.activeSubset label).card = 3 :=
    data.hdata.activeSubset_card label hmem
  by_cases houtOne : ∃ atomIndex : Fin 6,
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne)
      ∧ atomIndex ∉ data.activeSubset label
  · obtain ⟨atomIndex, hsupport, hout⟩ := houtOne
    refine ⟨atomIndex, hsupport, ?_⟩
    have hprop := data.outside_proportional_of_pair hmem hpos hne hpair hout
    have hvalOne : data.tightDir (data.basisLabel slotOne) atomIndex ≠ 0 :=
      mem_datumTightSupport.mp hsupport
    have hvalTwo : data.tightDir (data.basisLabel slotTwo) atomIndex ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero, add_zero] at hprop
      exact hvalOne ((mul_eq_zero.mp hprop).resolve_left hcoeffOne)
    exact mem_datumTightSupport.mpr hvalTwo
  · push Not at houtOne
    have hinsideOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
        ⊆ data.activeSubset label := fun atomIndex hsupport =>
      houtOne atomIndex hsupport
    -- the second support also stays inside
    have hinsideTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
        ⊆ data.activeSubset label := by
      intro atomIndex hsupport
      by_contra hout
      have hprop := data.outside_proportional_of_pair hmem hpos hne hpair hout
      have hvalTwo : data.tightDir (data.basisLabel slotTwo) atomIndex ≠ 0 :=
        mem_datumTightSupport.mp hsupport
      have hvalOne : data.tightDir (data.basisLabel slotOne) atomIndex = 0 := by
        by_contra hcontra
        exact hout (hinsideOne (mem_datumTightSupport.mpr hcontra))
      rw [hvalOne, mul_zero, zero_add] at hprop
      exact hvalTwo ((mul_eq_zero.mp hprop).resolve_left hcoeffTwo)
    exact absurd (data.false_of_pair_inside_pin hne hpin hcardLabel hinsideOne
      hinsideTwo) not_false

/-! ## Layer 4 — the circuit residues and the dispatch -/

/-- **THE PAIR CIRCUIT RESIDUE.**  A positive label whose coefficient
vector sits on exactly two slots, and which is parallel to no basis
column, dies. -/
def SharedPrivateCircuitPairClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      (∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
        data.labelCoeff label slot = 0) →
      False

/-- **THE WIDE CIRCUIT RESIDUE.**  A positive label whose coefficient
vector sits on three or more slots dies. -/
def SharedPrivateCircuitWideClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo slotThree : Fin data.basisCount,
      slotOne ≠ slotTwo → slotOne ≠ slotThree → slotTwo ≠ slotThree →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      data.labelCoeff label slotThree ≠ 0 →
      False

/-- **THE CIRCUIT DISPATCH.**  The width of the coefficient support
splits the circuit residue in two. -/
theorem sharedPrivateCircuitClosed_of_width
    (hpair : SharedPrivateCircuitPairClosed)
    (hwide : SharedPrivateCircuitWideClosed) :
    SharedPrivateCircuitClosed := by
  classical
  intro crux data label hmem hpos hcircuit
  obtain ⟨slotOne, slotTwo, hne, hcoeffOne, hcoeffTwo⟩ :=
    data.exists_two_slots_of_circuit hmem hpos hcircuit
  by_cases hthird : ∃ slotThree : Fin data.basisCount,
    slotThree ≠ slotOne ∧ slotThree ≠ slotTwo
      ∧ data.labelCoeff label slotThree ≠ 0
  · obtain ⟨slotThree, honeNe, htwoNe, hcoeffThree⟩ := hthird
    exact hwide crux data label hmem hpos slotOne slotTwo slotThree hne
      (Ne.symm honeNe) (Ne.symm htwoNe) hcoeffOne hcoeffTwo hcoeffThree
  · push Not at hthird
    refine hpair crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo
      fun slot honeNe htwoNe => ?_
    exact hthird slot honeNe htwoNe

/-- The extras residue through the circuit width. -/
theorem sharedPrivateExtrasClosed_of_width
    (hpair : SharedPrivateCircuitPairClosed)
    (hwide : SharedPrivateCircuitWideClosed) :
    SharedPrivateExtrasClosed :=
  sharedPrivateExtrasClosed_of_circuit
    (sharedPrivateCircuitClosed_of_width hpair hwide)

end Gtz

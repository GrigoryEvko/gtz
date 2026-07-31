/-
# The compatible graph of the `(7,3)` equal-share stratum always has a triangle

`Gtz.dominates_triple_iff_isElliptopeGoodTriangle` splits domination at a heavy
triple into an EDGE half — the three `2 x 2` gap minors are nonnegative, i.e.
`Gtz.IsCompatibleTriangle` — and a TRIPLE half, the cubic tie leg.  The edge half
carries its own named refutation channel: by
`Gtz.not_gtzWeightedAll_three_of_no_compatibleTriangle` an all-heavy design whose
compatible graph were triangle-free would refute rank-three GTZ outright.

This file closes that channel on the `(7,3)` equal-share stratum — weight `1/7`,
leverage `3`, the stratum every classical `(7,3)` witness inhabits.  The input is
the shipped row law `Gtz.sum_normalizedPairing_sq_uniform_seven`: at that stratum
the six squared correlations at any atom sum to EXACTLY three.  Three
incompatible edges would each cost more than one and already exceed it, so the
incompatible degree is at most two, the compatible degree is at least four out of
six, and two adjacent vertices then share a neighbour by counting on the
five-element common ground set.

The count is sharp in the size.  At `m = 7` the row sum is `3` over six edges and
the common-neighbour count is `3 + 3 - 5 = 1 > 0`.  At `m = 8` the row sum is
`15/4` over seven edges, the degree bound only weakens to three, the ambient set
grows, and the count becomes `3 + 3 - 6 = 0`.  The argument closes at seven and
nowhere above.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `IsEqualShare.heavyExcess_eq_two` — the excess the stratum pins, named once
  instead of inlined.
* `compatibleNeighbourhood`, `incompatibleNeighbourhood` and their `(7,3)`
  equal-share degree bounds `≤ 2` and `4 ≤ ·`.
* `exists_isCompatibleTriangle_of_isEqualShare_sevenThree` — the headline, with
  the `(atomShare = 3/7, leverage = 3)` restatement the `(7,3)` band modules
  consume and the non-vacuity instance at
  `Gtz.sevenThreeBasisTetrapodDesign`.
* `four_ninths_lt_edgeWeight_of_pairMinor_neg` — the edge cost in the tree's own
  `Gtz.edgeWeight` currency: at leverage three an incompatible pair spends more
  than `4/9`.

## NOT PROVED here, and the stratum is NOT settled

Compatibility is NECESSARY for domination and nothing more.  The cubic tie leg
`Gtz.discriminantTie` is untouched, so this does not show the equal-share stratum
of `(7,3)` satisfies `Gtz.GtzWeightedHeavy 7 3`; it removes one named way the
conjecture could have been false there.  The `(6,3)` analogue
`Gtz.exists_dominating_triple_of_isEqualShare` is a full domination statement;
this is the edge instalment of its `(7,3)` counterpart, whose absence
`Gtz/Reduction/WeightFloorWindow.lean` records in prose.

The leverage hypothesis is not decoration.  Scratch report 14 measured exact
rational `(7,3)` designs at uniform WEIGHT but non-uniform leverage carrying
incompatible degrees three, four and five, so the degree bound is false without
it.  That is a measurement, not a theorem here.

Provenance: scratch report 15 (`/tmp/gtz-wf/qe-agent/probe.lean`) supplies the
counting; scratch report 14 (`/tmp/gtz-wf/algebra-angle/final.lean`, Part II,
namespace `GtzPairLadder`) derives the same conclusion independently through the
edge budget `4/3` and the edge cost `4/9` rather than the row sum `3` and the
threshold `1`.  The two conclusions are the identical proposition, so only one is
landed; the edge-cost lemma is the one piece of the second route with no
counterpart in the first, and it is kept because it is the bridge from the
compatibility layer to the `(7,3)` band layer's `edgeWeight` machinery.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.FrameConservation
import Gtz.Design.SignSelectedAggregate
import Gtz.LinAlg.ElliptopeInterval
import Gtz.Quantitative.GoodTripleGraph
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.SevenThreeInvolution
import Gtz.Quantitative.WeightProductFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Finset Matrix

variable {m : ℕ}

/-! ## The excess the stratum pins

The squared reading of compatibility that the counting below charges against is
already shipped as `Gtz.isCompatiblePair_iff_normalizedPairing_sq_le_one`
(`Gtz/LinAlg/ElliptopeInterval.lean`); it is imported, not restated. -/

/-- Every heavy excess on a rank-three equal-share stratum is two. -/
theorem IsEqualShare.heavyExcess_eq_two {D : WeightedDesign m 3} (hequal : IsEqualShare D)
    (atomIndex : Fin m) : heavyExcess D atomIndex = 2 := by
  rw [heavyExcess, hequal.leverage_eq atomIndex]
  norm_num

/-- Every heavy excess on a rank-three equal-share stratum is positive. -/
theorem IsEqualShare.heavyExcess_pos {D : WeightedDesign m 3} (hequal : IsEqualShare D)
    (atomIndex : Fin m) : 0 < heavyExcess D atomIndex := by
  rw [hequal.heavyExcess_eq_two atomIndex]
  norm_num

/-! ## The two neighbourhoods of the compatible graph -/

/-- The atoms compatible with a given one: the neighbourhood of the compatible
graph, with the centre excluded. -/
noncomputable def compatibleNeighbourhood (D : WeightedDesign m 3) (center : Fin m) :
    Finset (Fin m) :=
  open Classical in
  (Finset.univ.erase center).filter (fun other => IsCompatiblePair D center other)

/-- The atoms INCOMPATIBLE with a given one — the edges no triangle can use. -/
noncomputable def incompatibleNeighbourhood (D : WeightedDesign m 3) (center : Fin m) :
    Finset (Fin m) :=
  open Classical in
  (Finset.univ.erase center).filter (fun other => ¬ IsCompatiblePair D center other)

/-- Membership in the compatible neighbourhood names both facts it carries. -/
theorem ne_and_isCompatiblePair_of_mem_compatibleNeighbourhood {D : WeightedDesign m 3}
    {center other : Fin m} (hmember : other ∈ compatibleNeighbourhood D center) :
    other ≠ center ∧ IsCompatiblePair D center other := by
  classical
  rw [compatibleNeighbourhood] at hmember
  obtain ⟨hmemErase, hcompatible⟩ := Finset.mem_filter.mp hmember
  exact ⟨Finset.ne_of_mem_erase hmemErase, hcompatible⟩

/-- The compatible neighbourhood sits inside the other atoms. -/
theorem compatibleNeighbourhood_subset_erase (D : WeightedDesign m 3) (center : Fin m) :
    compatibleNeighbourhood D center ⊆ Finset.univ.erase center := by
  classical
  rw [compatibleNeighbourhood]
  exact Finset.filter_subset _ _

/-! ## The degree bounds at the `(7,3)` equal-share stratum -/

/-- **THE INCOMPATIBLE DEGREE IS AT MOST TWO.**  Each incompatible edge at an atom
of the equal-share `(7,3)` stratum carries squared correlation strictly above one,
and the six edges at that atom carry exactly three in total, so three of them
would already overspend. -/
theorem card_incompatibleNeighbourhood_le_two_of_isEqualShare_sevenThree
    {D : WeightedDesign 7 3} (hequal : IsEqualShare D) (center : Fin 7) :
    (incompatibleNeighbourhood D center).card ≤ 2 := by
  classical
  have hrowLaw : ∑ other ∈ Finset.univ.erase center, normalizedPairing D center other ^ 2 = 3 :=
    sum_normalizedPairing_sq_uniform_seven
      (fun atomIndex => by rw [hequal.weight_eq atomIndex]; norm_num)
      (fun atomIndex => by rw [hequal.leverage_eq atomIndex]; norm_num) center
  by_contra hlarge
  obtain ⟨heavySample, hsampleSubset, hsampleCard⟩ :=
    Finset.exists_subset_card_eq (Nat.succ_le_of_lt (Nat.lt_of_not_le hlarge))
  obtain ⟨atomOne, atomTwo, atomThree, honeTwo, honeThree, htwoThree, hsampleEq⟩ :=
    Finset.card_eq_three.mp hsampleCard
  have hsampleInErase : heavySample ⊆ Finset.univ.erase center := by
    refine hsampleSubset.trans ?_
    rw [incompatibleNeighbourhood]
    exact Finset.filter_subset _ _
  have hoverspend : ∀ other ∈ heavySample, 1 < normalizedPairing D center other ^ 2 := by
    intro other hother
    have hmember := hsampleSubset hother
    rw [incompatibleNeighbourhood] at hmember
    have hincompatible := (Finset.mem_filter.mp hmember).2
    by_contra hwithin
    exact hincompatible ((isCompatiblePair_iff_normalizedPairing_sq_le_one D
      (hequal.heavyExcess_pos center) (hequal.heavyExcess_pos other)).mpr (not_lt.mp hwithin))
  have hone := hoverspend atomOne (by rw [hsampleEq]; simp)
  have htwo := hoverspend atomTwo (by rw [hsampleEq]; simp)
  have hthree := hoverspend atomThree (by rw [hsampleEq]; simp)
  have hsampleSum : ∑ other ∈ heavySample, normalizedPairing D center other ^ 2
      = normalizedPairing D center atomOne ^ 2 + normalizedPairing D center atomTwo ^ 2
        + normalizedPairing D center atomThree ^ 2 := by
    rw [hsampleEq, Finset.sum_insert (by simp [honeTwo, honeThree]),
      Finset.sum_insert (by simp [htwoThree]), Finset.sum_singleton]
    ring
  have hpartial : ∑ other ∈ heavySample, normalizedPairing D center other ^ 2
      ≤ ∑ other ∈ Finset.univ.erase center, normalizedPairing D center other ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsampleInErase
      (fun other _ _ => sq_nonneg (normalizedPairing D center other))
  rw [hsampleSum, hrowLaw] at hpartial
  linarith

/-- **THE COMPATIBLE MINIMUM DEGREE.**  Every atom of the equal-share `(7,3)`
stratum is compatible with at least four of the other six. -/
theorem four_le_card_compatibleNeighbourhood_of_isEqualShare_sevenThree
    {D : WeightedDesign 7 3} (hequal : IsEqualShare D) (center : Fin 7) :
    4 ≤ (compatibleNeighbourhood D center).card := by
  classical
  have hcardErase : (Finset.univ.erase center).card = 6 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ center), Finset.card_univ, Fintype.card_fin]
  have hsplit : (compatibleNeighbourhood D center).card
        + (incompatibleNeighbourhood D center).card
      = (Finset.univ.erase center).card := by
    rw [compatibleNeighbourhood, incompatibleNeighbourhood]
    exact Finset.card_filter_add_card_filter_not _
  have hincompatible := card_incompatibleNeighbourhood_le_two_of_isEqualShare_sevenThree hequal
    center
  rw [hcardErase] at hsplit
  omega

/-! ## The triangle -/

/-- **A COMPATIBLE TRIANGLE EXISTS ON THE `(7,3)` EQUAL-SHARE STRATUM.**  Three
distinct atoms whose three `2 x 2` gap minors are all nonnegative.  Equivalently,
the EDGE half of `Gtz.dominates_triple_iff_isElliptopeGoodTriangle` is
dischargeable on the whole stratum, and the refutation channel
`Gtz.not_gtzWeightedAll_three_of_no_compatibleTriangle` is closed there.  What
survives on the stratum is the single cubic tie leg. -/
theorem exists_isCompatibleTriangle_of_isEqualShare_sevenThree {D : WeightedDesign 7 3}
    (hequal : IsEqualShare D) :
    ∃ atomFirst atomSecond atomThird : Fin 7,
      atomFirst ≠ atomSecond ∧ atomFirst ≠ atomThird ∧ atomSecond ≠ atomThird
        ∧ IsCompatibleTriangle D atomFirst atomSecond atomThird := by
  classical
  have hdegree : ∀ center : Fin 7, 4 ≤ (compatibleNeighbourhood D center).card :=
    fun center => four_le_card_compatibleNeighbourhood_of_isEqualShare_sevenThree hequal center
  obtain ⟨pivotPartner, hpartnerMem⟩ : (compatibleNeighbourhood D 0).Nonempty := by
    rw [← Finset.card_pos]
    have := hdegree 0
    omega
  obtain ⟨hpartnerNe, hpartnerCompat⟩ :=
    ne_and_isCompatiblePair_of_mem_compatibleNeighbourhood hpartnerMem
  set leftSide : Finset (Fin 7) := (compatibleNeighbourhood D 0).erase pivotPartner
    with hleftDef
  set rightSide : Finset (Fin 7) := (compatibleNeighbourhood D pivotPartner).erase 0
    with hrightDef
  set commonGround : Finset (Fin 7) := (Finset.univ.erase (0 : Fin 7)).erase pivotPartner
    with hcommonDef
  have hpartnerInErase : pivotPartner ∈ Finset.univ.erase (0 : Fin 7) :=
    Finset.mem_erase.mpr ⟨hpartnerNe, Finset.mem_univ pivotPartner⟩
  have hcommonCard : commonGround.card = 5 := by
    rw [hcommonDef, Finset.card_erase_of_mem hpartnerInErase,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin 7)), Finset.card_univ,
      Fintype.card_fin]
  have hleftCard : 3 ≤ leftSide.card := by
    rw [hleftDef, Finset.card_erase_of_mem hpartnerMem]
    have := hdegree 0
    omega
  have hrightCard : 3 ≤ rightSide.card := by
    rw [hrightDef]
    by_cases hzeroMem : (0 : Fin 7) ∈ compatibleNeighbourhood D pivotPartner
    · rw [Finset.card_erase_of_mem hzeroMem]
      have := hdegree pivotPartner
      omega
    · rw [Finset.erase_eq_of_notMem hzeroMem]
      exact le_trans (by norm_num) (hdegree pivotPartner)
  have hleftSub : leftSide ⊆ commonGround := by
    intro element hmember
    rw [hleftDef] at hmember
    have hnePartner := Finset.ne_of_mem_erase hmember
    have hinNeighbourhood := Finset.mem_of_mem_erase hmember
    have hneZero := (ne_and_isCompatiblePair_of_mem_compatibleNeighbourhood hinNeighbourhood).1
    rw [hcommonDef]
    exact Finset.mem_erase.mpr ⟨hnePartner,
      Finset.mem_erase.mpr ⟨hneZero, Finset.mem_univ element⟩⟩
  have hrightSub : rightSide ⊆ commonGround := by
    intro element hmember
    rw [hrightDef] at hmember
    have hneZero := Finset.ne_of_mem_erase hmember
    have hinNeighbourhood := Finset.mem_of_mem_erase hmember
    have hnePartner := (ne_and_isCompatiblePair_of_mem_compatibleNeighbourhood hinNeighbourhood).1
    rw [hcommonDef]
    exact Finset.mem_erase.mpr ⟨hnePartner,
      Finset.mem_erase.mpr ⟨hneZero, Finset.mem_univ element⟩⟩
  have hunionCard : (leftSide ∪ rightSide).card ≤ 5 := by
    rw [← hcommonCard]
    exact Finset.card_le_card (Finset.union_subset hleftSub hrightSub)
  have hunionInter := Finset.card_union_add_card_inter leftSide rightSide
  obtain ⟨apex, hapexMem⟩ : (leftSide ∩ rightSide).Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hapexLeft := (Finset.mem_inter.mp hapexMem).1
  have hapexRight := (Finset.mem_inter.mp hapexMem).2
  rw [hleftDef] at hapexLeft
  rw [hrightDef] at hapexRight
  have hapexNePartner : apex ≠ pivotPartner := Finset.ne_of_mem_erase hapexLeft
  have hapexNeZero : apex ≠ 0 := Finset.ne_of_mem_erase hapexRight
  have hzeroApex : IsCompatiblePair D 0 apex :=
    (ne_and_isCompatiblePair_of_mem_compatibleNeighbourhood
      (Finset.mem_of_mem_erase hapexLeft)).2
  have hpartnerApex : IsCompatiblePair D pivotPartner apex :=
    (ne_and_isCompatiblePair_of_mem_compatibleNeighbourhood
      (Finset.mem_of_mem_erase hapexRight)).2
  exact ⟨0, pivotPartner, apex, hpartnerNe.symm, hapexNeZero.symm, hapexNePartner.symm,
    hpartnerCompat, hzeroApex, hpartnerApex⟩

/-- The equal-share stratum, recognised from the pair of hypotheses the `(7,3)`
band modules actually carry: uniform share `3/7` and leverage three force weight
`1/7`, which with the leverage is `Gtz.IsEqualShare`. -/
theorem isEqualShare_of_atomShare_of_leverage_sevenThree {D : WeightedDesign 7 3}
    (huniform : ∀ atomIndex : Fin 7, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex : Fin 7, leverageOf (D.atom atomIndex) = 3) :
    IsEqualShare D where
  weight_eq := fun atomIndex => by
    have hshare := huniform atomIndex
    rw [atomShare, hleverage atomIndex] at hshare
    norm_num
    linarith
  leverage_eq := fun atomIndex => by
    rw [hleverage atomIndex]
    norm_num

/-- The headline in the hypothesis shape the `(7,3)` band modules are written in. -/
theorem exists_isCompatibleTriangle_of_uniformShare_sevenThree {D : WeightedDesign 7 3}
    (huniform : ∀ atomIndex : Fin 7, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex : Fin 7, leverageOf (D.atom atomIndex) = 3) :
    ∃ atomFirst atomSecond atomThird : Fin 7,
      atomFirst ≠ atomSecond ∧ atomFirst ≠ atomThird ∧ atomSecond ≠ atomThird
        ∧ IsCompatibleTriangle D atomFirst atomSecond atomThird :=
  exists_isCompatibleTriangle_of_isEqualShare_sevenThree
    (isEqualShare_of_atomShare_of_leverage_sevenThree huniform hleverage)

/-- **NON-VACUITY.**  The shipped `(7,3)` equal-share witness — three axis atoms
and a tetrapod, at uniform weight `1/7` — satisfies the hypothesis, so the
headline is a statement about an inhabited stratum. -/
theorem exists_isCompatibleTriangle_sevenThreeBasisTetrapodDesign :
    ∃ atomFirst atomSecond atomThird : Fin 7,
      atomFirst ≠ atomSecond ∧ atomFirst ≠ atomThird ∧ atomSecond ≠ atomThird
        ∧ IsCompatibleTriangle sevenThreeBasisTetrapodDesign atomFirst atomSecond atomThird :=
  exists_isCompatibleTriangle_of_isEqualShare_sevenThree
    isEqualShare_sevenThreeBasisTetrapodDesign

/-! ## The edge cost, in the band layer's currency -/

/-- **THE EDGE COST.**  At uniform leverage three an incompatible pair spends
strictly more than `4/9` of the squared-correlation budget: the pair minor there
is `4 - 9 γ²`, so a negative minor forces `4/9 < γ² = Gtz.edgeWeight`.

Stated in `Gtz.edgeWeight` rather than in `Gtz.directionGram` squared — the two
are definitionally the same — because the whole `(7,3)` band layer is written in
`edgeWeight`, and this is the bridge that lets the compatibility layer charge
against it.  Independent second route to the degree bound above: six edges at a
budget of `4/3` admit at most two costing more than `4/9` each. -/
theorem four_ninths_lt_edgeWeight_of_pairMinor_neg {D : WeightedDesign m 3}
    (hleverage : ∀ atomIndex : Fin m, leverageOf (D.atom atomIndex) = 3)
    {firstIndex secondIndex : Fin m} (hincompatible : pairMinor D firstIndex secondIndex < 0) :
    4 / 9 < edgeWeight D firstIndex secondIndex := by
  have hscaled := directionGram_eq_scaled_atomPairing D firstIndex secondIndex
  rw [hleverage firstIndex, hleverage secondIndex] at hscaled
  have hrootSquare : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hrootInverse : (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = 1 / 3 := by
    rw [← mul_inv, hrootSquare]
    norm_num
  rw [hrootInverse] at hscaled
  have hpairing : atomPairing D firstIndex secondIndex
      = 3 * directionGram D firstIndex secondIndex := by
    simp only [atomPairing]
    rw [hscaled]
    ring
  have hexcess : ∀ probeIndex : Fin m, heavyExcess D probeIndex = 2 := by
    intro probeIndex
    rw [heavyExcess, hleverage probeIndex]
    norm_num
  simp only [pairMinor, hexcess, hpairing] at hincompatible
  rw [edgeWeight]
  nlinarith [hincompatible]

end Gtz

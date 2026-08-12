import Gtz.Wave.SharedSupportPairTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The two-shared-pair kill — two shared supports exhaust the trace budget

Four basis slots that split into two pairs, each pair on one shared
support that no other basis column touches, die against the trace budget:
each pair trace reads two shifted weights, the four atoms are distinct,
and the total gives `4 * value + (four weights) = 2` with the weights
summing to at most one — against the negative value.  This kill closes
the two-triple-edge representative of the dense census branch, and the
independent double edges of the mixed representatives.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.false_of_two_shared_support_pairs` — **THE KILL.**

## Vacuity

The statement takes the negative value as a hypothesis, and a crux
supplies it.  It is vacuous if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE TWO-SHARED-PAIR KILL.**  Two disjoint slot pairs, each on one
shared support that no other basis column touches, exhaust the trace
budget two against the negative value. -/
theorem false_of_two_shared_support_pairs
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hvalueNeg : value < 0)
    (basisLabel : Fin 4 → activeIndex)
    {L : Matrix (Fin 4) (Fin size) ℝ}
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (htrace : Matrix.trace M = 2)
    {slotA slotB slotC slotD : Fin 4}
    (hAB : slotA ≠ slotB) (hCD : slotC ≠ slotD)
    (hAC : slotA ≠ slotC) (hAD : slotA ≠ slotD)
    (hBC : slotB ≠ slotC) (hBD : slotB ≠ slotD)
    (hmemA : basisLabel slotA ∈ activeSet)
    (hmemB : basisLabel slotB ∈ activeSet)
    (hmemC : basisLabel slotC ∈ activeSet)
    (hmemD : basisLabel slotD ∈ activeSet)
    (hsharedAB : datumTightSupport tightDir (basisLabel slotA)
      = datumTightSupport tightDir (basisLabel slotB))
    (hsharedCD : datumTightSupport tightDir (basisLabel slotC)
      = datumTightSupport tightDir (basisLabel slotD))
    (hnonemptyAB : (datumTightSupport tightDir (basisLabel slotA)).Nonempty)
    (hnonemptyCD : (datumTightSupport tightDir (basisLabel slotC)).Nonempty)
    (hcarriersAB : ∀ atomIndex : Fin size,
      tightDir (basisLabel slotA) atomIndex ≠ 0 →
      ∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
        tightDir (basisLabel columnIndex) atomIndex = 0)
    (hcarriersCD : ∀ atomIndex : Fin size,
      tightDir (basisLabel slotC) atomIndex ≠ 0 →
      ∀ columnIndex, columnIndex ≠ slotC → columnIndex ≠ slotD →
        tightDir (basisLabel columnIndex) atomIndex = 0) :
    False := by
  classical
  obtain ⟨firstAtom, hfirstMem, secondAtom, hsecondMem, hfsNe, hpairAB⟩ :=
    pair_trace_eq_of_shared_support hdata basisLabel hleft hrepresentation hAB
      hmemA hmemB hsharedAB hnonemptyAB hcarriersAB
  obtain ⟨thirdAtom, hthirdMem, fourthAtom, hfourthMem, htfNe, hpairCD⟩ :=
    pair_trace_eq_of_shared_support hdata basisLabel hleft hrepresentation hCD
      hmemC hmemD hsharedCD hnonemptyCD hcarriersCD
  have hcross : ∀ leftAtom ∈ datumTightSupport tightDir (basisLabel slotA),
      ∀ rightAtom ∈ datumTightSupport tightDir (basisLabel slotC),
        leftAtom ≠ rightAtom := by
    intro leftAtom hleftMem rightAtom hrightMem hcontra
    have hAzero := hcarriersCD rightAtom (mem_datumTightSupport.mp hrightMem)
      slotA hAC hAD
    rw [← hcontra] at hAzero
    exact (mem_datumTightSupport.mp hleftMem) hAzero
  have h13 : firstAtom ≠ thirdAtom := hcross firstAtom hfirstMem thirdAtom hthirdMem
  have h14 : firstAtom ≠ fourthAtom := hcross firstAtom hfirstMem fourthAtom hfourthMem
  have h23 : secondAtom ≠ thirdAtom := hcross secondAtom hsecondMem thirdAtom hthirdMem
  have h24 : secondAtom ≠ fourthAtom :=
    hcross secondAtom hsecondMem fourthAtom hfourthMem
  have hBnotMem : slotB ∉ ({slotC, slotD} : Finset (Fin 4)) := by
    simp [hBC, hBD]
  have hAnotMem : slotA ∉ ({slotB, slotC, slotD} : Finset (Fin 4)) := by
    simp [hAB, hAC, hAD]
  have hCnotMem : slotC ∉ ({slotD} : Finset (Fin 4)) := by
    simp [hCD]
  have hslotCard : ({slotA, slotB, slotC, slotD} : Finset (Fin 4)).card = 4 := by
    rw [Finset.card_insert_of_notMem hAnotMem,
      Finset.card_insert_of_notMem hBnotMem,
      Finset.card_insert_of_notMem hCnotMem, Finset.card_singleton]
  have huniv : ({slotA, slotB, slotC, slotD} : Finset (Fin 4)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, Fintype.card_fin, hslotCard]
  have htraceSplit : Matrix.trace M
      = M slotA slotA + (M slotB slotB + (M slotC slotC + M slotD slotD)) := by
    have htraceSum : Matrix.trace M = ∑ slotIndex : Fin 4, M slotIndex slotIndex := rfl
    rw [htraceSum, ← huniv, Finset.sum_insert hAnotMem, Finset.sum_insert hBnotMem,
      Finset.sum_insert hCnotMem, Finset.sum_singleton]
  have hsecondNotMem : secondAtom ∉ ({thirdAtom, fourthAtom} : Finset (Fin size)) := by
    simp [h23, h24]
  have hfirstNotMem : firstAtom
      ∉ ({secondAtom, thirdAtom, fourthAtom} : Finset (Fin size)) := by
    simp [hfsNe, h13, h14]
  have hthirdNotMem : thirdAtom ∉ ({fourthAtom} : Finset (Fin size)) := by
    simp [htfNe]
  have hweightExpand : ∑ atomIndex ∈
      ({firstAtom, secondAtom, thirdAtom, fourthAtom} : Finset (Fin size)),
        weight atomIndex
      = weight firstAtom + (weight secondAtom
          + (weight thirdAtom + weight fourthAtom)) := by
    rw [Finset.sum_insert hfirstNotMem, Finset.sum_insert hsecondNotMem,
      Finset.sum_insert hthirdNotMem, Finset.sum_singleton]
  have hweightBound : ∑ atomIndex ∈
      ({firstAtom, secondAtom, thirdAtom, fourthAtom} : Finset (Fin size)),
        weight atomIndex ≤ 1 := by
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ
        ({firstAtom, secondAtom, thirdAtom, fourthAtom} : Finset (Fin size)))
      (fun atomIndex _ _ => le_of_lt (hdata.weight_pos atomIndex))
    rw [hdata.weight_sum_one] at hle
    exact hle
  rw [hweightExpand] at hweightBound
  rw [htraceSplit] at htrace
  linarith

end Gtz

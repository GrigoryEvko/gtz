import Gtz.Wave.AssemblySupportCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The tight-direction basis — labels for the coefficient coordinates

The exact span law puts `range Ξ` equal to the span of the positive tight
directions.  A finite spanning set contains a basis of its span, so every
stationary datum carries a POSITIVE-LABEL basis: `r` labels of the positive
support whose directions are independent and span `range Ξ`.  This is the
basis `B` of the campaign's coefficient coordinates, with the labels kept —
the sparse side of the two-coordinate dictionary reads supports through the
labels, and a vector-only basis would lose them.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.exists_tightBasisSet_of_isChartStationaryData` — the vector form: a
  finset of tight directions, inside the positive image, of size `r`, that
  spans `range Ξ` and is independent.
* `Gtz.exists_basisLabels_of_isChartStationaryData` — **THE LABELLED BASIS.**
  A finset of POSITIVE LABELS of size `r` whose directions are pairwise
  distinct, independent, and span `range Ξ`.
* `Gtz.SixThreeCrux.exists_basisLabels_card_le_span` — the crux packaging: a
  support-minimal datum together with a labelled basis of its assembly range,
  with the basis size read off the rank survivors.

## Vacuity

The crux corollary is vacuous if `Gtz.GtzWeighted 6 3` holds.  The generic
theorems hold at every stationary datum.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE VECTOR BASIS.**  Inside the positive tight image sits a finset of
size `r = rank Ξ` that spans `range Ξ` and is independent. -/
theorem exists_tightBasisSet_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    ∃ basisSet : Finset (Fin size → ℝ),
      (↑basisSet : Set (Fin size → ℝ))
          ⊆ ↑((positiveActiveSet activeSet activeWeight).image tightDir)
        ∧ basisSet.card = Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            (chartMultiplierAssembly activeSet activeWeight tightDir)))
        ∧ Submodule.span ℝ (↑basisSet : Set (Fin size → ℝ))
            = LinearMap.range (Matrix.toLin'
                (chartMultiplierAssembly activeSet activeWeight tightDir))
        ∧ LinearIndepOn ℝ id (↑basisSet : Set (Fin size → ℝ)) := by
  classical
  obtain ⟨basisSet, hsubset, hcard, hspan, hindep⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℝ
      (↑((positiveActiveSet activeSet activeWeight).image tightDir) : Set (Fin size → ℝ))
  have hspanLaw := range_multiplier_eq_span_positive_tightDir hdata
  refine ⟨basisSet, hsubset, ?_, ?_, hindep⟩
  · rw [hcard, hspanLaw]
  · rw [hspan, hspanLaw]

/-- **THE LABELLED BASIS.**  A finset of `r` positive labels whose tight
directions are pairwise distinct, independent, and span `range Ξ`.  The label
count equals the direction count, so no two chosen labels share a
direction. -/
theorem exists_basisLabels_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    ∃ basisLabels : Finset activeIndex,
      basisLabels ⊆ positiveActiveSet activeSet activeWeight
        ∧ basisLabels.card = Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            (chartMultiplierAssembly activeSet activeWeight tightDir)))
        ∧ (basisLabels.image tightDir).card = basisLabels.card
        ∧ Submodule.span ℝ (↑(basisLabels.image tightDir) : Set (Fin size → ℝ))
            = LinearMap.range (Matrix.toLin'
                (chartMultiplierAssembly activeSet activeWeight tightDir))
        ∧ LinearIndepOn ℝ id (↑(basisLabels.image tightDir) : Set (Fin size → ℝ)) := by
  classical
  obtain ⟨basisSet, hsubset, hcard, hspan, hindep⟩ :=
    exists_tightBasisSet_of_isChartStationaryData hdata
  have hchoose : ∀ vec ∈ basisSet, ∃ label,
      label ∈ positiveActiveSet activeSet activeWeight ∧ tightDir label = vec := by
    intro vec hvec
    have hmem := hsubset hvec
    simpa only [Finset.coe_image, Set.mem_image, Finset.mem_coe] using hmem
  choose labelOf hlabelMem hlabelEq using hchoose
  obtain ⟨basisLabels, hbasisLabelsDef⟩ :
      ∃ basisLabels : Finset activeIndex,
        basisLabels = basisSet.attach.image fun vec => labelOf vec.1 vec.2 := ⟨_, rfl⟩
  have himageEq : basisLabels.image tightDir = basisSet := by
    rw [hbasisLabelsDef, Finset.image_image]
    apply Finset.Subset.antisymm
    · intro vec hvec
      obtain ⟨vecAttach, -, rfl⟩ := Finset.mem_image.mp hvec
      simp only [Function.comp_apply, hlabelEq vecAttach.1 vecAttach.2]
      exact vecAttach.2
    · intro vec hvec
      refine Finset.mem_image.mpr ⟨⟨vec, hvec⟩, Finset.mem_attach _ _, ?_⟩
      simp only [Function.comp_apply, hlabelEq vec hvec]
  have hlabelCard : basisLabels.card = basisSet.card := by
    rw [hbasisLabelsDef]
    rw [Finset.card_image_of_injOn, Finset.card_attach]
    intro firstVec _ secondVec _ hlabelCollide
    have hlabelCollide' : labelOf firstVec.1 firstVec.2 = labelOf secondVec.1 secondVec.2 :=
      hlabelCollide
    have hfirst := hlabelEq firstVec.1 firstVec.2
    have hsecond := hlabelEq secondVec.1 secondVec.2
    have hvecEq : firstVec.1 = secondVec.1 := by
      rw [← hfirst, ← hsecond, hlabelCollide']
    exact Subtype.ext hvecEq
  have hsubsetLabels : basisLabels ⊆ positiveActiveSet activeSet activeWeight := by
    rw [hbasisLabelsDef]
    intro label hlabel
    obtain ⟨vecAttach, -, rfl⟩ := Finset.mem_image.mp hlabel
    exact hlabelMem vecAttach.1 vecAttach.2
  refine ⟨basisLabels, hsubsetLabels, ?_, ?_, ?_, ?_⟩
  · rw [hlabelCard, hcard]
  · rw [himageEq, hlabelCard]
  · rw [himageEq, hspan]
  · rw [himageEq]
    exact hindep

/-- **THE CRUX PACKAGING.**  A `(6,3)` counterexample carries a support-minimal
datum together with a labelled basis of its assembly range, and the basis size
is the assembly rank — four, five or six by the survivor list. -/
theorem SixThreeCrux.exists_basisLabels_card_le_span
    (crux : SixThreeCrux) :
    ∃ (multiplier : Finset (Fin 6) → ℝ) (selection : Finset (Fin 6) → (Fin 6 → ℝ))
      (basisLabels : Finset (Finset (Fin 6))),
      IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design))
        (chartArgmaxFamily (chartPointOfDesign crux.design))
        (id : Finset (Fin 6) → Finset (Fin 6)) multiplier selection
      ∧ LinearIndependent ℝ
          (fun index : {index // index ∈ positiveActiveSet
            (chartArgmaxFamily (chartPointOfDesign crux.design)) multiplier} =>
            atomMatrix (selection index.1))
      ∧ basisLabels ⊆ positiveActiveSet
          (chartArgmaxFamily (chartPointOfDesign crux.design)) multiplier
      ∧ Submodule.span ℝ (↑(basisLabels.image selection) : Set (Fin 6 → ℝ))
          = LinearMap.range (Matrix.toLin'
              (chartMultiplierAssembly (chartArgmaxFamily (chartPointOfDesign crux.design))
                multiplier selection))
      ∧ LinearIndepOn ℝ id (↑(basisLabels.image selection) : Set (Fin 6 → ℝ))
      ∧ (basisLabels.card = 4 ∨ basisLabels.card = 5 ∨ basisLabels.card = 6) := by
  obtain ⟨multiplier, selection, hdata, hindependent⟩ :=
    crux.exists_multiplier_isChartStationaryData_independent_positive_support
  obtain ⟨basisLabels, hsubsetLabels, hcardLabels, -, hspanLabels, hindepLabels⟩ :=
    exists_basisLabels_of_isChartStationaryData hdata
  refine ⟨multiplier, selection, basisLabels, hdata, hindependent, hsubsetLabels,
    hspanLabels, hindepLabels, ?_⟩
  rcases crux.finrank_range_multiplier_eq_four_or_five_or_six hdata with
    hrank | hrank | hrank
  · exact Or.inl (by rw [hcardLabels, hrank])
  · exact Or.inr (Or.inl (by rw [hcardLabels, hrank]))
  · exact Or.inr (Or.inr (by rw [hcardLabels, hrank]))

end Gtz

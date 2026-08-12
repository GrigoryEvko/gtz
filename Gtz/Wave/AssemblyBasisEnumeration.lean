import Gtz.Wave.AssemblyCoefficientTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The enumerated basis — the `Fin r` family the coefficient layer consumes

`Gtz.Wave.AssemblyBasisSelection` returns the basis as a FINSET of labels,
and the coefficient layer indexes its columns by `Fin r`.  This file is the
bridge: every stationary datum carries an injective family
`basisLabel : Fin r → activeIndex` of positive labels whose directions are
independent and span `range Ξ` — with `r` LITERALLY the assembly rank, so the
coefficient theorems apply with no cast at the call site.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.exists_enumerated_basis_of_isChartStationaryData` — **THE ENUMERATED
  BASIS.**  Positive labels, independent directions, exact span, indexed by
  the assembly rank.

## Vacuity

Nothing here quantifies over a crux.  The statement holds at every stationary
datum.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE ENUMERATED BASIS.**  Every stationary datum carries an injective
`Fin r`-indexed family of positive labels whose tight directions are
independent and span the assembly's range, with `r` the assembly rank. -/
theorem exists_enumerated_basis_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    ∃ basisLabel : Fin (Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir)))) → activeIndex,
      Function.Injective basisLabel
        ∧ (∀ columnIndex, basisLabel columnIndex
            ∈ positiveActiveSet activeSet activeWeight)
        ∧ LinearIndependent ℝ (fun columnIndex => tightDir (basisLabel columnIndex))
        ∧ Submodule.span ℝ (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
            = LinearMap.range (Matrix.toLin'
                (chartMultiplierAssembly activeSet activeWeight tightDir)) := by
  classical
  obtain ⟨basisLabels, hsubset, hcard, himageCard, hspan, hindep⟩ :=
    exists_basisLabels_of_isChartStationaryData hdata
  have hinjOn : Set.InjOn tightDir ↑basisLabels := Finset.card_image_iff.mp himageCard
  obtain ⟨basisLabel, hbasisLabelDef⟩ :
      ∃ basisLabel : Fin (Module.finrank ℝ (LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))) → activeIndex,
        basisLabel = fun columnIndex =>
          (basisLabels.equivFin.symm (Fin.cast hcard.symm columnIndex)).1 := ⟨_, rfl⟩
  have hmemLabels : ∀ columnIndex, basisLabel columnIndex ∈ basisLabels := by
    intro columnIndex
    rw [hbasisLabelDef]
    exact (basisLabels.equivFin.symm (Fin.cast hcard.symm columnIndex)).2
  have hinjective : Function.Injective basisLabel := by
    intro firstIndex secondIndex hcollide
    rw [hbasisLabelDef] at hcollide
    have hsubtypeEq := Subtype.ext hcollide
    have hequivEq := basisLabels.equivFin.symm.injective hsubtypeEq
    exact Fin.cast_injective hcard.symm hequivEq
  refine ⟨basisLabel, hinjective, fun columnIndex => hsubset (hmemLabels columnIndex),
    ?_, ?_⟩
  · -- independence, through the image subtype
    have hmemImage : ∀ columnIndex, tightDir (basisLabel columnIndex)
        ∈ (↑(basisLabels.image tightDir) : Set (Fin size → ℝ)) := by
      intro columnIndex
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨basisLabel columnIndex, hmemLabels columnIndex, rfl⟩
    obtain ⟨intoImage, hintoImageDef⟩ :
        ∃ intoImage : Fin (Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            (chartMultiplierAssembly activeSet activeWeight tightDir))))
          → (↑(basisLabels.image tightDir) : Set (Fin size → ℝ)),
          intoImage = fun columnIndex =>
            ⟨tightDir (basisLabel columnIndex), hmemImage columnIndex⟩ := ⟨_, rfl⟩
    have hintoInjective : Function.Injective intoImage := by
      intro firstIndex secondIndex hcollide
      rw [hintoImageDef] at hcollide
      have hvecEq : tightDir (basisLabel firstIndex) = tightDir (basisLabel secondIndex) :=
        congrArg Subtype.val hcollide
      have hlabelEq := hinjOn (hmemLabels firstIndex) (hmemLabels secondIndex) hvecEq
      exact hinjective hlabelEq
    have hcomposed := hindep.comp intoImage hintoInjective
    have hfamilyEq : (fun columnIndex => tightDir (basisLabel columnIndex))
        = (fun vec : (↑(basisLabels.image tightDir) : Set (Fin size → ℝ)) => (vec : Fin size → ℝ))
          ∘ intoImage := by
      funext columnIndex
      rw [hintoImageDef]
      rfl
    rw [hfamilyEq]
    exact hcomposed
  · -- span, through the image set
    have hrangeEq : (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
        = (↑(basisLabels.image tightDir) : Set (Fin size → ℝ)) := by
      apply Set.eq_of_subset_of_subset
      · rintro vec ⟨columnIndex, rfl⟩
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
        exact ⟨basisLabel columnIndex, hmemLabels columnIndex, rfl⟩
      · intro vec hvec
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hvec
        obtain ⟨label, hlabelMem, rfl⟩ := hvec
        refine ⟨Fin.cast hcard (basisLabels.equivFin ⟨label, hlabelMem⟩), ?_⟩
        rw [hbasisLabelDef]
        show tightDir ((basisLabels.equivFin.symm (Fin.cast hcard.symm
            (Fin.cast hcard (basisLabels.equivFin ⟨label, hlabelMem⟩)))) : activeIndex)
          = tightDir label
        rw [show Fin.cast hcard.symm (Fin.cast hcard (basisLabels.equivFin ⟨label, hlabelMem⟩))
            = basisLabels.equivFin ⟨label, hlabelMem⟩ from rfl]
        rw [Equiv.symm_apply_apply]

    rw [hrangeEq]
    exact hspan

end Gtz

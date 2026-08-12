import Gtz.Wave.PrivateSlotExtraction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The pinned dispatch — branch two of the census carries its diagonal pin

The census dispatch splits the rank-four crux data into three branches.
Branch two supplies a multiplicity-one atom, the extraction turns the atom
into a private slot, and the diagonal pin reads the coefficient matrix at
that slot.  This file composes the three steps into one dispatch, and it
adds the kernel-free positivity of the Gram diagonal together with the
private square law `q_s(y)^2 * H_ss = 1/size`.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.posSemidef_diagonal_pos_of_kernel_free` — a positive semidefinite
  matrix with a trivial kernel has a positive diagonal.
* `Gtz.private_atom_square_gram_eq_inv_size` — **THE PRIVATE SQUARE LAW.**
  At a private atom, the direction square times the Gram diagonal reads the
  constant assembly diagonal.
* `Gtz.SixThreeCrux.exists_rankFour_pinned_dispatch` — **THE PINNED
  DISPATCH.**  The census dispatch with branch two upgraded: the private
  slot, the private atom, and the pin `M_ss = value + weight`.

## Vacuity

The crux statement is vacuous if `Gtz.GtzWeighted 6 3` holds.  The matrix
statements are unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- A positive semidefinite matrix with a trivial kernel has a positive
diagonal.  A zero diagonal entry forces the axis vector into the kernel. -/
theorem posSemidef_diagonal_pos_of_kernel_free
    {H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hpsd : H.PosSemidef)
    (hker : ∀ coeffVec : Fin basisCount → ℝ, H *ᵥ coeffVec = 0 → coeffVec = 0)
    (slotIndex : Fin basisCount) :
    0 < H slotIndex slotIndex := by
  classical
  have hstar : star (Pi.single slotIndex 1 : Fin basisCount → ℝ)
      = Pi.single slotIndex 1 := by
    ext otherIndex
    simp
  have hdot : Pi.single slotIndex (1 : ℝ) ⬝ᵥ (H *ᵥ Pi.single slotIndex 1)
      = H slotIndex slotIndex := by
    rw [single_dotProduct, one_mul, Matrix.mulVec_single_one]
    simp [Matrix.col]
  have hquad := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2
    (Pi.single slotIndex (1 : ℝ))
  rw [hstar, hdot] at hquad
  rcases hquad.lt_or_eq with hpos | hzero
  · exact hpos
  exfalso
  have hzeroDot : star (Pi.single slotIndex (1 : ℝ))
      ⬝ᵥ (H *ᵥ Pi.single slotIndex 1) = 0 := by
    rw [hstar, hdot, ← hzero]
  have hcolZero : H *ᵥ Pi.single slotIndex (1 : ℝ) = 0 :=
    (hpsd.dotProduct_mulVec_zero_iff (Pi.single slotIndex 1)).mp hzeroDot
  have haxis := hker _ hcolZero
  have hone : (Pi.single slotIndex 1 : Fin basisCount → ℝ) slotIndex = 1 :=
    Pi.single_eq_same _ _
  rw [haxis] at hone
  simp at hone

/-- **THE PRIVATE SQUARE LAW.**  At a private atom, the assembly diagonal
collapses to the single surviving coordinate: the direction square times
the Gram diagonal equals the constant `1/size`. -/
theorem private_atom_square_gram_eq_inv_size
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    {privateSlot : Fin basisCount} {privateAtom : Fin size}
    (hprivate : ∀ columnIndex, columnIndex ≠ privateSlot →
      tightDir (basisLabel columnIndex) privateAtom = 0) :
    tightDir (basisLabel privateSlot) privateAtom
        * tightDir (basisLabel privateSlot) privateAtom
        * H privateSlot privateSlot
      = ((size : ℝ))⁻¹ :=
  (conjugated_diagonal_eq_of_private_atom basisLabel hHform hprivate).symm.trans
    (hdata.assembly_diagonal privateAtom)

/-- **THE PINNED DISPATCH.**  Every rank-four crux datum carries the normal
form together with the support trichotomy, and branch two carries its pin:
a private slot whose coefficient diagonal reads `value + weight` at the
private atom. -/
theorem SixThreeCrux.exists_rankFour_pinned_dispatch
    (crux : SixThreeCrux)
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (hrankFour : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir))) = 4) :
    ∃ (reducedWeight : activeIndex → ℝ)
      (basisLabel : Fin 4 → activeIndex)
      (L : Matrix (Fin 4) (Fin 6) ℝ) (M H : Matrix (Fin 4) (Fin 4) ℝ),
      IsChartStationaryData 3
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design))
          activeSet activeSubset reducedWeight tightDir
        ∧ chartMultiplierAssembly activeSet reducedWeight tightDir
            = chartMultiplierAssembly activeSet activeWeight tightDir
        ∧ Function.Injective basisLabel
        ∧ (∀ columnIndex, basisLabel columnIndex
            ∈ positiveActiveSet activeSet reducedWeight)
        ∧ Submodule.span ℝ
              (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
            = LinearMap.range (Matrix.toLin'
                (chartMultiplierAssembly activeSet reducedWeight tightDir))
        ∧ L * tightBasisColumns tightDir basisLabel = 1
        ∧ (chartPointOfDesign crux.design).chart * tightBasisColumns tightDir basisLabel
            = tightBasisColumns tightDir basisLabel * M
        ∧ M * M = M
        ∧ tightBasisColumns tightDir basisLabel * H
              * (tightBasisColumns tightDir basisLabel)ᵀ
            = chartMultiplierAssembly activeSet reducedWeight tightDir
        ∧ Hᵀ = H
        ∧ H.PosSemidef
        ∧ (∀ coeffVec : Fin 4 → ℝ, H *ᵥ coeffVec = 0 → coeffVec = 0)
        ∧ M * H = H * Mᵀ
        ∧ Matrix.trace M = 2
        ∧ ((∃ columnIndex,
              (datumTightSupport tightDir (basisLabel columnIndex)).card = 2)
          ∨ ((∀ columnIndex,
                (datumTightSupport tightDir (basisLabel columnIndex)).card = 3)
              ∧ ∃ (atomIndex : Fin 6) (privateSlot : Fin 4),
                  basisSupportMultiplicity tightDir basisLabel atomIndex = 1
                  ∧ atomIndex ∈ activeSubset (basisLabel privateSlot)
                  ∧ tightDir (basisLabel privateSlot) atomIndex ≠ 0
                  ∧ (∀ columnIndex, columnIndex ≠ privateSlot →
                      tightDir (basisLabel columnIndex) atomIndex = 0)
                  ∧ M privateSlot privateSlot
                      = chartObjective (chartPointOfDesign crux.design)
                        + (chartPointOfDesign crux.design).weight atomIndex)
          ∨ ((∀ columnIndex,
                (datumTightSupport tightDir (basisLabel columnIndex)).card = 3)
              ∧ ∀ atomIndex,
                  basisSupportMultiplicity tightDir basisLabel atomIndex = 2)) := by
  obtain ⟨reducedWeight, basisLabel, L, M, H, hreducedData, hassemblyEq, hinjective,
    hmem, hspan, hleft, hrepresentation, hidempotent, hHform, hsymmH, hpsd, hker,
    hexchange, htrace, htrichotomy⟩ :=
    crux.exists_rankFour_support_dispatch hdata hrankFour
  refine ⟨reducedWeight, basisLabel, L, M, H, hreducedData, hassemblyEq, hinjective,
    hmem, hspan, hleft, hrepresentation, hidempotent, hHform, hsymmH, hpsd, hker,
    hexchange, htrace, ?_⟩
  rcases htrichotomy with htwo | ⟨hthree, atomIndex, hmult⟩ | hdense
  · exact Or.inl htwo
  · refine Or.inr (Or.inl ⟨hthree, atomIndex, ?_⟩)
    have hmemActive : ∀ columnIndex, basisLabel columnIndex ∈ activeSet :=
      fun columnIndex => positiveActiveSet_subset_activeSet (hmem columnIndex)
    obtain ⟨privateSlot, hatomMem, hslotNe, hprivate⟩ :=
      exists_private_slot_of_multiplicity_one hreducedData basisLabel
        hmemActive hmult
    exact ⟨privateSlot, hmult, hatomMem, hslotNe, hprivate,
      coefficient_diagonal_eq_of_private_atom hreducedData basisLabel
        hrepresentation (hmemActive privateSlot) hatomMem hprivate hslotNe⟩
  · exact Or.inr (Or.inr hdense)

end Gtz

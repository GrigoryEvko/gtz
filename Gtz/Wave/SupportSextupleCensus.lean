import Gtz.Wave.RankSixNormalForm
import Gtz.Wave.SupportQuintupleCensus

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The support-sextuple census — the trichotomy of the rank-six rung

The six basis supports of a rank-six crux datum have cardinality two or
three (the dichotomy) and cover the six atoms (the coverage law).  The
branches mirror the rank-five trichotomy: some support has cardinality
two, or all six have cardinality three and some atom is private to one
support, or all six have cardinality three and every atom sits in at
least two supports.  In the dense branch the mass count gives eighteen
incidences over six atoms, thus some atom sits in at least three
supports — the heavy atom.

## The independence cap at six directions

Six basis directions span the ambient space, thus at most `|T|` basis
supports fit inside an atom set `T`.  The cap kills the fully private
sub-branch outright: a private support of cardinality three exiles the
other FIVE supports into the three complementary atoms, and five
independent directions do not fit in a three-dimensional coordinate
subspace.  The cap lemmas are the landed rank-generic ones from the
quintuple census — the sextuple census consumes them at `Fin 6`.

## The census count

The numeric census (`r6sweep_report.md`, engine `r6harden_probe.c`)
enumerates multisets of six card-3 blocks that cover the six atoms, up to
the atom symmetry: 334 representatives, all infeasible under first order
plus the ceiling, with floors near `8.7e-3`.  The recount
(`r6arc_census.py`) confirms 334 and classifies: 186 representatives
carry a multiplicity-one atom (the private branch), 148 are dense.  The
Hall-type independence cap makes 19 representatives vacuous (a block
subfamily concentrated in fewer atoms than slots), and the shared-block
cap (no block carries three slots) makes 41 more vacuous.  The twenty
shapes of the numeric report that no single mechanism drop explains are
exactly cap-vacuous cells.  After the two caps 274 representatives stay
combinatorially live: 137 private and 137 dense, with the dense mass
profiles from `(2,2,2,2,4,6)` thru `(3,3,3,3,3,3)`.  The Lean census is
coarser than the numeric one: the trichotomy names the branch, and the
per-branch work refines it, exactly as the lower rungs did.  The card-2
branch is invisible to the block census — the numeric hardening pass
(`r6harden_report.md`) swept the card-2 support masks separately, with
the same verdict.

## The realness calibration

The complex two-trine witness satisfies the FULL first-order system over
the complex field and sits in THIS cell: assembly rank six, captured rank
three, eighteen dense argmax labels.  Every rank-six pattern branch must
END in a real-only step.  The approved real-only exits are the sign
enumeration of an entry recovered from a square, the odd sign cycle
`false_of_oppositeSign_triangle`, and the real ratio of a two-by-two
least eigenvector.  The complex-valid tools must NOT close a branch
alone: the private-atom linear kills, the parallel-pair atom merge, the
circuit equations, the H-form laws, the coverage law, the support
dichotomy, the independence cap, and the value and trace windows.  The
numeric decision says the real first-order + ceiling system is empty over
the census and every trine tier while the complex analogue is feasible —
realness enters through the certificates, not through curvature.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.false_of_fully_private_sextuple` — **THE FULLY PRIVATE KILL.**  A
  fully private card-3 support dies at rank six by the cap alone.
* `Gtz.basisSupport_sextuple_trichotomy` — **THE TRICHOTOMY.**
* `Gtz.SixThreeCrux.exists_rankSix_pinned_dispatch` — **THE PINNED
  DISPATCH.**  The normal form, the trichotomy, and the diagonal pin of
  the private branch, at every rank-six crux datum.

## Vacuity

The crux statement is vacuous if `Gtz.GtzWeighted 6 3` holds.  The
combinatorial statements are unconditional.
-/

namespace Gtz

open Matrix

variable {activeIndex : Type*}

/-- **THE FULLY PRIVATE KILL.**  At six independent basis directions over
six atoms, a card-3 support whose atoms all have multiplicity one is
impossible: the other five supports sit inside the three complementary
atoms, against the independence cap. -/
theorem false_of_fully_private_sextuple {activeIndex : Type*}
    {tightDir : activeIndex → Fin 6 → ℝ} {basisLabel : Fin 6 → activeIndex}
    (hindep : LinearIndependent ℝ
      (fun columnIndex => tightDir (basisLabel columnIndex)))
    {privateSlot : Fin 6}
    (hcardS : (datumTightSupport tightDir (basisLabel privateSlot)).card = 3)
    (hallOne : ∀ atomIndex ∈ datumTightSupport tightDir (basisLabel privateSlot),
      basisSupportMultiplicity tightDir basisLabel atomIndex = 1) :
    False := by
  classical
  have hsub : ∀ columnIndex ∈ Finset.univ.erase privateSlot,
      datumTightSupport tightDir (basisLabel columnIndex)
        ⊆ Finset.univ \ datumTightSupport tightDir (basisLabel privateSlot) := by
    intro columnIndex hmemErase atomIndex hmemSupp
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, fun hmemS => ?_⟩
    have hzero := tightDir_eq_zero_of_multiplicity_one_of_ne
      (hallOne _ hmemS) hmemS (Finset.ne_of_mem_erase hmemErase)
    exact mem_datumTightSupport.mp hmemSupp hzero
  have hcap := card_le_card_of_supports_subset hindep
    (Finset.univ.erase privateSlot)
    (Finset.univ \ datumTightSupport tightDir (basisLabel privateSlot)) hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, Finset.card_univ_sdiff, Fintype.card_fin, hcardS] at hcap
  omega

/-- **THE SUPPORT-SEXTUPLE TRICHOTOMY.**  Six supports of cardinality two
or three that cover the six atoms fall into three classes: some support
has cardinality two, or all six have cardinality three and some atom is
private, or all six have cardinality three and every atom sits in at
least two supports.  In the dense branch the mass count gives eighteen
incidences over six atoms, thus some atom sits in at least three
supports. -/
theorem basisSupport_sextuple_trichotomy {activeIndex : Type*}
    (tightDir : activeIndex → (Fin 6 → ℝ)) (basisLabel : Fin 6 → activeIndex)
    (hcard : ∀ columnIndex,
        (datumTightSupport tightDir (basisLabel columnIndex)).card = 2
      ∨ (datumTightSupport tightDir (basisLabel columnIndex)).card = 3)
    (hcover : ∀ atomIndex : Fin 6,
        0 < basisSupportMultiplicity tightDir basisLabel atomIndex) :
    (∃ columnIndex, (datumTightSupport tightDir (basisLabel columnIndex)).card = 2)
      ∨ ((∀ columnIndex,
            (datumTightSupport tightDir (basisLabel columnIndex)).card = 3)
          ∧ ∃ atomIndex,
              basisSupportMultiplicity tightDir basisLabel atomIndex = 1)
      ∨ ((∀ columnIndex,
            (datumTightSupport tightDir (basisLabel columnIndex)).card = 3)
          ∧ (∀ atomIndex,
              2 ≤ basisSupportMultiplicity tightDir basisLabel atomIndex)
          ∧ ∃ atomIndex,
              3 ≤ basisSupportMultiplicity tightDir basisLabel atomIndex) := by
  classical
  by_cases htwo : ∃ columnIndex,
      (datumTightSupport tightDir (basisLabel columnIndex)).card = 2
  · exact Or.inl htwo
  have hthree : ∀ columnIndex,
      (datumTightSupport tightDir (basisLabel columnIndex)).card = 3 :=
    fun columnIndex =>
      (hcard columnIndex).resolve_left fun hcontra => htwo ⟨columnIndex, hcontra⟩
  by_cases hprivate : ∃ atomIndex,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 1
  · exact Or.inr (Or.inl ⟨hthree, hprivate⟩)
  have htwoLe : ∀ atomIndex : Fin 6,
      2 ≤ basisSupportMultiplicity tightDir basisLabel atomIndex := by
    intro atomIndex
    have hpos := hcover atomIndex
    have hne : basisSupportMultiplicity tightDir basisLabel atomIndex ≠ 1 :=
      fun hcontra => hprivate ⟨atomIndex, hcontra⟩
    omega
  have hmass : ∑ atomIndex : Fin 6,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 18 := by
    rw [sum_basisSupportMultiplicity]
    have hsum : ∑ columnIndex : Fin 6,
        (datumTightSupport tightDir (basisLabel columnIndex)).card
        = ∑ _columnIndex : Fin 6, 3 :=
      Finset.sum_congr rfl fun columnIndex _ => hthree columnIndex
    rw [hsum]
    simp
  refine Or.inr (Or.inr ⟨hthree, htwoLe, ?_⟩)
  by_contra hnone
  push Not at hnone
  have hcapAll : ∀ atomIndex : Fin 6,
      basisSupportMultiplicity tightDir basisLabel atomIndex ≤ 2 := by
    intro atomIndex
    have := hnone atomIndex
    omega
  have hbound : ∑ atomIndex : Fin 6,
      basisSupportMultiplicity tightDir basisLabel atomIndex
      ≤ Finset.univ.card • 2 :=
    Finset.sum_le_card_nsmul _ _ _ fun atomIndex _ => hcapAll atomIndex
  rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbound
  omega

/-- **THE PINNED DISPATCH.**  Every rank-six crux datum carries the normal
form together with the support trichotomy, and the private branch carries
its pin: a private slot whose coefficient diagonal reads `value + weight`
at the private atom.  The dense branch carries the heavy atom. -/
theorem SixThreeCrux.exists_rankSix_pinned_dispatch
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
    (hrankSix : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir))) = 6) :
    ∃ (reducedWeight : activeIndex → ℝ)
      (basisLabel : Fin 6 → activeIndex)
      (L : Matrix (Fin 6) (Fin 6) ℝ) (M H : Matrix (Fin 6) (Fin 6) ℝ),
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
        ∧ tightBasisColumns tightDir basisLabel * L = 1
        ∧ (chartPointOfDesign crux.design).chart * tightBasisColumns tightDir basisLabel
            = tightBasisColumns tightDir basisLabel * M
        ∧ M * M = M
        ∧ tightBasisColumns tightDir basisLabel * H
              * (tightBasisColumns tightDir basisLabel)ᵀ
            = chartMultiplierAssembly activeSet reducedWeight tightDir
        ∧ Hᵀ = H
        ∧ H.PosSemidef
        ∧ (∀ coeffVec : Fin 6 → ℝ, H *ᵥ coeffVec = 0 → coeffVec = 0)
        ∧ M * H = H * Mᵀ
        ∧ Matrix.trace M = 3
        ∧ ((∃ columnIndex,
              (datumTightSupport tightDir (basisLabel columnIndex)).card = 2)
          ∨ ((∀ columnIndex,
                (datumTightSupport tightDir (basisLabel columnIndex)).card = 3)
              ∧ ∃ (atomIndex : Fin 6) (privateSlot : Fin 6),
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
              ∧ (∀ atomIndex, 2 ≤ basisSupportMultiplicity tightDir basisLabel
                  atomIndex)
              ∧ ∃ atomIndex, 3 ≤ basisSupportMultiplicity tightDir basisLabel
                  atomIndex)) := by
  obtain ⟨reducedWeight, basisLabel, L, M, H, hreducedData, hassemblyEq, hinjective,
    hmem, hspan, hleft, hright, hrepresentation, hidempotent, hHform, hsymmH, hpsd,
    hker, hexchange, htrace⟩ := crux.exists_rankSix_coefficient_normalForm hdata
      hrankSix
  have hmemActive : ∀ columnIndex, basisLabel columnIndex ∈ activeSet :=
    fun columnIndex => positiveActiveSet_subset_activeSet (hmem columnIndex)
  have hcard : ∀ columnIndex,
      (datumTightSupport tightDir (basisLabel columnIndex)).card = 2
      ∨ (datumTightSupport tightDir (basisLabel columnIndex)).card = 3 :=
    fun columnIndex => crux.card_datumTightSupport_eq_two_or_three hreducedData
      (hmemActive columnIndex)
  have hcover : ∀ atomIndex : Fin 6,
      0 < basisSupportMultiplicity tightDir basisLabel atomIndex :=
    basisSupportMultiplicity_pos_of_Hform hreducedData basisLabel H hHform
  refine ⟨reducedWeight, basisLabel, L, M, H, hreducedData, hassemblyEq, hinjective,
    hmem, hspan, hleft, hright, hrepresentation, hidempotent, hHform, hsymmH, hpsd,
    hker, hexchange, htrace, ?_⟩
  rcases basisSupport_sextuple_trichotomy tightDir basisLabel hcard hcover with
    htwo | ⟨hthree, atomIndex, hmult⟩ | hdense
  · exact Or.inl htwo
  · refine Or.inr (Or.inl ⟨hthree, atomIndex, ?_⟩)
    obtain ⟨privateSlot, hatomMem, hslotNe, hprivate⟩ :=
      exists_private_slot_of_multiplicity_one hreducedData basisLabel
        hmemActive hmult
    exact ⟨privateSlot, hmult, hatomMem, hslotNe, hprivate,
      coefficient_diagonal_eq_of_private_atom hreducedData basisLabel
        hrepresentation (hmemActive privateSlot) hatomMem hprivate hslotNe⟩
  · exact Or.inr (Or.inr hdense)

end Gtz

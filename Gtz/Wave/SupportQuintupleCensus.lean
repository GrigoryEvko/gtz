import Gtz.Wave.RankFiveNormalForm
import Gtz.Wave.PinnedSupportDispatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The support-quintuple census — the trichotomy of the rank-five rung

The five basis supports of a rank-five crux datum have cardinality two or
three (the dichotomy) and cover the six atoms (the coverage law).  The
branches are the analog of the rank-four trichotomy: some support has
cardinality two, or all five have cardinality three and some atom is
private to one support, or all five have cardinality three and every atom
sits in at least two supports.  In the dense branch the mass count gives
fifteen incidences over six atoms, thus some atom sits in at least three
supports — the heavy atom, the structural novelty of rank five.

## The independence cap

Five basis directions are linearly independent, because the left inverse
kills every relation.  Thus at most `|T|` basis supports fit inside an
atom set `T`: the directions live in a coordinate subspace of dimension
`|T|`.  The cap kills the fully private sub-branch outright: a private
support of cardinality three exiles the other four supports into the
three complementary atoms, and four independent directions do not fit in
a three-dimensional coordinate subspace.  At rank four the same
sub-branch needed the trace budget — at rank five it is pure linear
algebra.

## The census count

The numeric census (`r5sweep_report.md`, engine `r5sweep_probe.c`)
enumerates multisets of five card-3 blocks that cover the six atoms, up
to the atom symmetry: 87 representatives, all infeasible under first
order plus the ceiling, with floors near `8.7e-3`.  The recount
(`r5arc_census.py`) confirms 87 and classifies: 66 representatives carry
a multiplicity-one atom (the private branch), 21 are dense with the mass
profiles `(2,2,2,2,2,5)` twice, `(2,2,2,2,3,4)` seven times, and
`(2,2,2,3,3,3)` twelve times.  Exactly one representative — four copies
of one block plus the complementary block — fails the independence cap
and carries no five-direction basis.  The Lean census is coarser than
the numeric one: the trichotomy names the branch, and the per-branch
work refines it, exactly as the rank-four dispatch did.  The card-2
branch is invisible to the block census, because supports live inside
blocks — the numeric hardening pass (`r6harden_report.md`) swept the
card-2 support masks separately, with the same verdict.

## The realness calibration

The complex two-trine witness (`paper/sections/04-complex.tex`, two
coplanar trines with a shared axis) satisfies the FULL first-order
system over the complex field and sits in the RANK-SIX cell: assembly
rank six, captured rank three, complement rank three.  Thus rank five
contains no known complex datum, but the survivor analysis is
field-agnostic, and every rank-five pattern branch must still END in a
real-only step.  The approved real-only exits are:

- The sign enumeration of an entry recovered from a square (over the
  complex field the phase is a continuum, over the reals a finite split)
- The odd sign cycle `false_of_oppositeSign_triangle`
- The real ratio of a two-by-two least eigenvector (the real symmetric
  gap block gives a real ratio, the Hermitian block gives a phase).

These tools are complex-valid and must NOT close a branch alone: the
private-atom linear kills, the parallel-pair atom merge, the circuit
equations, the H-form laws, the coverage law, the support dichotomy, the
independence cap, and the value and trace windows.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.linearIndependent_tightDir_of_leftInverse` — the left inverse
  makes the basis directions independent.
* `Gtz.card_le_card_of_supports_subset` — **THE INDEPENDENCE CAP.**
* `Gtz.tightDir_eq_zero_of_multiplicity_one_of_ne` — a multiplicity-one
  atom is carried by its slot alone.
* `Gtz.false_of_fully_private_quintuple` — **THE FULLY PRIVATE KILL.**
  A fully private card-3 support dies at rank five by the cap alone.
* `Gtz.basisSupport_quintuple_trichotomy` — **THE TRICHOTOMY.**
* `Gtz.SixThreeCrux.exists_rankFive_pinned_dispatch` — **THE PINNED
  DISPATCH.**  The normal form, the trichotomy, and the diagonal pin of
  the private branch, at every rank-five crux datum.

## Vacuity

The crux statement is vacuous if `Gtz.GtzWeighted 6 3` holds.  The
combinatorial statements and the cap are unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- The left inverse makes the basis directions linearly independent: it
reads every coefficient of a vanishing combination. -/
theorem linearIndependent_tightDir_of_leftInverse
    (basisLabel : Fin basisCount → activeIndex)
    (L : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : L * tightBasisColumns tightDir basisLabel = 1) :
    LinearIndependent ℝ (fun columnIndex => tightDir (basisLabel columnIndex)) := by
  rw [Fintype.linearIndependent_iff]
  intro coeffVec hsum
  have hmulVec : tightBasisColumns tightDir basisLabel *ᵥ coeffVec = 0 := by
    rw [tightBasisColumns_mulVec]
    exact hsum
  have hinjective := injective_toLin_tightBasisColumns_of_leftInverse basisLabel L hleft
  have happly : Matrix.toLin' (tightBasisColumns tightDir basisLabel) coeffVec
      = Matrix.toLin' (tightBasisColumns tightDir basisLabel) 0 := by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hmulVec, Matrix.mulVec_zero]
  have hzero : coeffVec = 0 := hinjective happly
  intro columnIndex
  rw [hzero]
  rfl

/-- **THE INDEPENDENCE CAP.**  Independent basis directions whose supports
sit inside an atom set `T` number at most `|T|`: the restricted family is
independent in the coordinate space of `T`. -/
theorem card_le_card_of_supports_subset
    {basisLabel : Fin basisCount → activeIndex}
    (hindep : LinearIndependent ℝ
      (fun columnIndex => tightDir (basisLabel columnIndex)))
    (slots : Finset (Fin basisCount)) (atoms : Finset (Fin size))
    (hsub : ∀ columnIndex ∈ slots,
      datumTightSupport tightDir (basisLabel columnIndex) ⊆ atoms) :
    slots.card ≤ atoms.card := by
  classical
  have hsubIndep : LinearIndependent ℝ
      (fun columnIndex : {columnIndex // columnIndex ∈ slots} =>
        tightDir (basisLabel columnIndex.1)) :=
    hindep.comp
      (Subtype.val : {columnIndex // columnIndex ∈ slots} → Fin basisCount)
      Subtype.val_injective
  have hrestrictedIndep : LinearIndependent ℝ
      (fun (columnIndex : {columnIndex // columnIndex ∈ slots})
          (atomIndex : {atomIndex // atomIndex ∈ atoms}) =>
        tightDir (basisLabel columnIndex.1) atomIndex.1) := by
    rw [Fintype.linearIndependent_iff] at hsubIndep ⊢
    intro coeffVec hsum
    refine hsubIndep coeffVec ?_
    funext atomIndex
    rw [Finset.sum_apply, Pi.zero_apply]
    by_cases hmemAtom : atomIndex ∈ atoms
    · have hpoint := congrFun hsum ⟨atomIndex, hmemAtom⟩
      rw [Finset.sum_apply, Pi.zero_apply] at hpoint
      simpa using hpoint
    · refine Finset.sum_eq_zero fun columnIndex _ => ?_
      have hzero : tightDir (basisLabel columnIndex.1) atomIndex = 0 := by
        by_contra hne
        exact hmemAtom (hsub columnIndex.1 columnIndex.2
          (mem_datumTightSupport.mpr hne))
      rw [Pi.smul_apply, hzero, smul_zero]
  have hcard := hrestrictedIndep.fintype_card_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe]
    at hcard

/-- A multiplicity-one atom is carried by its slot alone: every other basis
direction vanishes there. -/
theorem tightDir_eq_zero_of_multiplicity_one_of_ne
    {basisLabel : Fin basisCount → activeIndex} {atomIndex : Fin size}
    {privateSlot : Fin basisCount}
    (hmult : basisSupportMultiplicity tightDir basisLabel atomIndex = 1)
    (hmem : atomIndex ∈ datumTightSupport tightDir (basisLabel privateSlot))
    {columnIndex : Fin basisCount} (hne : columnIndex ≠ privateSlot) :
    tightDir (basisLabel columnIndex) atomIndex = 0 := by
  classical
  rw [basisSupportMultiplicity] at hmult
  obtain ⟨uniqueSlot, hfilter⟩ := Finset.card_eq_one.mp hmult
  have hslotMem : privateSlot ∈ Finset.univ.filter (fun innerIndex =>
      atomIndex ∈ datumTightSupport tightDir (basisLabel innerIndex)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
  rw [hfilter, Finset.mem_singleton] at hslotMem
  by_contra hnonzero
  have hcolMem : columnIndex ∈ Finset.univ.filter (fun innerIndex =>
      atomIndex ∈ datumTightSupport tightDir (basisLabel innerIndex)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      mem_datumTightSupport.mpr hnonzero⟩
  rw [hfilter, Finset.mem_singleton] at hcolMem
  exact hne (hcolMem.trans hslotMem.symm)

/-- **THE FULLY PRIVATE KILL.**  At five independent basis directions over
six atoms, a card-3 support whose atoms all have multiplicity one is
impossible: the other four supports sit inside the three complementary
atoms, against the independence cap. -/
theorem false_of_fully_private_quintuple {activeIndex : Type*}
    {tightDir : activeIndex → Fin 6 → ℝ} {basisLabel : Fin 5 → activeIndex}
    (hindep : LinearIndependent ℝ
      (fun columnIndex => tightDir (basisLabel columnIndex)))
    {privateSlot : Fin 5}
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

/-- **THE SUPPORT-QUINTUPLE TRICHOTOMY.**  Five supports of cardinality two
or three that cover the six atoms fall into three classes: some support
has cardinality two, or all five have cardinality three and some atom is
private, or all five have cardinality three and every atom sits in at
least two supports.  In the dense branch the mass count gives fifteen
incidences over six atoms, thus some atom sits in at least three
supports. -/
theorem basisSupport_quintuple_trichotomy {activeIndex : Type*}
    (tightDir : activeIndex → (Fin 6 → ℝ)) (basisLabel : Fin 5 → activeIndex)
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
      basisSupportMultiplicity tightDir basisLabel atomIndex = 15 := by
    rw [sum_basisSupportMultiplicity]
    have hsum : ∑ columnIndex : Fin 5,
        (datumTightSupport tightDir (basisLabel columnIndex)).card
        = ∑ _columnIndex : Fin 5, 3 :=
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

/-- **THE PINNED DISPATCH.**  Every rank-five crux datum carries the normal
form together with the support trichotomy, and the private branch carries
its pin: a private slot whose coefficient diagonal reads `value + weight`
at the private atom.  The dense branch carries the heavy atom. -/
theorem SixThreeCrux.exists_rankFive_pinned_dispatch
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
    (hrankFive : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir))) = 5) :
    ∃ (reducedWeight : activeIndex → ℝ)
      (basisLabel : Fin 5 → activeIndex)
      (L : Matrix (Fin 5) (Fin 6) ℝ) (M H : Matrix (Fin 5) (Fin 5) ℝ),
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
        ∧ (∀ coeffVec : Fin 5 → ℝ, H *ᵥ coeffVec = 0 → coeffVec = 0)
        ∧ M * H = H * Mᵀ
        ∧ (Matrix.trace M = 2 ∨ Matrix.trace M = 3)
        ∧ ((∃ columnIndex,
              (datumTightSupport tightDir (basisLabel columnIndex)).card = 2)
          ∨ ((∀ columnIndex,
                (datumTightSupport tightDir (basisLabel columnIndex)).card = 3)
              ∧ ∃ (atomIndex : Fin 6) (privateSlot : Fin 5),
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
    hmem, hspan, hleft, hrepresentation, hidempotent, hHform, hsymmH, hpsd, hker,
    hexchange, htrace⟩ := crux.exists_rankFive_coefficient_normalForm hdata hrankFive
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
    hmem, hspan, hleft, hrepresentation, hidempotent, hHform, hsymmH, hpsd, hker,
    hexchange, htrace, ?_⟩
  rcases basisSupport_quintuple_trichotomy tightDir basisLabel hcard hcover with
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

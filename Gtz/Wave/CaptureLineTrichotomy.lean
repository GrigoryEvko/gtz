import Gtz.Wave.ArgmaxBlockFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The capture line trichotomy — the floored residue splits in two

The capture line of a rank-four frame is chart-fixed, basis-null and
nonzero, thus its support has one, two, or three-plus atoms.  The
singleton support DIES OUTRIGHT: five atoms orthogonal to the
coplanarity normal refuse the co-singleton field.  The two live
branches become two named residues, and the floored rank-four residue
follows from the pair.

**THE PAIR BRANCH IS THE CLONE BRANCH.**  A pair-supported basis-null
direction makes the two basis rows proportional, thus the pair is a
clone pair, the landed chart pair minor makes both clone atoms
INTERIOR, and the coplanarity reading puts the four other atoms into
one plane.  The pair residue receives all of that structure as
hypotheses: the clone law in both directions, the chart-fixed pair
line, the plane normal with its four orthogonal atoms, and the
chart-null basis-null direction alongside.

**THE WIDE BRANCH** receives the capture line alive at three atoms
together with the chart-null direction.

Thus the campaign endgame at rank four reads: the cell follows from
the PAIR residue, the WIDE residue, and the six upper closures.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.RankFourFrame.captureLine_pair_clone`,
  `Gtz.RankFourFrame.captureLine_pair_clone_swap` — **THE PAIR IS A
  CLONE PAIR, both directions.**
* `Gtz.RankFourFrame.captureLine_pair_interior` — **BOTH CLONE ATOMS
  ARE INTERIOR.**
* `Gtz.RankFourCaptureLinePairFlooredClosed`,
  `Gtz.RankFourCaptureLineWideFlooredClosed` — the two named residues.
* `Gtz.rankFourChartNullBasisNullFloored_of_pair_wide` — **THE
  TRICHOTOMY: the singleton dies here, the residue splits in two.**
* `Gtz.isSixThreeAssemblyRankExcludedFloored_four_of_pair_wide`,
  `Gtz.gtzWeighted_six_three_of_captureLine_residues`,
  `Gtz.gtzWeightedAll_three_of_captureLine_residues` — **THE CELL FROM
  THE TWO RESIDUES AND THE SIX UPPER CLOSURES.**

## Vacuity

Every statement is vacuous if `Gtz.GtzWeighted 6 3` holds: no crux
exists, thus no frame and no capture line exists.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the pair clone laws of a basis-null line -/

section PairClone

variable {crux : SixThreeCrux}

/-- **A PAIR-SUPPORTED BASIS-NULL DIRECTION IS A CLONE PAIR.**  Every
basis row at the second atom is the fixed multiple of the row at the
first: the pair carries the whole dot product. -/
theorem RankFourFrame.captureLine_pair_clone (frame : RankFourFrame crux)
    {lineVec : Fin 6 → ℝ} {atomOne atomTwo : Fin 6} (hne : atomOne ≠ atomTwo)
    (hliveTwo : lineVec atomTwo ≠ 0)
    (hoff : ∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      lineVec atomIndex = 0)
    (hlineBasis : ∀ slot : Fin 4,
      frame.tightDir (frame.basisLabel slot) ⬝ᵥ lineVec = 0)
    (slot : Fin 4) :
    frame.tightDir (frame.basisLabel slot) atomTwo
      = (-(lineVec atomOne) / lineVec atomTwo)
        * frame.tightDir (frame.basisLabel slot) atomOne := by
  classical
  have hsum := hlineBasis slot
  rw [dotProduct] at hsum
  have hpair : ∑ atomIndex : Fin 6,
        frame.tightDir (frame.basisLabel slot) atomIndex * lineVec atomIndex
      = frame.tightDir (frame.basisLabel slot) atomOne * lineVec atomOne
        + frame.tightDir (frame.basisLabel slot) atomTwo * lineVec atomTwo := by
    rw [← Finset.sum_pair (f := fun atomIndex =>
      frame.tightDir (frame.basisLabel slot) atomIndex * lineVec atomIndex) hne]
    refine (Finset.sum_subset (Finset.subset_univ _) fun atomIndex _ hnot => ?_).symm
    have hnotOne : atomIndex ≠ atomOne := fun hcontra => hnot (by
      rw [hcontra]; exact Finset.mem_insert_self atomOne {atomTwo})
    have hnotTwo : atomIndex ≠ atomTwo := fun hcontra => hnot (by
      rw [hcontra]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self atomTwo))
    rw [hoff atomIndex hnotOne hnotTwo, mul_zero]
  rw [hpair] at hsum
  field_simp
  linarith [hsum]

/-- The clone law with the two atoms interchanged. -/
theorem RankFourFrame.captureLine_pair_clone_swap (frame : RankFourFrame crux)
    {lineVec : Fin 6 → ℝ} {atomOne atomTwo : Fin 6} (hne : atomOne ≠ atomTwo)
    (hliveOne : lineVec atomOne ≠ 0)
    (hoff : ∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      lineVec atomIndex = 0)
    (hlineBasis : ∀ slot : Fin 4,
      frame.tightDir (frame.basisLabel slot) ⬝ᵥ lineVec = 0)
    (slot : Fin 4) :
    frame.tightDir (frame.basisLabel slot) atomOne
      = (-(lineVec atomTwo) / lineVec atomOne)
        * frame.tightDir (frame.basisLabel slot) atomTwo :=
  frame.captureLine_pair_clone hne.symm hliveOne
    (fun atomIndex hindexTwo hindexOne => hoff atomIndex hindexOne hindexTwo)
    hlineBasis slot

/-- **BOTH CLONE ATOMS OF A PAIR-SUPPORTED CAPTURE LINE ARE
INTERIOR.**  The landed chart pair minor law fires on the clone
relation in each direction. -/
theorem RankFourFrame.captureLine_pair_interior (frame : RankFourFrame crux)
    {lineVec : Fin 6 → ℝ} {atomOne atomTwo : Fin 6} (hne : atomOne ≠ atomTwo)
    (hliveOne : lineVec atomOne ≠ 0) (hliveTwo : lineVec atomTwo ≠ 0)
    (hoff : ∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      lineVec atomIndex = 0)
    (hlineBasis : ∀ slot : Fin 4,
      frame.tightDir (frame.basisLabel slot) ⬝ᵥ lineVec = 0) :
    (0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomOne)
      ∧ (0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomTwo) :=
  ⟨frame.shifted_weight_pos_of_clone_minor hne
      (fun slot => frame.captureLine_pair_clone hne hliveTwo hoff hlineBasis slot),
    frame.shifted_weight_pos_of_clone_minor hne.symm
      (fun slot => frame.captureLine_pair_clone_swap hne hliveOne hoff hlineBasis slot)⟩

end PairClone

/-! ## Layer 2 — the two named residues -/

section NamedResidues

/-- **THE PAIR RESIDUE.**  A rank-four frame with the argmax floor, a
chart-null basis-null direction, and a pair-supported capture line
dies.  The residue receives the clone laws, the interiority of the two
clone atoms, and the plane normal with its four orthogonal atoms. -/
def RankFourCaptureLinePairFlooredClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankFourFrame crux),
    (∀ activeLabel ∈ frame.activeSet,
      BlockFloor (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design))
        (frame.activeSubset activeLabel)) →
    ∀ (nullVec lineVec : Fin 6 → ℝ) (atomOne atomTwo : Fin 6)
      (normalVec : Fin 3 → ℝ),
    nullVec ≠ 0 →
    (∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) ⬝ᵥ nullVec = 0) →
    (chartPointOfDesign crux.design).chart *ᵥ nullVec = 0 →
    atomOne ≠ atomTwo →
    lineVec atomOne ≠ 0 →
    lineVec atomTwo ≠ 0 →
    (∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      lineVec atomIndex = 0) →
    (chartPointOfDesign crux.design).chart *ᵥ lineVec = lineVec →
    (∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) ⬝ᵥ lineVec = 0) →
    (∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) atomTwo
      = (-(lineVec atomOne) / lineVec atomTwo)
        * frame.tightDir (frame.basisLabel slot) atomOne) →
    (0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne) →
    (0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomTwo) →
    normalVec ≠ 0 →
    (∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      crux.design.atom atomIndex ⬝ᵥ normalVec = 0) →
    False

/-- **THE WIDE RESIDUE.**  A rank-four frame with the argmax floor, a
chart-null basis-null direction, and a capture line alive at three
atoms dies. -/
def RankFourCaptureLineWideFlooredClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankFourFrame crux),
    (∀ activeLabel ∈ frame.activeSet,
      BlockFloor (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design))
        (frame.activeSubset activeLabel)) →
    ∀ (nullVec lineVec : Fin 6 → ℝ) (atomOne atomTwo atomThree : Fin 6),
    nullVec ≠ 0 →
    (∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) ⬝ᵥ nullVec = 0) →
    (chartPointOfDesign crux.design).chart *ᵥ nullVec = 0 →
    atomOne ≠ atomTwo → atomOne ≠ atomThree → atomTwo ≠ atomThree →
    lineVec atomOne ≠ 0 →
    lineVec atomTwo ≠ 0 →
    lineVec atomThree ≠ 0 →
    (chartPointOfDesign crux.design).chart *ᵥ lineVec = lineVec →
    (∀ slot : Fin 4, frame.tightDir (frame.basisLabel slot) ⬝ᵥ lineVec = 0) →
    False

end NamedResidues

/-! ## Layer 3 — the trichotomy -/

section Trichotomy

/-- **THE TRICHOTOMY.**  The support of the capture line has one, two,
or three-plus atoms.  The singleton dies at the co-singleton field, the
pair feeds the pair residue with the clone structure derived here, and
the rest feeds the wide residue. -/
theorem rankFourChartNullBasisNullFloored_of_pair_wide
    (hpair : RankFourCaptureLinePairFlooredClosed)
    (hwide : RankFourCaptureLineWideFlooredClosed) :
    RankFourChartNullBasisNullFlooredClosed := by
  classical
  intro crux frame hfloors nullVec hne hbasis hchart
  obtain ⟨lineVec, hlineNe, _, hlineBasis, hlineChart⟩ := frame.exists_capture_line
  set support : Finset (Fin 6) :=
    Finset.univ.filter (fun atomIndex => lineVec atomIndex ≠ 0) with hsupportDef
  have hmem : ∀ atomIndex : Fin 6, atomIndex ∈ support ↔ lineVec atomIndex ≠ 0 := by
    intro atomIndex
    rw [hsupportDef]
    simp
  have hnonempty : 0 < support.card := by
    obtain ⟨liveAtom, hlive⟩ := Function.ne_iff.mp hlineNe
    exact Finset.card_pos.mpr ⟨liveAtom, (hmem liveAtom).mpr (by simpa using hlive)⟩
  rcases Nat.lt_or_ge support.card 2 with hone | htwoPlus
  · obtain ⟨liveAtom, hsingleton⟩ := Finset.card_eq_one.mp
      (show support.card = 1 by omega)
    refine crux.false_of_chart_fixed_singleton hlineNe (liveAtom := liveAtom) ?_ hlineChart
    intro atomIndex hindex
    by_contra hlive
    have hmemIndex := (hmem atomIndex).mpr hlive
    rw [hsingleton, Finset.mem_singleton] at hmemIndex
    exact hindex hmemIndex
  rcases Nat.lt_or_ge support.card 3 with htwo | hthreePlus
  · obtain ⟨atomOne, atomTwo, hneAtoms, hpairSet⟩ := Finset.card_eq_two.mp
      (show support.card = 2 by omega)
    have hliveOne : lineVec atomOne ≠ 0 := (hmem atomOne).mp (by
      rw [hpairSet]; exact Finset.mem_insert_self atomOne {atomTwo})
    have hliveTwo : lineVec atomTwo ≠ 0 := (hmem atomTwo).mp (by
      rw [hpairSet]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self atomTwo))
    have hoff : ∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
        lineVec atomIndex = 0 := by
      intro atomIndex hindexOne hindexTwo
      by_contra hlive
      have hmemIndex := (hmem atomIndex).mpr hlive
      rw [hpairSet, Finset.mem_insert, Finset.mem_singleton] at hmemIndex
      rcases hmemIndex with hcontra | hcontra
      · exact hindexOne hcontra
      · exact hindexTwo hcontra
    obtain ⟨normalVec, hnormalNe, hnormal⟩ :=
      crux.exists_orthogonal_of_chart_fixed hlineNe hlineChart
    obtain ⟨hinteriorOne, hinteriorTwo⟩ :=
      frame.captureLine_pair_interior hneAtoms hliveOne hliveTwo hoff hlineBasis
    exact hpair crux frame hfloors nullVec lineVec atomOne atomTwo normalVec hne hbasis
      hchart hneAtoms hliveOne hliveTwo hoff hlineChart hlineBasis
      (fun slot => frame.captureLine_pair_clone hneAtoms hliveTwo hoff hlineBasis slot)
      hinteriorOne hinteriorTwo hnormalNe
      (fun atomIndex hindexOne hindexTwo =>
        hnormal atomIndex (hoff atomIndex hindexOne hindexTwo))
  · obtain ⟨atomOne, atomTwo, atomThree, hmemOne, hmemTwo, hmemThree, hneOneTwo,
      hneOneThree, hneTwoThree⟩ := Finset.two_lt_card_iff.mp
      (show 2 < support.card by omega)
    exact hwide crux frame hfloors nullVec lineVec atomOne atomTwo atomThree hne hbasis
      hchart hneOneTwo hneOneThree hneTwoThree ((hmem atomOne).mp hmemOne)
      ((hmem atomTwo).mp hmemTwo) ((hmem atomThree).mp hmemThree) hlineChart hlineBasis

/-- **THE FLOORED RANK-FOUR RUNG FROM THE TWO RESIDUES.** -/
theorem isSixThreeAssemblyRankExcludedFloored_four_of_pair_wide
    (hpair : RankFourCaptureLinePairFlooredClosed)
    (hwide : RankFourCaptureLineWideFlooredClosed) :
    IsSixThreeAssemblyRankExcludedFloored 4 :=
  isSixThreeAssemblyRankExcludedFloored_four_of_chartNullBasisNullFloored
    (rankFourChartNullBasisNullFloored_of_pair_wide hpair hwide)

/-- **THE CELL FROM THE TWO RESIDUES AND THE SIX UPPER CLOSURES.** -/
theorem gtzWeighted_six_three_of_captureLine_residues
    (hpair : RankFourCaptureLinePairFlooredClosed)
    (hwide : RankFourCaptureLineWideFlooredClosed)
    (hfiveOne : RankFiveSupportTwoClosed)
    (hfiveTwo : RankFiveSharedPrivateClosed)
    (hfiveDense : RankFiveDenseClosed)
    (hsixOne : RankSixSupportTwoClosed)
    (hsixTwo : RankSixSharedPrivateClosed)
    (hsixDense : RankSixDenseClosed) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_flooredResidue_of_upperClosures
    (rankFourChartNullBasisNullFloored_of_pair_wide hpair hwide) hfiveOne hfiveTwo
    hfiveDense hsixOne hsixTwo hsixDense

/-- **THE RANK-THREE PAYOFF FROM THE TWO RESIDUES.** -/
theorem gtzWeightedAll_three_of_captureLine_residues
    (hpair : RankFourCaptureLinePairFlooredClosed)
    (hwide : RankFourCaptureLineWideFlooredClosed)
    (hfiveOne : RankFiveSupportTwoClosed)
    (hfiveTwo : RankFiveSharedPrivateClosed)
    (hfiveDense : RankFiveDenseClosed)
    (hsixOne : RankSixSupportTwoClosed)
    (hsixTwo : RankSixSharedPrivateClosed)
    (hsixDense : RankSixDenseClosed) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three
    (gtzWeighted_six_three_of_captureLine_residues hpair hwide hfiveOne hfiveTwo
      hfiveDense hsixOne hsixTwo hsixDense)

end Trichotomy

end Gtz

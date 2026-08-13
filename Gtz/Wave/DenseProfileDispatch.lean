import Gtz.Wave.DenseFullCarrierQuantization

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The dense profile dispatch — the multiplicity census of the two rungs

The dense branches of the rank-five and rank-six rungs carry all basis
supports at cardinality three, every atom in at least two supports, and
one atom in at least three.  The double count prices the multiplicity
vector: fifteen at rank five, eighteen at rank six.  With the landed
multiplicity caps, the vector splits into three profiles by its maximum,
and each profile carries exact counts.

At rank five the profiles are exact: a multiplicity-five atom forces
five doubles, a multiplicity-four atom forces one triple and four
doubles, and a maximum of three forces exactly three triples.  The
heavy-five profile also receives the landed pins: the coefficient trace
is two and the heavy shifted weight is zero.  At rank six the maximum
is five by the quantization cap, and the all-triple profile is the
exact `(3, 3, 3, 3, 3, 3)` vector — the cell where the complex trine
shadow lives.

Each dense closure now reduces to three named profile closures.  The
dispatch theorems consume nothing beyond the landed census laws, thus
the certificate work per profile proceeds in parallel.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.double_esum_of_idempotent` — **THE PAIR MINOR SUM.**  The full
  double sum of the two-by-two minors of an idempotent reads the trace.
* `Gtz.forall_carrier_of_multiplicity_eq_card` — the full-carrier
  extraction.
* `Gtz.basisSupportMultiplicity_le_basisCount` — the trivial cap.
* `Gtz.RankFiveFrame.dense_multiplicity_sum`,
  `Gtz.RankSixFrame.dense_multiplicity_sum` — the double counts.
* `Gtz.RankFiveFrame.doubles_of_multiplicity_five`,
  `Gtz.RankFiveFrame.le_three_of_multiplicity_four`,
  `Gtz.RankFiveFrame.exists_triple_of_multiplicity_four`,
  `Gtz.RankFiveFrame.exists_three_triples_of_max_three` — the exact
  rank-five profiles.
* `Gtz.RankSixFrame.all_triples_of_max_three` — the exact rank-six
  all-triple profile.
* `Gtz.RankFiveDenseHeavyFiveClosed`,
  `Gtz.RankFiveDenseHeavyFourClosed`,
  `Gtz.RankFiveDenseThreeTriplesClosed` — **THE RANK-FIVE PROFILE
  CLOSURES.**
* `Gtz.rankFiveDenseClosed_of_profile_closures` — **THE RANK-FIVE
  DISPATCH.**
* `Gtz.RankSixDenseHeavyFiveClosed`, `Gtz.RankSixDenseHeavyFourClosed`,
  `Gtz.RankSixDenseAllTriplesClosed` — **THE RANK-SIX PROFILE
  CLOSURES.**
* `Gtz.rankSixDenseClosed_of_profile_closures` — **THE RANK-SIX
  DISPATCH.**

## Vacuity

The profile closures and the dispatches are vacuous if
`Gtz.GtzWeighted 6 3` holds: no crux exists, thus no frame exists.
-/

namespace Gtz

open Matrix

variable {size : ℕ} {activeIndex : Type*}
variable {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the generic census tools -/

/-- **THE PAIR MINOR SUM.**  The full double sum of the two-by-two
principal minors of an idempotent matrix reads the trace: the diagonal
terms vanish, and each unordered pair appears two times. -/
theorem double_esum_of_idempotent {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hidem : M * M = M) :
    ∑ rowIndex : Fin n, ∑ columnIndex : Fin n,
        (M rowIndex rowIndex * M columnIndex columnIndex
          - M rowIndex columnIndex * M columnIndex rowIndex)
      = Matrix.trace M ^ 2 - Matrix.trace M := by
  have htrace : Matrix.trace M = ∑ rowIndex : Fin n, M rowIndex rowIndex := by
    simp [Matrix.trace, Matrix.diag]
  have hcross : ∑ rowIndex : Fin n, ∑ columnIndex : Fin n,
      M rowIndex columnIndex * M columnIndex rowIndex = Matrix.trace M := by
    calc ∑ rowIndex : Fin n, ∑ columnIndex : Fin n,
        M rowIndex columnIndex * M columnIndex rowIndex
        = ∑ rowIndex : Fin n, (M * M) rowIndex rowIndex := by
          refine Finset.sum_congr rfl fun rowIndex _ => ?_
          rw [Matrix.mul_apply]
      _ = ∑ rowIndex : Fin n, M rowIndex rowIndex := by rw [hidem]
      _ = Matrix.trace M := htrace.symm
  have hproduct : ∑ rowIndex : Fin n, ∑ columnIndex : Fin n,
      M rowIndex rowIndex * M columnIndex columnIndex
      = Matrix.trace M ^ 2 := by
    calc ∑ rowIndex : Fin n, ∑ columnIndex : Fin n,
        M rowIndex rowIndex * M columnIndex columnIndex
        = ∑ rowIndex : Fin n, M rowIndex rowIndex
          * ∑ columnIndex : Fin n, M columnIndex columnIndex := by
          refine Finset.sum_congr rfl fun rowIndex _ => ?_
          rw [Finset.mul_sum]
      _ = (∑ rowIndex : Fin n, M rowIndex rowIndex)
          * ∑ columnIndex : Fin n, M columnIndex columnIndex := by
          rw [Finset.sum_mul]
      _ = Matrix.trace M ^ 2 := by rw [← htrace, sq]
  calc ∑ rowIndex : Fin n, ∑ columnIndex : Fin n,
      (M rowIndex rowIndex * M columnIndex columnIndex
        - M rowIndex columnIndex * M columnIndex rowIndex)
      = ∑ rowIndex : Fin n, (∑ columnIndex : Fin n,
          M rowIndex rowIndex * M columnIndex columnIndex
        - ∑ columnIndex : Fin n,
            M rowIndex columnIndex * M columnIndex rowIndex) := by
        refine Finset.sum_congr rfl fun rowIndex _ => ?_
        rw [Finset.sum_sub_distrib]
    _ = ∑ rowIndex : Fin n, ∑ columnIndex : Fin n,
          M rowIndex rowIndex * M columnIndex columnIndex
        - ∑ rowIndex : Fin n, ∑ columnIndex : Fin n,
            M rowIndex columnIndex * M columnIndex rowIndex := by
        rw [Finset.sum_sub_distrib]
    _ = Matrix.trace M ^ 2 - Matrix.trace M := by rw [hproduct, hcross]

/-- **THE FULL-CARRIER EXTRACTION.**  A multiplicity equal to the basis
count puts the atom in every basis support. -/
theorem forall_carrier_of_multiplicity_eq_card
    {basisLabel : Fin basisCount → activeIndex} {atomIndex : Fin size}
    (hfull : basisSupportMultiplicity tightDir basisLabel atomIndex
      = basisCount) :
    ∀ columnIndex, atomIndex ∈ datumTightSupport tightDir
      (basisLabel columnIndex) := by
  classical
  have huniv := Finset.eq_univ_of_card
    (Finset.univ.filter fun columnIndex =>
      atomIndex ∈ datumTightSupport tightDir (basisLabel columnIndex))
    (by rw [← basisSupportMultiplicity, hfull, Fintype.card_fin])
  intro columnIndex
  have hmem : columnIndex ∈ Finset.univ.filter fun otherColumn =>
      atomIndex ∈ datumTightSupport tightDir (basisLabel otherColumn) := by
    rw [huniv]
    exact Finset.mem_univ _
  exact (Finset.mem_filter.mp hmem).2

/-- The trivial multiplicity cap: at most every basis slot. -/
theorem basisSupportMultiplicity_le_basisCount
    (basisLabel : Fin basisCount → activeIndex) (atomIndex : Fin size) :
    basisSupportMultiplicity tightDir basisLabel atomIndex ≤ basisCount := by
  classical
  rw [basisSupportMultiplicity]
  have hcap := Finset.card_filter_le (Finset.univ : Finset (Fin basisCount))
    (fun columnIndex => atomIndex ∈ datumTightSupport tightDir
      (basisLabel columnIndex))
  simpa using hcap

/-! ## Layer 2 — the rank-five multiplicity census -/

/-- The rank-five dense double count: the multiplicities sum to
fifteen. -/
theorem RankFiveFrame.dense_multiplicity_sum {crux : SixThreeCrux}
    (frame : RankFiveFrame crux)
    (hthree : ∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3) :
    ∑ atomIndex : Fin 6, basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex = 15 := by
  rw [sum_basisSupportMultiplicity]
  rw [Finset.sum_congr rfl fun columnIndex _ => hthree columnIndex]
  simp

/-- **THE FIVE DOUBLES.**  A multiplicity-five atom at a dense rank-five
frame forces every other atom to multiplicity two exactly. -/
theorem RankFiveFrame.doubles_of_multiplicity_five {crux : SixThreeCrux}
    (frame : RankFiveFrame crux)
    (hthree : ∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3)
    (hmultTwo : ∀ atomIndex, 2 ≤ basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex)
    {heavyAtom : Fin 6}
    (hfive : basisSupportMultiplicity frame.tightDir frame.basisLabel
      heavyAtom = 5) :
    ∀ atomIndex, atomIndex ≠ heavyAtom →
      basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex
        = 2 := by
  classical
  intro otherAtom hne
  have hsum := frame.dense_multiplicity_sum hthree
  have hsplitHeavy := Finset.add_sum_erase Finset.univ
    (basisSupportMultiplicity frame.tightDir frame.basisLabel)
    (Finset.mem_univ heavyAtom)
  have hmemOther : otherAtom ∈ Finset.univ.erase heavyAtom :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
  have hsplitOther := Finset.add_sum_erase (Finset.univ.erase heavyAtom)
    (basisSupportMultiplicity frame.tightDir frame.basisLabel) hmemOther
  have hcard : ((Finset.univ.erase heavyAtom).erase otherAtom).card = 4 := by
    rw [Finset.card_erase_of_mem hmemOther,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hlower : ((Finset.univ.erase heavyAtom).erase otherAtom).card • 2
      ≤ ∑ atomIndex ∈ (Finset.univ.erase heavyAtom).erase otherAtom,
          basisSupportMultiplicity frame.tightDir frame.basisLabel
            atomIndex :=
    Finset.card_nsmul_le_sum _ _ _ (fun atomIndex _ => hmultTwo atomIndex)
  rw [hcard, smul_eq_mul] at hlower
  have hfloor := hmultTwo otherAtom
  omega

/-- A multiplicity-four atom at a dense rank-five frame caps every other
multiplicity at three. -/
theorem RankFiveFrame.le_three_of_multiplicity_four {crux : SixThreeCrux}
    (frame : RankFiveFrame crux)
    (hthree : ∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3)
    (hmultTwo : ∀ atomIndex, 2 ≤ basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex)
    {heavyAtom : Fin 6}
    (hfour : basisSupportMultiplicity frame.tightDir frame.basisLabel
      heavyAtom = 4) :
    ∀ atomIndex, atomIndex ≠ heavyAtom →
      basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex
        ≤ 3 := by
  classical
  intro otherAtom hne
  have hsum := frame.dense_multiplicity_sum hthree
  have hsplitHeavy := Finset.add_sum_erase Finset.univ
    (basisSupportMultiplicity frame.tightDir frame.basisLabel)
    (Finset.mem_univ heavyAtom)
  have hmemOther : otherAtom ∈ Finset.univ.erase heavyAtom :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
  have hsplitOther := Finset.add_sum_erase (Finset.univ.erase heavyAtom)
    (basisSupportMultiplicity frame.tightDir frame.basisLabel) hmemOther
  have hcard : ((Finset.univ.erase heavyAtom).erase otherAtom).card = 4 := by
    rw [Finset.card_erase_of_mem hmemOther,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hlower : ((Finset.univ.erase heavyAtom).erase otherAtom).card • 2
      ≤ ∑ atomIndex ∈ (Finset.univ.erase heavyAtom).erase otherAtom,
          basisSupportMultiplicity frame.tightDir frame.basisLabel
            atomIndex :=
    Finset.card_nsmul_le_sum _ _ _ (fun atomIndex _ => hmultTwo atomIndex)
  rw [hcard, smul_eq_mul] at hlower
  omega

/-- **THE TRIPLE EXTRACTION.**  A multiplicity-four atom at a dense
rank-five frame forces exactly one triple atom, and every remaining atom
is a double. -/
theorem RankFiveFrame.exists_triple_of_multiplicity_four
    {crux : SixThreeCrux} (frame : RankFiveFrame crux)
    (hthree : ∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3)
    (hmultTwo : ∀ atomIndex, 2 ≤ basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex)
    {heavyAtom : Fin 6}
    (hfour : basisSupportMultiplicity frame.tightDir frame.basisLabel
      heavyAtom = 4) :
    ∃ tripleAtom : Fin 6, tripleAtom ≠ heavyAtom
      ∧ basisSupportMultiplicity frame.tightDir frame.basisLabel tripleAtom
          = 3
      ∧ ∀ atomIndex, atomIndex ≠ heavyAtom → atomIndex ≠ tripleAtom →
          basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex
            = 2 := by
  classical
  have hle := frame.le_three_of_multiplicity_four hthree hmultTwo hfour
  have hsum := frame.dense_multiplicity_sum hthree
  have hsplitHeavy := Finset.add_sum_erase Finset.univ
    (basisSupportMultiplicity frame.tightDir frame.basisLabel)
    (Finset.mem_univ heavyAtom)
  have hsplitFilter := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.erase heavyAtom)
    (fun atomIndex => basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex = 3)
    (basisSupportMultiplicity frame.tightDir frame.basisLabel)
  have htripleSum : ∑ atomIndex ∈ (Finset.univ.erase heavyAtom).filter
      (fun atomIndex => basisSupportMultiplicity frame.tightDir
        frame.basisLabel atomIndex = 3),
      basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex
      = 3 * ((Finset.univ.erase heavyAtom).filter
        (fun atomIndex => basisSupportMultiplicity frame.tightDir
          frame.basisLabel atomIndex = 3)).card := by
    rw [Finset.sum_congr rfl (fun atomIndex hmem =>
      (Finset.mem_filter.mp hmem).2), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hdoubleSum : ∑ atomIndex ∈ (Finset.univ.erase heavyAtom).filter
      (fun atomIndex => ¬ basisSupportMultiplicity frame.tightDir
        frame.basisLabel atomIndex = 3),
      basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex
      = 2 * ((Finset.univ.erase heavyAtom).filter
        (fun atomIndex => ¬ basisSupportMultiplicity frame.tightDir
          frame.basisLabel atomIndex = 3)).card := by
    rw [Finset.sum_congr rfl (fun atomIndex hmem => ?_), Finset.sum_const,
      smul_eq_mul, mul_comm]
    have hmemErase := (Finset.mem_filter.mp hmem).1
    have hnotTriple := (Finset.mem_filter.mp hmem).2
    have hne := (Finset.mem_erase.mp hmemErase).1
    have hcap := hle atomIndex hne
    have hfloor := hmultTwo atomIndex
    omega
  have hcards := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.erase heavyAtom)
    (p := fun atomIndex => basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex = 3)
  have hcardErase : (Finset.univ.erase heavyAtom).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hone : ((Finset.univ.erase heavyAtom).filter
      (fun atomIndex => basisSupportMultiplicity frame.tightDir
        frame.basisLabel atomIndex = 3)).card = 1 := by
    rw [hcardErase] at hcards
    omega
  obtain ⟨tripleAtom, hsingleton⟩ := Finset.card_eq_one.mp hone
  have hmemTriple : tripleAtom ∈ (Finset.univ.erase heavyAtom).filter
      (fun atomIndex => basisSupportMultiplicity frame.tightDir
        frame.basisLabel atomIndex = 3) := by
    rw [hsingleton]
    exact Finset.mem_singleton_self _
  refine ⟨tripleAtom,
    (Finset.mem_erase.mp (Finset.mem_filter.mp hmemTriple).1).1,
    (Finset.mem_filter.mp hmemTriple).2, ?_⟩
  intro otherAtom hneHeavy hneTriple
  have hmemErase : otherAtom ∈ Finset.univ.erase heavyAtom :=
    Finset.mem_erase.mpr ⟨hneHeavy, Finset.mem_univ _⟩
  have hnotTriple : ¬ basisSupportMultiplicity frame.tightDir
      frame.basisLabel otherAtom = 3 := by
    intro hcontra
    have hmemFilter : otherAtom ∈ (Finset.univ.erase heavyAtom).filter
        (fun atomIndex => basisSupportMultiplicity frame.tightDir
          frame.basisLabel atomIndex = 3) :=
      Finset.mem_filter.mpr ⟨hmemErase, hcontra⟩
    rw [hsingleton, Finset.mem_singleton] at hmemFilter
    exact hneTriple hmemFilter
  have hcap := hle otherAtom hneHeavy
  have hfloor := hmultTwo otherAtom
  omega

/-- **THE THREE TRIPLES.**  A dense rank-five frame with every
multiplicity at most three carries exactly three triple atoms, and every
remaining atom is a double. -/
theorem RankFiveFrame.exists_three_triples_of_max_three
    {crux : SixThreeCrux} (frame : RankFiveFrame crux)
    (hthree : ∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3)
    (hmultTwo : ∀ atomIndex, 2 ≤ basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex)
    (hcap : ∀ atomIndex, basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex ≤ 3) :
    ∃ tripleOne tripleTwo tripleThree : Fin 6,
      tripleOne ≠ tripleTwo ∧ tripleOne ≠ tripleThree
      ∧ tripleTwo ≠ tripleThree
      ∧ basisSupportMultiplicity frame.tightDir frame.basisLabel tripleOne
          = 3
      ∧ basisSupportMultiplicity frame.tightDir frame.basisLabel tripleTwo
          = 3
      ∧ basisSupportMultiplicity frame.tightDir frame.basisLabel tripleThree
          = 3
      ∧ ∀ atomIndex, atomIndex ≠ tripleOne → atomIndex ≠ tripleTwo →
          atomIndex ≠ tripleThree →
          basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex
            = 2 := by
  classical
  have hsum := frame.dense_multiplicity_sum hthree
  have hsplitFilter := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin 6))
    (fun atomIndex => basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex = 3)
    (basisSupportMultiplicity frame.tightDir frame.basisLabel)
  have htripleSum : ∑ atomIndex ∈ Finset.univ.filter
      (fun atomIndex => basisSupportMultiplicity frame.tightDir
        frame.basisLabel atomIndex = 3),
      basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex
      = 3 * (Finset.univ.filter
        (fun atomIndex => basisSupportMultiplicity frame.tightDir
          frame.basisLabel atomIndex = 3)).card := by
    rw [Finset.sum_congr rfl (fun atomIndex hmem =>
      (Finset.mem_filter.mp hmem).2), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hdoubleSum : ∑ atomIndex ∈ Finset.univ.filter
      (fun atomIndex => ¬ basisSupportMultiplicity frame.tightDir
        frame.basisLabel atomIndex = 3),
      basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex
      = 2 * (Finset.univ.filter
        (fun atomIndex => ¬ basisSupportMultiplicity frame.tightDir
          frame.basisLabel atomIndex = 3)).card := by
    rw [Finset.sum_congr rfl (fun atomIndex hmem => ?_), Finset.sum_const,
      smul_eq_mul, mul_comm]
    have hnotTriple := (Finset.mem_filter.mp hmem).2
    have hcapAtom := hcap atomIndex
    have hfloor := hmultTwo atomIndex
    omega
  have hcards := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 6)))
    (p := fun atomIndex => basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex = 3)
  have hthreeCard : (Finset.univ.filter
      (fun atomIndex => basisSupportMultiplicity frame.tightDir
        frame.basisLabel atomIndex = 3)).card = 3 := by
    rw [Finset.card_univ, Fintype.card_fin] at hcards
    omega
  obtain ⟨tripleOne, tripleTwo, tripleThree, hOneTwo, hOneThree, hTwoThree,
    hset⟩ := Finset.card_eq_three.mp hthreeCard
  have hmemOf : ∀ atomIndex ∈ ({tripleOne, tripleTwo, tripleThree}
      : Finset (Fin 6)),
      basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex
        = 3 := by
    intro atomIndex hmem
    rw [← hset] at hmem
    exact (Finset.mem_filter.mp hmem).2
  refine ⟨tripleOne, tripleTwo, tripleThree, hOneTwo, hOneThree, hTwoThree,
    hmemOf tripleOne (Finset.mem_insert_self _ _),
    hmemOf tripleTwo (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
    hmemOf tripleThree (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))), ?_⟩
  intro otherAtom hneOne hneTwo hneThree
  have hnotTriple : ¬ basisSupportMultiplicity frame.tightDir
      frame.basisLabel otherAtom = 3 := by
    intro hcontra
    have hmemFilter : otherAtom ∈ Finset.univ.filter
        (fun atomIndex => basisSupportMultiplicity frame.tightDir
          frame.basisLabel atomIndex = 3) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcontra⟩
    rw [hset] at hmemFilter
    rcases Finset.mem_insert.mp hmemFilter with hcase | hcase
    · exact hneOne hcase
    rcases Finset.mem_insert.mp hcase with hcase' | hcase'
    · exact hneTwo hcase'
    · exact hneThree (Finset.mem_singleton.mp hcase')
  have hcapAtom := hcap otherAtom
  have hfloor := hmultTwo otherAtom
  omega

/-! ## Layer 3 — the rank-five profile closures and the dispatch -/

/-- **PROFILE CLOSURE A.**  The heavy-five profile dies: five doubles
around one full-carrier atom, with the landed pins in hand — the
coefficient trace is two and the heavy shifted weight is zero. -/
def RankFiveDenseHeavyFiveClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankFiveFrame crux) (heavyAtom : Fin 6),
    (∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3) →
    basisSupportMultiplicity frame.tightDir frame.basisLabel heavyAtom
      = 5 →
    (∀ atomIndex, atomIndex ≠ heavyAtom →
      basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex
        = 2) →
    Matrix.trace frame.coeff = 2 →
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight heavyAtom = 0 →
    False

/-- **PROFILE CLOSURE B.**  The heavy-four profile dies: one
multiplicity-four atom, one triple atom, four doubles. -/
def RankFiveDenseHeavyFourClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankFiveFrame crux)
    (heavyAtom tripleAtom : Fin 6),
    (∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3) →
    basisSupportMultiplicity frame.tightDir frame.basisLabel heavyAtom
      = 4 →
    tripleAtom ≠ heavyAtom →
    basisSupportMultiplicity frame.tightDir frame.basisLabel tripleAtom
      = 3 →
    (∀ atomIndex, atomIndex ≠ heavyAtom → atomIndex ≠ tripleAtom →
      basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex
        = 2) →
    False

/-- **PROFILE CLOSURE C.**  The three-triple profile dies: three triple
atoms and three doubles. -/
def RankFiveDenseThreeTriplesClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankFiveFrame crux)
    (tripleOne tripleTwo tripleThree : Fin 6),
    (∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3) →
    tripleOne ≠ tripleTwo → tripleOne ≠ tripleThree →
    tripleTwo ≠ tripleThree →
    basisSupportMultiplicity frame.tightDir frame.basisLabel tripleOne
      = 3 →
    basisSupportMultiplicity frame.tightDir frame.basisLabel tripleTwo
      = 3 →
    basisSupportMultiplicity frame.tightDir frame.basisLabel tripleThree
      = 3 →
    (∀ atomIndex, atomIndex ≠ tripleOne → atomIndex ≠ tripleTwo →
      atomIndex ≠ tripleThree →
      basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex
        = 2) →
    False

/-- **THE RANK-FIVE DISPATCH.**  The three profile closures imply the
rank-five dense closure.  The dispatch derives the exact profile from
the double count, and hands profile A the landed trace and weight
pins. -/
theorem rankFiveDenseClosed_of_profile_closures
    (killHeavyFive : RankFiveDenseHeavyFiveClosed)
    (killHeavyFour : RankFiveDenseHeavyFourClosed)
    (killThreeTriples : RankFiveDenseThreeTriplesClosed) :
    RankFiveDenseClosed := by
  intro crux frame heavyAtom hthree hmultTwo _hheavy
  classical
  by_cases hfive : ∃ atomIndex, basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex = 5
  · obtain ⟨atomFive, hatomFive⟩ := hfive
    have hdoubles := frame.doubles_of_multiplicity_five hthree hmultTwo
      hatomFive
    have htrace := frame.trace_eq_two_of_multiplicity_five hatomFive
    have hdiagZero := full_carrier_diagonal_zero frame.hdata frame.basisLabel
      frame.hrepresentation frame.hidempotent frame.hmemAll frame.hvalueNeg
      (0 : Fin 5)
      (forall_carrier_of_multiplicity_eq_card hatomFive)
    exact killHeavyFive crux frame atomFive hthree hatomFive hdoubles htrace
      hdiagZero
  · by_cases hfour : ∃ atomIndex, basisSupportMultiplicity frame.tightDir
        frame.basisLabel atomIndex = 4
    · obtain ⟨atomFour, hatomFour⟩ := hfour
      obtain ⟨tripleAtom, hneTriple, htripleMult, hdoubles⟩ :=
        frame.exists_triple_of_multiplicity_four hthree hmultTwo hatomFour
      exact killHeavyFour crux frame atomFour tripleAtom hthree hatomFour
        hneTriple htripleMult hdoubles
    · have hcap : ∀ atomIndex, basisSupportMultiplicity frame.tightDir
          frame.basisLabel atomIndex ≤ 3 := by
        intro atomIndex
        have hle := basisSupportMultiplicity_le_basisCount
          (tightDir := frame.tightDir) frame.basisLabel atomIndex
        have hnotFive : basisSupportMultiplicity frame.tightDir
            frame.basisLabel atomIndex ≠ 5 :=
          fun hcontra => hfive ⟨atomIndex, hcontra⟩
        have hnotFour : basisSupportMultiplicity frame.tightDir
            frame.basisLabel atomIndex ≠ 4 :=
          fun hcontra => hfour ⟨atomIndex, hcontra⟩
        omega
      obtain ⟨tripleOne, tripleTwo, tripleThree, hOneTwo, hOneThree,
        hTwoThree, hmultOne, hmultTwo', hmultThree, hdoubles⟩ :=
        frame.exists_three_triples_of_max_three hthree hmultTwo hcap
      exact killThreeTriples crux frame tripleOne tripleTwo tripleThree
        hthree hOneTwo hOneThree hTwoThree hmultOne hmultTwo' hmultThree
        hdoubles

/-! ## Layer 4 — the rank-six multiplicity census -/

/-- The rank-six dense double count: the multiplicities sum to
eighteen. -/
theorem RankSixFrame.dense_multiplicity_sum {crux : SixThreeCrux}
    (frame : RankSixFrame crux)
    (hthree : ∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3) :
    ∑ atomIndex : Fin 6, basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex = 18 := by
  rw [sum_basisSupportMultiplicity]
  rw [Finset.sum_congr rfl fun columnIndex _ => hthree columnIndex]
  simp

/-- **THE ALL-TRIPLE PROFILE.**  A dense rank-six frame with every
multiplicity at most three carries every atom at multiplicity three
exactly: the `(3, 3, 3, 3, 3, 3)` vector. -/
theorem RankSixFrame.all_triples_of_max_three {crux : SixThreeCrux}
    (frame : RankSixFrame crux)
    (hthree : ∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3)
    (hmultTwo : ∀ atomIndex, 2 ≤ basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex)
    (hcap : ∀ atomIndex, basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex ≤ 3) :
    ∀ atomIndex, basisSupportMultiplicity frame.tightDir frame.basisLabel
      atomIndex = 3 := by
  classical
  intro atomIndex
  have hsum := frame.dense_multiplicity_sum hthree
  have hsplit := Finset.add_sum_erase Finset.univ
    (basisSupportMultiplicity frame.tightDir frame.basisLabel)
    (Finset.mem_univ atomIndex)
  have hcard : (Finset.univ.erase atomIndex).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hupper : ∑ otherAtom ∈ Finset.univ.erase atomIndex,
      basisSupportMultiplicity frame.tightDir frame.basisLabel otherAtom
      ≤ (Finset.univ.erase atomIndex).card • 3 :=
    Finset.sum_le_card_nsmul _ _ _ (fun otherAtom _ => hcap otherAtom)
  rw [hcard, smul_eq_mul] at hupper
  have hfloor := hmultTwo atomIndex
  have hcapAtom := hcap atomIndex
  omega

/-! ## Layer 5 — the rank-six profile closures and the dispatch -/

/-- **PROFILE CLOSURE A.**  The rank-six heavy-five profile dies: some
atom sits in five of the six supports. -/
def RankSixDenseHeavyFiveClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankSixFrame crux) (heavyAtom : Fin 6),
    (∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3) →
    (∀ atomIndex, 2 ≤ basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex) →
    basisSupportMultiplicity frame.tightDir frame.basisLabel heavyAtom
      = 5 →
    False

/-- **PROFILE CLOSURE B.**  The rank-six heavy-four profile dies: the
maximum multiplicity is four. -/
def RankSixDenseHeavyFourClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankSixFrame crux) (heavyAtom : Fin 6),
    (∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3) →
    (∀ atomIndex, 2 ≤ basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex) →
    (∀ atomIndex, basisSupportMultiplicity frame.tightDir frame.basisLabel
      atomIndex ≤ 4) →
    basisSupportMultiplicity frame.tightDir frame.basisLabel heavyAtom
      = 4 →
    False

/-- **PROFILE CLOSURE C.**  The rank-six all-triple profile dies: every
atom sits in exactly three supports.  The complex trine shadow lives in
this cell, thus every kill chain here must end real-only. -/
def RankSixDenseAllTriplesClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankSixFrame crux),
    (∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3) →
    (∀ atomIndex, basisSupportMultiplicity frame.tightDir frame.basisLabel
      atomIndex = 3) →
    False

/-- **THE RANK-SIX DISPATCH.**  The three profile closures imply the
rank-six dense closure.  The landed quantization cap excludes
multiplicity six, and the double count pins the all-triple profile. -/
theorem rankSixDenseClosed_of_profile_closures
    (killHeavyFive : RankSixDenseHeavyFiveClosed)
    (killHeavyFour : RankSixDenseHeavyFourClosed)
    (killAllTriples : RankSixDenseAllTriplesClosed) :
    RankSixDenseClosed := by
  intro crux frame heavyAtom hthree hmultTwo _hheavy
  classical
  by_cases hfive : ∃ atomIndex, basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex = 5
  · obtain ⟨atomFive, hatomFive⟩ := hfive
    exact killHeavyFive crux frame atomFive hthree hmultTwo hatomFive
  · by_cases hfour : ∃ atomIndex, basisSupportMultiplicity frame.tightDir
        frame.basisLabel atomIndex = 4
    · obtain ⟨atomFour, hatomFour⟩ := hfour
      have hcap : ∀ atomIndex, basisSupportMultiplicity frame.tightDir
          frame.basisLabel atomIndex ≤ 4 := by
        intro atomIndex
        have hle := frame.basisSupportMultiplicity_le_five atomIndex
        have hnotFive : basisSupportMultiplicity frame.tightDir
            frame.basisLabel atomIndex ≠ 5 :=
          fun hcontra => hfive ⟨atomIndex, hcontra⟩
        omega
      exact killHeavyFour crux frame atomFour hthree hmultTwo hcap hatomFour
    · have hcap : ∀ atomIndex, basisSupportMultiplicity frame.tightDir
          frame.basisLabel atomIndex ≤ 3 := by
        intro atomIndex
        have hle := frame.basisSupportMultiplicity_le_five atomIndex
        have hnotFive : basisSupportMultiplicity frame.tightDir
            frame.basisLabel atomIndex ≠ 5 :=
          fun hcontra => hfive ⟨atomIndex, hcontra⟩
        have hnotFour : basisSupportMultiplicity frame.tightDir
            frame.basisLabel atomIndex ≠ 4 :=
          fun hcontra => hfour ⟨atomIndex, hcontra⟩
        omega
      exact killAllTriples crux frame hthree
        (frame.all_triples_of_max_three hthree hmultTwo hcap)

end Gtz

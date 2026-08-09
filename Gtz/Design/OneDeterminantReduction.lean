import Gtz.Design.LivePairExistence
import Gtz.Design.DepthCapAxisParseval
import Gtz.Design.PairCapEngine
import Gtz.Design.LineClassObstructions
import Gtz.Design.LineFreeConicBridge
import Gtz.Design.ThreeLinesTriangleCell
import Gtz.Reduction.RealVolumeFloor
import Gtz.Reduction.ConverseBridge
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.RayleighCertificate
import Gtz.Quantitative.DesignQuadraticFloors
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The one-determinant reduction

The shared Phase-2 substrate.

* **Part 1 -- the free composition.**  Every rank-three weighted design owns a
  pair of labels and a plane on which that pair strictly dominates every nonzero
  probe.  Unconditional: no heaviness, no primitivity, no pattern, no bound on
  the number of atoms.  This is `Gtz.exists_pos_pairGapExcessOf` packaged into
  `Gtz.IsLivePair` and pushed through `Gtz.dotProduct_self_lt_pair_of_isLivePair`.

* **Part 2 -- Sylvester runs backwards.**  The converse of
  `Gtz.posDef_of_leadingMinors_fin_three`: a positive definite explicit `3x3`
  has all three leading minors positive.  Read on `Gtz.tripleGapMatrix` this
  says a STRICTLY dominating triple always carries a live pair with positive
  tie leg, so the sufficient condition of Part 3 is also necessary.

* **Part 3 -- the one-determinant reduction.**  Strict domination of SOME
  card-three subset is EQUIVALENT to the existence of a live pair together with
  one third label at which `Gtz.discriminantTie` is strictly positive.  Since
  the live pair is free (Part 1), every obligation of the shape "there exists a
  card-three subset with positive definite gap" reduces to producing ONE label
  with a positive tie leg.  The reduction is packaged per obligation, in the
  hypothesis shape of the landed
  `Gtz.patternHeavyWeakToStrict_of_capBlindSpot`, and once more with the pair
  cap engine's blind spot carved out on top.

* **Part 4 -- the excess split, on both sides.**  The design-side twin of the
  landed `Gtz.directionChartGap_eq_excessSplit`: selected atoms contribute with
  their COMPLEMENTARY weight, outside atoms subtract with their OWN weight, and
  the total moment matrix disappears.  Strict and weak domination are read off
  it as sign conditions.

* **Part 5 -- the chart-to-design dictionary, square-root free.**  Every chart
  point whose moment matrix is positive definite IS a weighted design: one
  invertible congruence, produced by the landed `Gtz.exists_congruence_to_one`,
  carries the chart gap of every subset onto the design gap of the same subset.
  No matrix square root is built.  The moment hypothesis is then DISCHARGED at
  both live charts, so `Gtz.DirectionChartIsTieFree` at `Gtz.kFourDirection` and
  at `Gtz.threeLinesDirection` reduces to a design-level statement with no chart
  data in it.

* **Part 6 -- non-vacuity.**  The tetrahedron carries a live pair and no
  positive tie leg, so the residual is exactly false at the ties; and the chart
  realization fires at the canonical inhabitant of the K4 residual band.
-/

namespace Gtz

open Matrix Finset

variable {size rank : ℕ}

/-! ## Part 1: every rank-three design owns a plane-dominating pair -/

/-- The three conjuncts `Gtz.exists_pos_pairGapExcessOf` produces are literally
`Gtz.IsLivePair`, so the existence statement repackages with no work. -/
theorem exists_isLivePair (design : WeightedDesign size rank) (hrank : 3 ≤ rank) :
    ∃ firstLabel secondLabel : Fin size, firstLabel ≠ secondLabel
      ∧ IsLivePair design firstLabel secondLabel := by
  obtain ⟨firstLabel, secondLabel, hdistinct, hfirstPos, hsecondPos, hminorPos⟩ :=
    exists_pos_pairGapExcessOf design hrank
  exact ⟨firstLabel, secondLabel, hdistinct, hfirstPos, hsecondPos, hminorPos⟩

/-- The rank-three instance. -/
theorem exists_isLivePair_rankThree (design : WeightedDesign size 3) :
    ∃ firstLabel secondLabel : Fin size, firstLabel ≠ secondLabel
      ∧ IsLivePair design firstLabel secondLabel :=
  exists_isLivePair design (le_refl 3)

/-- **TARGET A.  EVERY RANK-THREE DESIGN STRICTLY DOMINATES A PLANE.**  Two
distinct labels and a genuine plane -- the orthogonal complement of the pair's
own cross axis, which is nonzero -- on which the two atoms alone already beat
the identity at every nonzero probe.  Unconditional. -/
theorem exists_pair_dominating_crossAxisPlane (design : WeightedDesign size 3) :
    ∃ firstLabel secondLabel : Fin size, firstLabel ≠ secondLabel
      ∧ crossAxis design firstLabel secondLabel ≠ 0
      ∧ ∀ probeVec : Fin 3 → ℝ,
          probeVec ⬝ᵥ crossAxis design firstLabel secondLabel = 0 → probeVec ≠ 0 →
            probeVec ⬝ᵥ probeVec
              < (design.atom firstLabel ⬝ᵥ probeVec) ^ 2
                + (design.atom secondLabel ⬝ᵥ probeVec) ^ 2 := by
  obtain ⟨firstLabel, secondLabel, hdistinct, hlive⟩ := exists_isLivePair_rankThree design
  exact ⟨firstLabel, secondLabel, hdistinct, crossAxis_ne_zero_of_isLivePair design hlive,
    fun probeVec hplanar hprobeNe =>
      dotProduct_self_lt_pair_of_isLivePair design hlive hplanar hprobeNe⟩

/-- **TARGET A, matrix form.**  The same pair, read as a strict quadratic-form
inequality on the pair's own gap `S_{i,j} - 1`. -/
theorem exists_pair_posDef_gapForm_on_crossAxisPlane (design : WeightedDesign size 3) :
    ∃ firstLabel secondLabel : Fin size, firstLabel ≠ secondLabel
      ∧ crossAxis design firstLabel secondLabel ≠ 0
      ∧ ∀ probeVec : Fin 3 → ℝ,
          probeVec ⬝ᵥ crossAxis design firstLabel secondLabel = 0 → probeVec ≠ 0 →
            0 < probeVec ⬝ᵥ ((subsetSum design {firstLabel, secondLabel} - 1) *ᵥ probeVec) := by
  obtain ⟨firstLabel, secondLabel, hdistinct, hlive⟩ := exists_isLivePair_rankThree design
  exact ⟨firstLabel, secondLabel, hdistinct, crossAxis_ne_zero_of_isLivePair design hlive,
    fun probeVec hplanar hprobeNe =>
      pos_gapForm_pair_of_isLivePair design hlive hdistinct hplanar hprobeNe⟩

/-! ## Part 2: Sylvester runs backwards at `Fin 3` -/

/-- The corner of a positive definite explicit `3x3` is positive: read the
quadratic form at the first basis vector. -/
theorem posDef_fin_three_corner_pos {entryOneOne entryOneTwo entryOneThree entryTwoTwo
    entryTwoThree entryThreeThree : ℝ}
    (hposDef : (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef) :
    0 < entryOneOne := by
  have hbasisNe : (![1, 0, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hfirst := congrFun hzero 0
    simp at hfirst
  have hvalue := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hbasisNe
  rw [star_trivial] at hvalue
  have hform : (![1, 0, 0] : Fin 3 → ℝ)
        ⬝ᵥ ((!![entryOneOne, entryOneTwo, entryOneThree;
            entryOneTwo, entryTwoTwo, entryTwoThree;
            entryOneThree, entryTwoThree, entryThreeThree]
          : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ![1, 0, 0]) = entryOneOne := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  linarith [hform ▸ hvalue]

/-- The second diagonal entry of a positive definite explicit `3x3` is positive:
read the quadratic form at the second basis vector. -/
theorem posDef_fin_three_secondDiag_pos {entryOneOne entryOneTwo entryOneThree entryTwoTwo
    entryTwoThree entryThreeThree : ℝ}
    (hposDef : (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef) :
    0 < entryTwoTwo := by
  have hbasisNe : (![0, 1, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hsecond := congrFun hzero 1
    simp at hsecond
  have hvalue := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hbasisNe
  rw [star_trivial] at hvalue
  have hform : (![0, 1, 0] : Fin 3 → ℝ)
        ⬝ᵥ ((!![entryOneOne, entryOneTwo, entryOneThree;
            entryOneTwo, entryTwoTwo, entryTwoThree;
            entryOneThree, entryTwoThree, entryThreeThree]
          : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ![0, 1, 0]) = entryTwoTwo := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  linarith [hform ▸ hvalue]

/-- The leading two-by-two minor of a positive definite explicit `3x3` is
positive: read the quadratic form at the in-plane witness
`(entryOneTwo, -entryOneOne, 0)`. -/
theorem posDef_fin_three_blockMinor_pos {entryOneOne entryOneTwo entryOneThree entryTwoTwo
    entryTwoThree entryThreeThree : ℝ}
    (hposDef : (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef) :
    0 < entryOneOne * entryTwoTwo - entryOneTwo ^ 2 := by
  have hcorner : 0 < entryOneOne := posDef_fin_three_corner_pos hposDef
  have hwitnessNe : (![entryOneTwo, -entryOneOne, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hsecond := congrFun hzero 1
    simp at hsecond
    exact absurd hsecond (ne_of_gt hcorner)
  have hvalue := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hwitnessNe
  rw [star_trivial] at hvalue
  have hform : (![entryOneTwo, -entryOneOne, 0] : Fin 3 → ℝ)
        ⬝ᵥ ((!![entryOneOne, entryOneTwo, entryOneThree;
            entryOneTwo, entryTwoTwo, entryTwoThree;
            entryOneThree, entryTwoThree, entryThreeThree]
          : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ![entryOneTwo, -entryOneOne, 0])
      = entryOneOne * (entryOneOne * entryTwoTwo - entryOneTwo ^ 2) := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    ring
  nlinarith [hform ▸ hvalue]

/-- The determinant of a positive definite explicit `3x3` is positive. -/
theorem posDef_fin_three_det_pos {entryOneOne entryOneTwo entryOneThree entryTwoTwo
    entryTwoThree entryThreeThree : ℝ}
    (hposDef : (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef) :
    0 < entryOneOne * entryTwoTwo * entryThreeThree - entryOneOne * entryTwoThree ^ 2
      - entryOneTwo ^ 2 * entryThreeThree
      + 2 * entryOneTwo * entryOneThree * entryTwoThree
      - entryOneThree ^ 2 * entryTwoTwo := by
  have hdet := hposDef.det_pos
  rw [Matrix.det_fin_three] at hdet
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.of_apply] at hdet
  nlinarith [hdet]

/-- **THE CONVERSE OF THE LANDED SYLVESTER STEP.**  Positive definiteness of an
explicit symmetric `3x3` returns all three leading minors, so
`Gtz.posDef_of_leadingMinors_fin_three` is an equivalence. -/
theorem leadingMinors_pos_iff_posDef_fin_three (entryOneOne entryOneTwo entryOneThree
    entryTwoTwo entryTwoThree entryThreeThree : ℝ) :
    (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef
      ↔ (0 < entryOneOne ∧ 0 < entryOneOne * entryTwoTwo - entryOneTwo ^ 2
          ∧ 0 < entryOneOne * entryTwoTwo * entryThreeThree - entryOneOne * entryTwoThree ^ 2
            - entryOneTwo ^ 2 * entryThreeThree
            + 2 * entryOneTwo * entryOneThree * entryTwoThree
            - entryOneThree ^ 2 * entryTwoTwo) :=
  ⟨fun hposDef => ⟨posDef_fin_three_corner_pos hposDef, posDef_fin_three_blockMinor_pos hposDef,
      posDef_fin_three_det_pos hposDef⟩,
    fun hminors => posDef_of_leadingMinors_fin_three entryOneOne entryOneTwo entryOneThree
      entryTwoTwo entryTwoThree entryThreeThree hminors.1 hminors.2.1 hminors.2.2⟩

/-! ### The converse, read on the triple gap matrix -/

/-- A strictly dominating ordered triple has a heavy pivot. -/
theorem heavyExcess_pos_of_posDef_tripleGapMatrix (design : WeightedDesign size 3)
    (pivotLabel pairFirst pairSecond : Fin size)
    (hposDef : (tripleGapMatrix design pivotLabel pairFirst pairSecond).PosDef) :
    0 < heavyExcess design pivotLabel :=
  posDef_fin_three_corner_pos (by simpa only [tripleGapMatrix] using hposDef)

/-- A strictly dominating ordered triple has a live leading pair. -/
theorem pairGapExcessOf_pos_of_posDef_tripleGapMatrix (design : WeightedDesign size 3)
    (pivotLabel pairFirst pairSecond : Fin size)
    (hposDef : (tripleGapMatrix design pivotLabel pairFirst pairSecond).PosDef) :
    0 < pairGapExcessOf design pivotLabel pairFirst := by
  have hminor := posDef_fin_three_blockMinor_pos (by simpa only [tripleGapMatrix] using hposDef)
  simpa only [pairGapExcessOf, gapExcessOf_eq_heavyExcess, gapPairingOf_eq_atomPairing]
    using hminor

/-- A strictly dominating ordered triple has a strictly positive tie leg. -/
theorem discriminantTie_pos_of_posDef_tripleGapMatrix (design : WeightedDesign size 3)
    (pivotLabel pairFirst pairSecond : Fin size)
    (hposDef : (tripleGapMatrix design pivotLabel pairFirst pairSecond).PosDef) :
    0 < discriminantTie design pivotLabel pairFirst pairSecond := by
  rw [← det_tripleGapMatrix]
  exact hposDef.det_pos

/-- **THE LEADING PAIR OF A STRICT DOMINATOR IS LIVE.**  Both its atoms are
heavy and its two-by-two gap minor is positive, so the free live pair of Part 1
is not a special choice: EVERY strictly dominating triple exhibits one. -/
theorem isLivePair_of_posDef_tripleGapMatrix (design : WeightedDesign size 3)
    (pivotLabel pairFirst pairSecond : Fin size)
    (hposDef : (tripleGapMatrix design pivotLabel pairFirst pairSecond).PosDef) :
    IsLivePair design pivotLabel pairFirst := by
  refine ⟨?_, ?_, pairGapExcessOf_pos_of_posDef_tripleGapMatrix design pivotLabel pairFirst
    pairSecond hposDef⟩
  · rw [gapExcessOf_eq_heavyExcess]
    exact heavyExcess_pos_of_posDef_tripleGapMatrix design pivotLabel pairFirst pairSecond hposDef
  · rw [gapExcessOf_eq_heavyExcess]
    exact posDef_fin_three_secondDiag_pos (by simpa only [tripleGapMatrix] using hposDef)

/-! ## Part 3: the one-determinant reduction -/

/-- Three pairwise distinct labels make a card-three subset. -/
theorem card_labelTriple_eq_three {firstLabel secondLabel thirdLabel : Fin size}
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel) :
    ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
    Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]

/-- **The residual, named.**  A design carries a LIVE PAIR WITH POSITIVE TIE
when some live pair admits a third label whose tie leg is strictly positive.
By Part 2 this is not a strengthening of strict domination -- it is a
restatement of it in scalar coordinates. -/
def HasLivePairPositiveTie (design : WeightedDesign size 3) : Prop :=
  ∃ pivotLabel pairFirst pairSecond : Fin size,
    pivotLabel ≠ pairFirst ∧ pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
      ∧ IsLivePair design pivotLabel pairFirst
      ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond

/-- **THE PRODUCER.**  A live pair plus one positive tie leg is a strictly
dominating card-three subset. -/
theorem exists_posDef_cardThree_of_hasLivePairPositiveTie (design : WeightedDesign size 3)
    (hresidual : HasLivePairPositiveTie design) :
    ∃ selected : Finset (Fin size), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef := by
  obtain ⟨pivotLabel, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
    ⟨hpivotHeavy, -, hminor⟩, hdeterminant⟩ := hresidual
  rw [gapExcessOf_eq_heavyExcess] at hpivotHeavy
  exact ⟨{pivotLabel, pairFirst, pairSecond},
    card_labelTriple_eq_three hpivotFirst hpivotSecond hpairDistinct,
    posDef_subsetSum_sub_one_of_livePair design hpivotFirst hpivotSecond hpairDistinct
      hpivotHeavy hminor hdeterminant⟩

/-- **THE CONVERSE.**  A strictly dominating card-three subset always exhibits a
live pair with positive tie leg, so the producer above loses nothing. -/
theorem hasLivePairPositiveTie_of_exists_posDef_cardThree (design : WeightedDesign size 3)
    (hstrict : ∃ selected : Finset (Fin size), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef) :
    HasLivePairPositiveTie design := by
  obtain ⟨selected, hcard, hposDef⟩ := hstrict
  obtain ⟨pivotLabel, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct, hset⟩ :=
    Finset.card_eq_three.mp hcard
  subst hset
  have hgap : (tripleGapMatrix design pivotLabel pairFirst pairSecond).PosDef :=
    (posDef_subsetSum_sub_one_iff_posDef_tripleGapMatrix design hpivotFirst hpivotSecond
      hpairDistinct).mp hposDef
  exact ⟨pivotLabel, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
    isLivePair_of_posDef_tripleGapMatrix design pivotLabel pairFirst pairSecond hgap,
    discriminantTie_pos_of_posDef_tripleGapMatrix design pivotLabel pairFirst pairSecond hgap⟩

/-- **THE ONE-DETERMINANT REDUCTION, as an equivalence.**  Strict domination of
SOME card-three subset IS the existence of a live pair with one strictly
positive tie leg.  The live pair half is free
(`Gtz.exists_isLivePair_rankThree`), so the whole content of every
"there exists a strictly dominating triple" obligation is the SIGN OF ONE
DETERMINANT at one completing label. -/
theorem hasLivePairPositiveTie_iff_exists_posDef_cardThree (design : WeightedDesign size 3) :
    HasLivePairPositiveTie design
      ↔ ∃ selected : Finset (Fin size), selected.card = 3
          ∧ (subsetSum design selected - 1).PosDef :=
  ⟨exists_posDef_cardThree_of_hasLivePairPositiveTie design,
    hasLivePairPositiveTie_of_exists_posDef_cardThree design⟩

/-- The convenient hypothesis shape: it is enough that EVERY live pair completes
to a positive tie leg, because Part 1 guarantees at least one live pair. -/
theorem exists_posDef_cardThree_of_forall_livePair (design : WeightedDesign size 3)
    (hcomplete : ∀ pivotLabel pairFirst : Fin size, pivotLabel ≠ pairFirst →
      IsLivePair design pivotLabel pairFirst →
      ∃ pairSecond : Fin size, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
        ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond) :
    ∃ selected : Finset (Fin size), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef := by
  obtain ⟨pivotLabel, pairFirst, hdistinct, hlive⟩ := exists_isLivePair_rankThree design
  obtain ⟨pairSecond, hpivotSecond, hpairDistinct, hdeterminant⟩ :=
    hcomplete pivotLabel pairFirst hdistinct hlive
  exact exists_posDef_cardThree_of_hasLivePairPositiveTie design
    ⟨pivotLabel, pairFirst, pairSecond, hdistinct, hpivotSecond, hpairDistinct, hlive,
      hdeterminant⟩

/-! ### The reduction, packaged per obligation

Hypothesis shape copied from the landed
`Gtz.patternHeavyWeakToStrict_of_capBlindSpot`: the obligation follows from a
statement about a named smaller residual. -/

/-- **TARGET B(i).**  `Gtz.PatternHeavyWeakToStrict` at an ARBITRARY line
pattern follows from the one-determinant residual: at every heavy,
weakly-dominated design of the stratum, EVERY live pair completes to a strictly
positive tie leg.  The live pair itself never has to be produced -- Part 1 hands
one over for free. -/
theorem patternHeavyWeakToStrict_of_livePairTie (pattern : LinePattern size)
    (hresidual : ∀ design : WeightedDesign size 3, HasLinePattern design pattern →
      (∀ label : Fin size, 1 ≤ leverageOf (design.atom label)) →
      (∃ dominator : Finset (Fin size), dominator.card = 3 ∧ Dominates design dominator) →
      ∀ pivotLabel pairFirst : Fin size, pivotLabel ≠ pairFirst →
        IsLivePair design pivotLabel pairFirst →
        ∃ pairSecond : Fin size, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond) :
    PatternHeavyWeakToStrict pattern := fun design hpattern hheavy hweak =>
  exists_posDef_cardThree_of_forall_livePair design (hresidual design hpattern hheavy hweak)

/-- The same reduction against the weakest residual: SOME live pair completes. -/
theorem patternHeavyWeakToStrict_of_hasLivePairPositiveTie (pattern : LinePattern size)
    (hresidual : ∀ design : WeightedDesign size 3, HasLinePattern design pattern →
      (∀ label : Fin size, 1 ≤ leverageOf (design.atom label)) →
      (∃ dominator : Finset (Fin size), dominator.card = 3 ∧ Dominates design dominator) →
      HasLivePairPositiveTie design) :
    PatternHeavyWeakToStrict pattern := fun design hpattern hheavy hweak =>
  exists_posDef_cardThree_of_hasLivePairPositiveTie design
    (hresidual design hpattern hheavy hweak)

/-- **The two engines stacked.**  Outside the pair cap's blind spot the landed
`Gtz.exists_posDef_triple_of_pairCapExcess` already fires, so the one-determinant
residual only has to be supplied ON the blind spot.  Strictly smaller region than
either reduction alone. -/
theorem patternHeavyWeakToStrict_of_capBlindSpot_livePairTie (pattern : LinePattern size)
    (hresidual : ∀ design : WeightedDesign size 3, HasLinePattern design pattern →
      (∀ label : Fin size, 1 ≤ leverageOf (design.atom label)) →
      IsCapBlindSpot design →
      (∃ dominator : Finset (Fin size), dominator.card = 3 ∧ Dominates design dominator) →
      ∀ pivotLabel pairFirst : Fin size, pivotLabel ≠ pairFirst →
        IsLivePair design pivotLabel pairFirst →
        ∃ pairSecond : Fin size, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond) :
    PatternHeavyWeakToStrict pattern :=
  patternHeavyWeakToStrict_of_capBlindSpot pattern
    fun design hpattern hheavy hblind hweak =>
      exists_posDef_cardThree_of_forall_livePair design
        (hresidual design hpattern hheavy hblind hweak)

/-- **TARGET B(ii).**  The U(3,6) residual
`Gtz.BaseTripleTightLineFreeOffConicWeakToStrict` under the same reduction: at a
line-free off-conic design with the base triple weakly dominating along an
explicit tight direction, EVERY live pair completes to a positive tie leg. -/
theorem baseTripleTightLineFreeOffConicWeakToStrict_of_livePairTie
    (hresidual : ∀ (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ),
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
      HasNoCommonQuadric design.atom →
      Dominates design {0, 1, 2} →
      tightDir ≠ 0 →
      tightDir ⬝ᵥ ((subsetSum design {0, 1, 2} - 1) *ᵥ tightDir) = 0 →
      ∀ pivotLabel pairFirst : Fin 6, pivotLabel ≠ pairFirst →
        IsLivePair design pivotLabel pairFirst →
        ∃ pairSecond : Fin 6, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond) :
    BaseTripleTightLineFreeOffConicWeakToStrict :=
  fun design tightDir hlineFree hoffConic hdominates htightNe htight =>
    exists_posDef_cardThree_of_forall_livePair design
      (hresidual design tightDir hlineFree hoffConic hdominates htightNe htight)

/-- The U(3,6) reduction against the weakest residual. -/
theorem baseTripleTightLineFreeOffConicWeakToStrict_of_hasLivePairPositiveTie
    (hresidual : ∀ (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ),
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
      HasNoCommonQuadric design.atom →
      Dominates design {0, 1, 2} →
      tightDir ≠ 0 →
      tightDir ⬝ᵥ ((subsetSum design {0, 1, 2} - 1) *ᵥ tightDir) = 0 →
      HasLivePairPositiveTie design) :
    BaseTripleTightLineFreeOffConicWeakToStrict :=
  fun design tightDir hlineFree hoffConic hdominates htightNe htight =>
    exists_posDef_cardThree_of_hasLivePairPositiveTie design
      (hresidual design tightDir hlineFree hoffConic hdominates htightNe htight)

/-! ## Part 4: the excess split, on both sides of the dictionary

The identity every certificate in the campaign is a reading of.  Substituting
weighted Parseval for `|x|^2` in `Gtz.dominationGap_form` makes the total moment
matrix disappear: SELECTED atoms contribute with their COMPLEMENTARY weight,
OUTSIDE atoms subtract with their OWN weight, and both sums run over half the
labels.  The chart-side twin is the landed
`Gtz.directionChartGap_eq_excessSplit`; the design side was missing. -/

/-- **THE DESIGN-SIDE EXCESS SPLIT.**  No hypotheses, any rank, any subset. -/
theorem dotProduct_subsetSum_sub_one_mulVec_eq_excessSplit (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (probeVec : Fin rank → ℝ) :
    probeVec ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probeVec)
      = (∑ label ∈ selected,
          (1 - design.weight label) * (design.atom label ⬝ᵥ probeVec) ^ 2)
        - ∑ label ∈ selectedᶜ,
            design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 := by
  classical
  have hsplit : ∑ label, design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2
      = (∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2)
        + ∑ label ∈ selectedᶜ, design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 :=
    (Finset.sum_add_sum_compl selected
      (fun label => design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2)).symm
  have hcombine : ∑ label ∈ selected,
        (1 - design.weight label) * (design.atom label ⬝ᵥ probeVec) ^ 2
      = (∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec) ^ 2)
        - ∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by ring
  rw [dominationGap_form, dotProduct_self_eq_sum_weight_mul_sq design probeVec, hsplit,
    hcombine]
  ring

/-- **The complement engine as an equivalence.**  Strict domination of a subset
IS the statement that the outside carries strictly less weighted Parseval mass
than the selection's complementary-weight mass, in every nonzero direction. -/
theorem posDef_subsetSum_sub_one_iff_excessSplit (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    (subsetSum design selected - 1).PosDef
      ↔ ∀ probeVec : Fin rank → ℝ, probeVec ≠ 0 →
          (∑ label ∈ selectedᶜ,
              design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2)
            < ∑ label ∈ selected,
                (1 - design.weight label) * (design.atom label ⬝ᵥ probeVec) ^ 2 := by
  classical
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · intro hposDef probeVec hprobeNe
    have hvalue := hposDef.2 hprobeNe
    rw [star_trivial,
      dotProduct_subsetSum_sub_one_mulVec_eq_excessSplit design selected probeVec] at hvalue
    linarith
  · refine fun hexcess => ⟨isHermitian_of_transpose_eq
      (transpose_subsetSum_sub_one design selected), fun probeVec hprobeNe => ?_⟩
    rw [star_trivial,
      dotProduct_subsetSum_sub_one_mulVec_eq_excessSplit design selected probeVec]
    linarith [hexcess probeVec hprobeNe]

/-- The weak twin: domination read in excess coordinates. -/
theorem dominates_iff_excessSplit (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    Dominates design selected
      ↔ ∀ probeVec : Fin rank → ℝ,
          (∑ label ∈ selectedᶜ,
              design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2)
            ≤ ∑ label ∈ selected,
                (1 - design.weight label) * (design.atom label ⬝ᵥ probeVec) ^ 2 := by
  classical
  rw [Dominates, Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro hposSemidef probeVec
    have hvalue := hposSemidef.2 probeVec
    rw [star_trivial,
      dotProduct_subsetSum_sub_one_mulVec_eq_excessSplit design selected probeVec] at hvalue
    linarith
  · refine fun hexcess => ⟨isHermitian_of_transpose_eq
      (transpose_subsetSum_sub_one design selected), fun probeVec => ?_⟩
    rw [star_trivial,
      dotProduct_subsetSum_sub_one_mulVec_eq_excessSplit design selected probeVec]
    linarith [hexcess probeVec]

/-! ## Part 5: the chart-to-design dictionary, square-root free -/

/-- The chart gap's quadratic form in EXCESS-SPLIT coordinates: selected labels
contribute their weight excess `m (1 - w) / w`, outside labels subtract their raw
mass.  The total moment matrix has disappeared and both sums run over half the
labels.  This is the chart-side reading of the design-side excess split. -/
theorem dotProduct_directionChartGap_mulVec (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hweightNe : ∀ label, weight label ≠ 0)
    (selected : Finset (Fin size)) (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probeVec)
      = (∑ label ∈ selected,
          chartExcess mass weight label * (direction label ⬝ᵥ probeVec) ^ 2)
        - ∑ label ∈ selectedᶜ, mass label * (direction label ⬝ᵥ probeVec) ^ 2 := by
  classical
  rw [directionChartGap_eq_excessSplit direction mass weight hweightNe selected,
    Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, Matrix.sum_mulVec,
    dotProduct_sum, dotProduct_sum]
  congr 1
  · refine Finset.sum_congr rfl fun label _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec,
      chartExcess]
  · refine Finset.sum_congr rfl fun label _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]

/-- **The chart complement engine.**  Sign-only, no dictionary: the chart gap is
positive definite exactly when the labels OUTSIDE the selection carry strictly
less squared mass than the selected labels' weight excess, in every nonzero
direction. -/
theorem posDef_directionChartGap_iff_excess (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hweightNe : ∀ label, weight label ≠ 0)
    (selected : Finset (Fin size)) :
    (directionChartGap direction mass weight selected).PosDef
      ↔ ∀ probeVec : Fin 3 → ℝ, probeVec ≠ 0 →
          (∑ label ∈ selectedᶜ, mass label * (direction label ⬝ᵥ probeVec) ^ 2)
            < ∑ label ∈ selected,
                chartExcess mass weight label * (direction label ⬝ᵥ probeVec) ^ 2 := by
  classical
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · intro hposDef probeVec hprobeNe
    have hvalue := hposDef.2 hprobeNe
    rw [star_trivial,
      dotProduct_directionChartGap_mulVec direction mass weight hweightNe selected] at hvalue
    linarith
  · refine fun hexcess => ⟨isHermitian_of_transpose_eq
      (directionChartGap_transpose direction mass weight selected), fun probeVec hprobeNe => ?_⟩
    rw [star_trivial,
      dotProduct_directionChartGap_mulVec direction mass weight hweightNe selected]
    linarith [hexcess probeVec hprobeNe]

/-- The weak twin of the same reading. -/
theorem posSemidef_directionChartGap_iff_excess (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hweightNe : ∀ label, weight label ≠ 0)
    (selected : Finset (Fin size)) :
    (directionChartGap direction mass weight selected).PosSemidef
      ↔ ∀ probeVec : Fin 3 → ℝ,
          (∑ label ∈ selectedᶜ, mass label * (direction label ⬝ᵥ probeVec) ^ 2)
            ≤ ∑ label ∈ selected,
                chartExcess mass weight label * (direction label ⬝ᵥ probeVec) ^ 2 := by
  classical
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro hposSemidef probeVec
    have hvalue := hposSemidef.2 probeVec
    rw [star_trivial,
      dotProduct_directionChartGap_mulVec direction mass weight hweightNe selected] at hvalue
    linarith
  · refine fun hexcess => ⟨isHermitian_of_transpose_eq
      (directionChartGap_transpose direction mass weight selected), fun probeVec => ?_⟩
    rw [star_trivial,
      dotProduct_directionChartGap_mulVec direction mass weight hweightNe selected]
    linarith [hexcess probeVec]

/-! ### The realization: a chart point IS a design, up to one congruence -/

/-- The atom family a chart point names: the fixed direction scaled by the square
root of the point's mass-to-weight ratio.  That scalar square root is the ONLY
root anywhere in this file -- no matrix square root is built, exactly as in
`Gtz.ComplementFrame`. -/
noncomputable def chartAtomFamily (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (label : Fin size) : Fin 3 → ℝ :=
  Real.sqrt (mass label / weight label) • direction label

theorem atomMatrix_chartAtomFamily (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (label : Fin size)
    (hratio : 0 ≤ mass label / weight label) :
    atomMatrix (chartAtomFamily direction mass weight label)
      = (mass label / weight label) • atomMatrix (direction label) := by
  rw [chartAtomFamily, atomMatrix_smul, Real.sq_sqrt hratio]

/-- The chart point's frame operator IS the total moment matrix of the chart. -/
theorem frameOperatorOfAtoms_chartAtomFamily (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmassNonneg : ∀ label, 0 ≤ mass label)
    (hweightPos : ∀ label, 0 < weight label) :
    frameOperatorOfAtoms (chartAtomFamily direction mass weight) weight
      = ∑ label, mass label • atomMatrix (direction label) := by
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [atomMatrix_chartAtomFamily direction mass weight label
      (div_nonneg (hmassNonneg label) (hweightPos label).le), smul_smul,
    mul_div_cancel₀ _ (hweightPos label).ne']

/-- The chart point's selected moment is the chart's own selected sum. -/
theorem subsetSumOfAtoms_chartAtomFamily (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmassNonneg : ∀ label, 0 ≤ mass label)
    (hweightPos : ∀ label, 0 < weight label) (selected : Finset (Fin size)) :
    subsetSumOfAtoms (chartAtomFamily direction mass weight) selected
      = ∑ label ∈ selected, (mass label / weight label) • atomMatrix (direction label) :=
  Finset.sum_congr rfl fun label _ =>
    atomMatrix_chartAtomFamily direction mass weight label
      (div_nonneg (hmassNonneg label) (hweightPos label).le)

/-- **The chart gap is a frame gap.**  No congruence yet, no invertibility: the
chart gap is literally the selected moment of the chart atom family minus that
family's frame operator. -/
theorem directionChartGap_eq_frameGap (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmassNonneg : ∀ label, 0 ≤ mass label)
    (hweightPos : ∀ label, 0 < weight label) (selected : Finset (Fin size)) :
    directionChartGap direction mass weight selected
      = subsetSumOfAtoms (chartAtomFamily direction mass weight) selected
        - frameOperatorOfAtoms (chartAtomFamily direction mass weight) weight := by
  rw [subsetSumOfAtoms_chartAtomFamily direction mass weight hmassNonneg hweightPos selected,
    frameOperatorOfAtoms_chartAtomFamily direction mass weight hmassNonneg hweightPos,
    directionChartGap]

/-- **TARGET C.  EVERY CHART POINT WITH A POSITIVE DEFINITE MOMENT MATRIX IS A
WEIGHTED DESIGN.**  One invertible congruence -- produced square-root free by the
landed `Gtz.exists_congruence_to_one` -- carries the chart gap of EVERY subset,
simultaneously, onto the design gap of the same subset.  Positive definiteness
and positive semidefiniteness therefore agree on the nose, and the design keeps
the chart point's own weights. -/
theorem exists_design_of_chartPoint (direction : Fin size → (Fin 3 → ℝ))
    (point : DirectionChartPoint size)
    (hmoment : (∑ label, point.mass label • atomMatrix (direction label)).PosDef) :
    ∃ design : WeightedDesign size 3, design.weight = point.weight ∧
      ∀ selected : Finset (Fin size),
        ((subsetSum design selected - 1).PosDef
            ↔ (directionChartGap direction point.mass point.weight selected).PosDef)
          ∧ (Dominates design selected
            ↔ (directionChartGap direction point.mass point.weight selected).PosSemidef) := by
  classical
  have hmassNonneg : ∀ label, 0 ≤ point.mass label := fun label => (point.mass_pos label).le
  have hframe : frameOperatorOfAtoms (chartAtomFamily direction point.mass point.weight)
      point.weight = ∑ label, point.mass label • atomMatrix (direction label) :=
    frameOperatorOfAtoms_chartAtomFamily direction point.mass point.weight hmassNonneg
      point.weight_pos
  obtain ⟨congruence, hunit, hcongruence⟩ := exists_congruence_to_one (hframe ▸ hmoment)
  have hwhiten : congruenceᵀ * (∑ label, point.weight label
      • atomMatrix (chartAtomFamily direction point.mass point.weight label))
      * congruence = 1 := hcongruence
  refine ⟨whitenedFamilyDesign (chartAtomFamily direction point.mass point.weight) point.weight
      point.weight_pos point.weight_sum_one congruence hwhiten, rfl, fun selected => ?_⟩
  have hmomentEq : subsetSum (whitenedFamilyDesign
        (chartAtomFamily direction point.mass point.weight) point.weight point.weight_pos
        point.weight_sum_one congruence hwhiten) selected
      = congruenceᵀ * subsetSumOfAtoms (chartAtomFamily direction point.mass point.weight)
          selected * congruence := by
    rw [whitenedDesign_subsetSum_eq, sum_atomMatrix_conj, subsetSumOfAtoms]
  have hgapEq : subsetSum (whitenedFamilyDesign
        (chartAtomFamily direction point.mass point.weight) point.weight point.weight_pos
        point.weight_sum_one congruence hwhiten) selected - 1
      = congruenceᵀ * directionChartGap direction point.mass point.weight selected
          * congruence := by
    rw [hmomentEq, ← hcongruence,
      directionChartGap_eq_frameGap direction point.mass point.weight hmassNonneg
        point.weight_pos selected,
      frameOperatorOfAtoms, Matrix.mul_assoc congruenceᵀ, Matrix.mul_assoc congruenceᵀ,
      ← Matrix.mul_sub, ← Matrix.sub_mul, ← Matrix.mul_assoc]
  have hsymmetric : (directionChartGap direction point.mass point.weight selected)ᵀ
      = directionChartGap direction point.mass point.weight selected :=
    directionChartGap_transpose direction point.mass point.weight selected
  refine ⟨?_, ?_⟩
  · rw [hgapEq]
    exact (posDef_congr_right hsymmetric hunit).symm
  · show (subsetSum _ selected - 1).PosSemidef ↔ _
    rw [hgapEq]
    exact (posSemidef_congr_right hsymmetric hunit).symm

/-- **TARGET C, consumed.**  The chart obligation reduces to a DESIGN-side
weak-to-strict upgrade at every chart point whose moment matrix is positive
definite.  No chart-specific data survives on the design side. -/
theorem directionChartIsTieFree_of_momentPosDef_of_designUpgrade
    (direction : Fin size → (Fin 3 → ℝ))
    (hmoment : ∀ point : DirectionChartPoint size,
      (∑ label, point.mass label • atomMatrix (direction label)).PosDef)
    (hupgrade : ∀ design : WeightedDesign size 3,
      (∃ dominator : Finset (Fin size), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin size), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    DirectionChartIsTieFree direction := by
  intro point hweak
  obtain ⟨design, -, htransfer⟩ := exists_design_of_chartPoint direction point (hmoment point)
  obtain ⟨dominator, hcard, hdominates⟩ := hweak
  obtain ⟨selected, hcardSelected, hposDef⟩ :=
    hupgrade design ⟨dominator, hcard, (htransfer dominator).2.mpr hdominates⟩
  exact ⟨selected, hcardSelected, (htransfer selected).1.mp hposDef⟩

/-- **TARGET B(iii).**  The chart obligation, reduced all the way to ONE
DETERMINANT SIGN: at every weakly dominated realization of a chart point, every
live pair completes to a strictly positive tie leg. -/
theorem directionChartIsTieFree_of_momentPosDef_of_livePairTie
    (direction : Fin size → (Fin 3 → ℝ))
    (hmoment : ∀ point : DirectionChartPoint size,
      (∑ label, point.mass label • atomMatrix (direction label)).PosDef)
    (hresidual : ∀ design : WeightedDesign size 3,
      (∃ dominator : Finset (Fin size), dominator.card = 3 ∧ Dominates design dominator) →
      ∀ pivotLabel pairFirst : Fin size, pivotLabel ≠ pairFirst →
        IsLivePair design pivotLabel pairFirst →
        ∃ pairSecond : Fin size, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond) :
    DirectionChartIsTieFree direction :=
  directionChartIsTieFree_of_momentPosDef_of_designUpgrade direction hmoment
    fun design hweak => exists_posDef_cardThree_of_forall_livePair design (hresidual design hweak)

/-! ### The moment hypothesis is discharged on both live charts -/

/-- A chart whose directions contain three labels spanning the probe space has a
positive definite moment matrix at every point with positive masses. -/
theorem posDef_massMoment_of_spanningTriple (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) (hmassPos : ∀ label, 0 < mass label)
    (firstLabel secondLabel thirdLabel : Fin size)
    (hspan : ∀ probeVec : Fin 3 → ℝ, direction firstLabel ⬝ᵥ probeVec = 0 →
      direction secondLabel ⬝ᵥ probeVec = 0 → direction thirdLabel ⬝ᵥ probeVec = 0 →
      probeVec = 0) :
    (∑ label, mass label • atomMatrix (direction label)).PosDef := by
  classical
  have hform : ∀ probeVec : Fin 3 → ℝ,
      probeVec ⬝ᵥ ((∑ label, mass label • atomMatrix (direction label)) *ᵥ probeVec)
        = ∑ label, mass label * (direction label ⬝ᵥ probeVec) ^ 2 := by
    intro probeVec
    rw [Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun label _ => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_of_transpose_eq ?_,
    fun probeVec hprobeNe => ?_⟩
  · rw [Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [Matrix.transpose_smul, atomMatrix, Matrix.transpose_vecMulVec]
  · rw [star_trivial, hform probeVec]
    have htermNonneg : ∀ label ∈ (Finset.univ : Finset (Fin size)),
        0 ≤ mass label * (direction label ⬝ᵥ probeVec) ^ 2 :=
      fun label _ => mul_nonneg (hmassPos label).le (sq_nonneg _)
    rcases lt_or_eq_of_le (Finset.sum_nonneg htermNonneg) with hpos | hzero
    · exact hpos
    · exfalso
      have hvanish : ∀ label ∈ (Finset.univ : Finset (Fin size)),
          mass label * (direction label ⬝ᵥ probeVec) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg htermNonneg).mp hzero.symm
      have hoverlap : ∀ label : Fin size, direction label ⬝ᵥ probeVec = 0 := by
        intro label
        have hproduct := hvanish label (Finset.mem_univ label)
        have hsquare : (direction label ⬝ᵥ probeVec) ^ 2 = 0 := by
          rcases mul_eq_zero.mp hproduct with hmassZero | hsquareZero
          · exact absurd hmassZero (hmassPos label).ne'
          · exact hsquareZero
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsquare
      exact hprobeNe (hspan probeVec (hoverlap firstLabel) (hoverlap secondLabel)
        (hoverlap thirdLabel))

/-- A probe with all three coordinates zero is the zero probe. -/
theorem eq_zero_of_coordinates_eq_zero {probeVec : Fin 3 → ℝ}
    (hzeroth : probeVec 0 = 0) (hfirst : probeVec 1 = 0) (hsecond : probeVec 2 = 0) :
    probeVec = 0 := by
  funext coordinate
  fin_cases coordinate
  · exact hzeroth
  · exact hfirst
  · exact hsecond

/-- The K4 chart's moment matrix is positive definite at every chart point: its
labels three, four and five are the coordinate axes. -/
theorem posDef_massMoment_kFourDirection (point : DirectionChartPoint 6) :
    (∑ label, point.mass label • atomMatrix (kFourDirection label)).PosDef := by
  refine posDef_massMoment_of_spanningTriple kFourDirection point.mass point.mass_pos 3 4 5
    fun probeVec hfirst hsecond hthird => ?_
  simp only [kFourDirection, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at hfirst hsecond hthird
  exact eq_zero_of_coordinates_eq_zero (by linarith) (by linarith) (by linarith)

/-- The three-lines chart's moment matrix is positive definite at every chart
point and every slide: its labels zero, one and three are the coordinate axes.
No admissibility hypothesis is needed. -/
theorem posDef_massMoment_threeLinesDirection (slide : ℝ) (point : DirectionChartPoint 6) :
    (∑ label, point.mass label • atomMatrix (threeLinesDirection slide label)).PosDef := by
  refine posDef_massMoment_of_spanningTriple (threeLinesDirection slide) point.mass
    point.mass_pos 0 1 3 fun probeVec hfirst hsecond hthird => ?_
  simp only [threeLinesDirection, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at hfirst hsecond hthird
  exact eq_zero_of_coordinates_eq_zero (by linarith) (by linarith) (by linarith)

/-- **The K4 chart obligation, on the design side.**  `Gtz.DirectionChartIsTieFree`
at `Gtz.kFourDirection` follows from a design-level weak-to-strict upgrade with
no chart data at all. -/
theorem directionChartIsTieFree_kFour_of_designUpgrade
    (hupgrade : ∀ design : WeightedDesign 6 3,
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    DirectionChartIsTieFree kFourDirection :=
  directionChartIsTieFree_of_momentPosDef_of_designUpgrade kFourDirection
    posDef_massMoment_kFourDirection hupgrade

/-- **The three-lines chart obligation, on the design side**, at every slide. -/
theorem directionChartIsTieFree_threeLines_of_designUpgrade (slide : ℝ)
    (hupgrade : ∀ design : WeightedDesign 6 3,
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    DirectionChartIsTieFree (threeLinesDirection slide) :=
  directionChartIsTieFree_of_momentPosDef_of_designUpgrade (threeLinesDirection slide)
    (posDef_massMoment_threeLinesDirection slide) hupgrade

/-! ## Part 6: the statements are not vacuous

The regular tetrahedron is the campaign's hardest small fixture: it IS a tie, and
its live pairs cannot be completed.  So the one-determinant residual is a genuine
open condition, not a tautology dressed up -- it is FALSE exactly at the ties. -/

/-- The tetrahedron carries no live pair with a positive tie leg, because it
carries no strictly dominating triple at all. -/
theorem not_hasLivePairPositiveTie_tetraDesign : ¬ HasLivePairPositiveTie tetraDesign := by
  intro hresidual
  obtain ⟨selected, hcard, hposDef⟩ :=
    exists_posDef_cardThree_of_hasLivePairPositiveTie tetraDesign hresidual
  exact tetraDesign_no_strictDominator selected hcard hposDef

/-- **The reduction is faithful.**  At the tetrahedron the live pair exists (Part
1 is unconditional, and ties are no exception) yet no completion has a positive
tie leg (Part 3 is equivalent to strict domination, which fails).  So the whole
residual really does sit in the determinant sign. -/
theorem tetraDesign_hasLivePair_and_not_positiveTie :
    (∃ pivotLabel pairFirst : Fin 4, pivotLabel ≠ pairFirst
        ∧ IsLivePair tetraDesign pivotLabel pairFirst)
      ∧ ¬ HasLivePairPositiveTie tetraDesign :=
  ⟨exists_isLivePair_rankThree tetraDesign, not_hasLivePairPositiveTie_tetraDesign⟩

/-- **The chart realization fires** at the canonical inhabitant of the K4 residual
band, the point every Layer-B candidate must be tested against first. -/
theorem exists_design_of_bandResidualWitnessPoint :
    ∃ design : WeightedDesign 6 3, design.weight = bandResidualWitnessPoint.weight ∧
      ∀ selected : Finset (Fin 6),
        ((subsetSum design selected - 1).PosDef
            ↔ (directionChartGap kFourDirection bandResidualWitnessPoint.mass
                bandResidualWitnessPoint.weight selected).PosDef)
          ∧ (Dominates design selected
            ↔ (directionChartGap kFourDirection bandResidualWitnessPoint.mass
                bandResidualWitnessPoint.weight selected).PosSemidef) :=
  exists_design_of_chartPoint kFourDirection bandResidualWitnessPoint
    (posDef_massMoment_kFourDirection bandResidualWitnessPoint)

end Gtz

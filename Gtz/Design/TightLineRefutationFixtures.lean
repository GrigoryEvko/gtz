import Gtz.Design.LineBranchFreePairAggregateBridge
import Gtz.Design.TightLineBranchLivePairBridge
import Gtz.Design.UThreeSixStratumWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Two exact designs that permanently close two nominated routes

Both designs below are literal `Gtz.WeightedDesign 6 3` values with rational
atoms, Parseval exactly the identity, all six weights strictly positive, and
the full line-branch antecedent set: the base triple `{0,1,2}` dominates
weakly, the design is line-free (`Gtz.HasLinePattern` at the empty family) and
off-conic (`Gtz.HasNoCommonQuadric`), and an explicit tight direction of the
base gap is exhibited.  At both designs the branch itself **holds** -- a
strictly dominating card-three subset is exhibited -- so neither is a
counterexample to anything the campaign is trying to prove.  What each one
kills is a *selector*: a proposed sufficient condition whose hypothesis is
false here while the conclusion is true, i.e. a true theorem that can never
be applied.

## The base-pair killer

`Gtz.baseTieKillerDesign` has base gap `!![0,0,0; 0,3,8; 0,8,31]`, tight
direction `e_0`, leverages `16, 20, 1, 9/4, 17, 26`.  Its only transverse base
label is `2`, so the canonical base pair is `{0,1}`, and that pair **is** live.
Every tie leg there is nonpositive -- `0, -287/4, -496, -331` -- and in fact
`Gtz.discriminantTie` is nonpositive at **every** ordered pair of distinct base
labels and **every** completion.  Meanwhile the branch holds three times over:
`{0,4,5}`, `{1,3,5}` and `{1,4,5}` all dominate strictly, and each of them sits
at distance **two** from the base triple.  So "some tie leg at a live base pair
is positive" is not a route: a positive leg there would produce a strict triple
with two base labels, i.e. a one-slot swap, and this design has none.

## The free-pair killer

`Gtz.freePairKillerDesign` has base gap `!![20,14,3; 14,16,-1; 3,-1,2]`, tight
direction `(1,-1,-2)`, leverages `9, 26, 6, 11/2, 1, 6`.  **No free pair is
live**, while the branch holds five times over and every one of its strict
triples is a one-slot swap.  So the unconditional statement "some free pair is
live at every tight-line antecedent" is false, and the conditional form -- the
one guarded by *no one-slot swap is strict* -- is the only survivor.

The same design calibrates the aggregate hinge.  Exactly one of its free atoms
is light (label `4`, leverage exactly one), so the pairwise heaviness ingredient
**holds** here; yet the weighted pair-minor row aggregate is `-315/128 < 0`.
Pairwise heaviness therefore does not imply aggregate positivity, and any proof
of the aggregate must consume the no-one-slot hypothesis, which this design
fails.  For the opposite sign, `Gtz.baseTieKillerDesign` has aggregate
`14107/1008 > 0`, which is the inhabiting witness for the hypothesis of
`Gtz.exists_live_freePair_of_no_cardThree_posDef_of_rowAggregate_pos`.
-/

namespace Gtz

open Matrix

/-! ## The three-label pair-row aggregate, unfolded -/

/-- `Gtz.pairRowAggregateOn` at three indices, as its six explicit terms. -/
theorem pairRowAggregateOn_fin_three {size : ℕ} (design : WeightedDesign size 3)
    (label : Fin 3 → Fin size) :
    pairRowAggregateOn design label
      = design.weight (label 1) * pairGapExcessOf design (label 0) (label 1)
        + design.weight (label 2) * pairGapExcessOf design (label 0) (label 2)
        + (design.weight (label 0) * pairGapExcessOf design (label 1) (label 0)
            + design.weight (label 2) * pairGapExcessOf design (label 1) (label 2))
        + (design.weight (label 0) * pairGapExcessOf design (label 2) (label 0)
            + design.weight (label 1) * pairGapExcessOf design (label 2) (label 1)) := by
  have hdropZero : (Finset.univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide
  have hdropOne : (Finset.univ : Finset (Fin 3)).erase 1 = {0, 2} := by decide
  have hdropTwo : (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} := by decide
  simp only [pairRowAggregateOn, Fin.sum_univ_three, hdropZero, hdropOne, hdropTwo]
  rw [Finset.sum_pair (by decide), Finset.sum_pair (by decide), Finset.sum_pair (by decide)]

/-! ## Fixture one: the base-pair killer -/

noncomputable def baseTieKillerAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![0, 0, -4]
  | 1 => ![0, -2, -4]
  | 2 => ![1, 0, 0]
  | 3 => ![-(1 / 2), -1, 1]
  | 4 => ![-1, -4, 0]
  | 5 => ![3, -4, 1]

noncomputable def baseTieKillerWeight : Fin 6 → ℝ
  | 0 => 1 / 28
  | 1 => 5 / 252
  | 2 => 67 / 84
  | 3 => 2 / 21
  | 4 => 1 / 28
  | 5 => 1 / 63

/-- The base-pair killer: Parseval exact, all weights positive. -/
noncomputable def baseTieKillerDesign : WeightedDesign 6 3 where
  atom := baseTieKillerAtom
  weight := baseTieKillerWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [baseTieKillerWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [baseTieKillerWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [baseTieKillerAtom, baseTieKillerWeight, atomMatrix, Matrix.cons_val_two] <;>
      norm_num

/-- **LINE-FREE.**  All twenty triples have nonzero bracket. -/
theorem baseTieKillerDesign_hasLinePattern :
    HasLinePattern baseTieKillerDesign (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, baseTieKillerDesign,
            baseTieKillerAtom, Matrix.cons_val_two])
          (by decide)

/-- **OFF-CONIC.**  The Veronese determinant is `129024`; the elimination below
never needs it. -/
theorem baseTieKillerDesign_hasNoCommonQuadric :
    HasNoCommonQuadric baseTieKillerDesign.atom := by
  intro form hsymmetric hquadric
  have hsym : ∀ rowIndex colIndex : Fin 3, form colIndex rowIndex = form rowIndex colIndex :=
    fun rowIndex colIndex => congrFun (congrFun hsymmetric rowIndex) colIndex
  have hzero := hquadric 0
  have hone := hquadric 1
  have htwo := hquadric 2
  have hthree := hquadric 3
  have hfour := hquadric 4
  have hfive := hquadric 5
  simp only [baseTieKillerDesign, baseTieKillerAtom, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hzero hone htwo hthree hfour hfive
  simp only [hsym 0 1, hsym 0 2, hsym 1 2] at hzero hone htwo hthree hfour hfive
  have hcornerZero : form 0 0 = 0 := by linarith
  have hlastZero : form 2 2 = 0 := by linarith
  have hsideZero : form 1 2 = 0 := by linarith
  have hmidZero : form 1 1 = 0 := by linarith
  have hcrossZero : form 0 1 = 0 := by linarith
  have hupZero : form 0 2 = 0 := by linarith
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Matrix.zero_apply] <;>
    first
      | exact hcornerZero
      | exact hmidZero
      | exact hlastZero
      | exact hcrossZero
      | exact hupZero
      | exact hsideZero
      | exact (hsym 0 1).trans hcrossZero
      | exact (hsym 0 2).trans hupZero
      | exact (hsym 1 2).trans hsideZero

/-- The base gap as a sum of squares in the last two coordinates; the first
coordinate is absent, which is exactly the tight direction. -/
theorem baseTieKillerDesign_baseTripleGap_form (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ ((subsetSum baseTieKillerDesign ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ probeVec)
      = 3 * (probeVec 1 + 8 / 3 * probeVec 2) ^ 2 + 29 / 3 * probeVec 2 ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [baseTieKillerDesign, baseTieKillerAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

/-- **WEAK DOMINATION** at the base triple. -/
theorem baseTieKillerDesign_dominates_baseTriple :
    Dominates baseTieKillerDesign ({0, 1, 2} : Finset (Fin 6)) := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 1, 2} : Finset (Fin 6)) fun label _ =>
      posSemidef_atomMatrix (baseTieKillerDesign.atom label)).1).sub Matrix.isHermitian_one
  · rw [star_trivial, baseTieKillerDesign_baseTripleGap_form]
    positivity

theorem baseTieKillerDesign_tightDirection_ne_zero :
    (![1, 0, 0] : Fin 3 → ℝ) ≠ 0 := by
  intro hzero
  have hentry : (![1, 0, 0] : Fin 3 → ℝ) 0 = 0 := by rw [hzero]; rfl
  norm_num at hentry

theorem baseTieKillerDesign_tightDirection_rayleigh :
    (![1, 0, 0] : Fin 3 → ℝ)
        ⬝ᵥ ((subsetSum baseTieKillerDesign ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ ![1, 0, 0])
      = 0 := by
  rw [baseTieKillerDesign_baseTripleGap_form]
  norm_num [Matrix.cons_val_two]

/-- The canonical base pair -- the one opposite the sole transverse base label
`2` -- **is** live. -/
theorem baseTieKillerDesign_isLivePair_baseZeroOne :
    IsLivePair baseTieKillerDesign 0 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [gapExcessOf, gapPairingOf, pairGapExcessOf, leverageOf, dotProduct,
      Fin.sum_univ_three, baseTieKillerDesign, baseTieKillerAtom, Matrix.cons_val_two]

/-- **THE REFUTATION.**  At every ordered pair of *distinct* base labels and
every completion, the tie leg is nonpositive.  No liveness hypothesis is needed:
the statement is uniform over the six ordered base pairs. -/
theorem baseTieKillerDesign_baseTriplePair_discriminantTie_nonpos
    (pivotLabel pairFirst pairSecond : Fin 6)
    (hpivot : pivotLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hfirst : pairFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hdistinct : pivotLabel ≠ pairFirst) :
    discriminantTie baseTieKillerDesign pivotLabel pairFirst pairSecond ≤ 0 := by
  fin_cases pivotLabel <;> fin_cases pairFirst <;> fin_cases pairSecond <;>
    first
      | exact absurd rfl hdistinct
      | exact absurd hpivot (by decide)
      | exact absurd hfirst (by decide)
      | (simp only [discriminantTie, heavyExcess, atomPairing, leverageOf, dotProduct,
          Fin.sum_univ_three, baseTieKillerDesign, baseTieKillerAtom, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
         norm_num)

/-- The distance-two triple `{0,4,5}` as a sum of three squares. -/
theorem baseTieKillerDesign_strictTripleGap_form (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ ((subsetSum baseTieKillerDesign ({0, 4, 5} : Finset (Fin 6)) - 1) *ᵥ probeVec)
      = 9 * (probeVec 0 - 8 / 9 * probeVec 1 + 1 / 3 * probeVec 2) ^ 2
        + 215 / 9 * (probeVec 1 - 12 / 215 * probeVec 2) ^ 2
        + 3209 / 215 * probeVec 2 ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [baseTieKillerDesign, baseTieKillerAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

/-- **THE BRANCH HOLDS.**  `{0,4,5}` dominates strictly, at distance two from
the base triple. -/
theorem baseTieKillerDesign_hasStrictTriple :
    (subsetSum baseTieKillerDesign ({0, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec hne => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 4, 5} : Finset (Fin 6)) fun label _ =>
      posSemidef_atomMatrix (baseTieKillerDesign.atom label)).1).sub Matrix.isHermitian_one
  · rw [star_trivial, baseTieKillerDesign_strictTripleGap_form]
    by_cases hlast : probeVec 2 = 0
    · by_cases hmid : probeVec 1 = 0
      · have hfirst : probeVec 0 ≠ 0 := by
          intro hfirstZero
          refine hne (funext fun coordIndex => ?_)
          fin_cases coordIndex
          · simpa using hfirstZero
          · simpa using hmid
          · simpa using hlast
        rw [hlast, hmid]
        have hsq : 0 < probeVec 0 ^ 2 := by positivity
        nlinarith
      · have hsq : 0 < probeVec 1 ^ 2 := by positivity
        rw [hlast]
        nlinarith [sq_nonneg (probeVec 0 - 8 / 9 * probeVec 1)]
    · have hsq : 0 < probeVec 2 ^ 2 := by positivity
      nlinarith [sq_nonneg (probeVec 0 - 8 / 9 * probeVec 1 + 1 / 3 * probeVec 2),
        sq_nonneg (probeVec 1 - 12 / 215 * probeVec 2)]

/-- **THE INHABITING WITNESS** for the aggregate hypothesis of
`Gtz.exists_live_freePair_of_no_cardThree_posDef_of_rowAggregate_pos`: the row
aggregate is `14107/1008`, strictly positive. -/
theorem baseTieKillerDesign_freePairRowAggregate_pos :
    0 < freePairRowAggregate baseTieKillerDesign := by
  rw [freePairRowAggregate, pairRowAggregateOn_fin_three]
  norm_num [freeThreeLabel, pairGapExcessOf, gapExcessOf, gapPairingOf, leverageOf,
    dotProduct, Fin.sum_univ_three, baseTieKillerDesign, baseTieKillerAtom,
    baseTieKillerWeight, Matrix.cons_val_two]

/-! ## Fixture two: the free-pair killer -/

noncomputable def freePairKillerAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![2, 2, -1]
  | 1 => ![-4, -3, -1]
  | 2 => ![-1, 2, -1]
  | 3 => ![3 / 2, -(3 / 2), -1]
  | 4 => ![0, 0, -1]
  | 5 => ![2, -1, -1]

noncomputable def freePairKillerWeight : Fin 6 → ℝ
  | 0 => 1 / 48
  | 1 => 1 / 32
  | 2 => 5 / 48
  | 3 => 1 / 12
  | 4 => 35 / 48
  | 5 => 1 / 32

/-- The free-pair killer: Parseval exact, all weights positive. -/
noncomputable def freePairKillerDesign : WeightedDesign 6 3 where
  atom := freePairKillerAtom
  weight := freePairKillerWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [freePairKillerWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [freePairKillerWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [freePairKillerAtom, freePairKillerWeight, atomMatrix, Matrix.cons_val_two] <;>
      norm_num

/-- **LINE-FREE.**  All twenty triples have nonzero bracket; the smallest in
absolute value is `3/2`. -/
theorem freePairKillerDesign_hasLinePattern :
    HasLinePattern freePairKillerDesign (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, freePairKillerDesign,
            freePairKillerAtom, Matrix.cons_val_two])
          (by decide)

/-- **OFF-CONIC.**  The Veronese determinant is `27648`. -/
theorem freePairKillerDesign_hasNoCommonQuadric :
    HasNoCommonQuadric freePairKillerDesign.atom := by
  intro form hsymmetric hquadric
  have hsym : ∀ rowIndex colIndex : Fin 3, form colIndex rowIndex = form rowIndex colIndex :=
    fun rowIndex colIndex => congrFun (congrFun hsymmetric rowIndex) colIndex
  have hzero := hquadric 0
  have hone := hquadric 1
  have htwo := hquadric 2
  have hthree := hquadric 3
  have hfour := hquadric 4
  have hfive := hquadric 5
  simp only [freePairKillerDesign, freePairKillerAtom, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hzero hone htwo hthree hfour hfive
  simp only [hsym 0 1, hsym 0 2, hsym 1 2] at hzero hone htwo hthree hfour hfive
  have hlastZero : form 2 2 = 0 := by linarith
  have hcornerZero : form 0 0 = 0 := by linarith
  have hmidZero : form 1 1 = 0 := by linarith
  have hcrossZero : form 0 1 = 0 := by linarith
  have hupZero : form 0 2 = 0 := by linarith
  have hsideZero : form 1 2 = 0 := by linarith
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Matrix.zero_apply] <;>
    first
      | exact hcornerZero
      | exact hmidZero
      | exact hlastZero
      | exact hcrossZero
      | exact hupZero
      | exact hsideZero
      | exact (hsym 0 1).trans hcrossZero
      | exact (hsym 0 2).trans hupZero
      | exact (hsym 1 2).trans hsideZero

/-- The base gap as two squares; the missing third square is the tight
direction `(1,-1,-2)`. -/
theorem freePairKillerDesign_baseTripleGap_form (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ ((subsetSum freePairKillerDesign ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ probeVec)
      = 20 * (probeVec 0 + 7 / 10 * probeVec 1 + 3 / 20 * probeVec 2) ^ 2
        + 31 / 5 * (probeVec 1 - 1 / 2 * probeVec 2) ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [freePairKillerDesign, freePairKillerAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

/-- **WEAK DOMINATION** at the base triple. -/
theorem freePairKillerDesign_dominates_baseTriple :
    Dominates freePairKillerDesign ({0, 1, 2} : Finset (Fin 6)) := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 1, 2} : Finset (Fin 6)) fun label _ =>
      posSemidef_atomMatrix (freePairKillerDesign.atom label)).1).sub Matrix.isHermitian_one
  · rw [star_trivial, freePairKillerDesign_baseTripleGap_form]
    positivity

theorem freePairKillerDesign_tightDirection_ne_zero :
    (![1, -1, -2] : Fin 3 → ℝ) ≠ 0 := by
  intro hzero
  have hentry : (![1, -1, -2] : Fin 3 → ℝ) 0 = 0 := by rw [hzero]; rfl
  norm_num at hentry

theorem freePairKillerDesign_tightDirection_rayleigh :
    (![1, -1, -2] : Fin 3 → ℝ)
        ⬝ᵥ ((subsetSum freePairKillerDesign ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ ![1, -1, -2])
      = 0 := by
  rw [freePairKillerDesign_baseTripleGap_form]
  norm_num [Matrix.cons_val_two]

/-- **THE REFUTATION.**  No free pair is live.  The three pair minors are
`-1`, `-31/4` and `-1`. -/
theorem not_isLivePair_freePairKillerDesign_freePair (first second : Fin 3)
    (hdistinct : first ≠ second) :
    ¬ IsLivePair freePairKillerDesign (freeThreeLabel first) (freeThreeLabel second) := by
  intro hlive
  have hminor := hlive.2.2
  revert hminor
  fin_cases first <;> fin_cases second <;>
    first
      | exact absurd rfl hdistinct
      | norm_num [freeThreeLabel, pairGapExcessOf, gapExcessOf, gapPairingOf, leverageOf,
          dotProduct, Fin.sum_univ_three, freePairKillerDesign, freePairKillerAtom,
          Matrix.cons_val_two]

/-- Exactly one free atom is light, so the pairwise heaviness ingredient of the
conditional hinge **holds** at this design. -/
theorem freePairKillerDesign_atMostOneNonheavyFree (first second : Fin 3)
    (hdistinct : first ≠ second) :
    0 < gapExcessOf freePairKillerDesign (freeThreeLabel first) ∨
      0 < gapExcessOf freePairKillerDesign (freeThreeLabel second) := by
  have hthreeHeavy : 0 < gapExcessOf freePairKillerDesign (freeThreeLabel 0) := by
    norm_num [freeThreeLabel, gapExcessOf, leverageOf, dotProduct, Fin.sum_univ_three,
      freePairKillerDesign, freePairKillerAtom, Matrix.cons_val_two]
  have hfiveHeavy : 0 < gapExcessOf freePairKillerDesign (freeThreeLabel 2) := by
    norm_num [freeThreeLabel, gapExcessOf, leverageOf, dotProduct, Fin.sum_univ_three,
      freePairKillerDesign, freePairKillerAtom, Matrix.cons_val_two]
  fin_cases first <;> fin_cases second <;>
    first
      | exact absurd rfl hdistinct
      | exact Or.inl hthreeHeavy
      | exact Or.inl hfiveHeavy
      | exact Or.inr hthreeHeavy
      | exact Or.inr hfiveHeavy

/-- **THE CALIBRATION.**  Pairwise heaviness holds here and the aggregate is
still negative -- `-315/128`.  So the heaviness ingredient does not imply the
aggregate ingredient, and any proof of the aggregate must consume the
no-one-slot hypothesis, which this design fails five times over. -/
theorem freePairKillerDesign_freePairRowAggregate_neg :
    freePairRowAggregate freePairKillerDesign < 0 := by
  rw [freePairRowAggregate, pairRowAggregateOn_fin_three]
  norm_num [freeThreeLabel, pairGapExcessOf, gapExcessOf, gapPairingOf, leverageOf,
    dotProduct, Fin.sum_univ_three, freePairKillerDesign, freePairKillerAtom,
    freePairKillerWeight, Matrix.cons_val_two]

/-- The one-slot triple `{0,1,3}` as a sum of three squares. -/
theorem freePairKillerDesign_strictTripleGap_form (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ ((subsetSum freePairKillerDesign ({0, 1, 3} : Finset (Fin 6)) - 1) *ᵥ probeVec)
      = 85 / 4 * (probeVec 0 + 11 / 17 * probeVec 1 + 2 / 85 * probeVec 2) ^ 2
        + 91 / 17 * (probeVec 1 + 37 / 91 * probeVec 2) ^ 2
        + 502 / 455 * probeVec 2 ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [freePairKillerDesign, freePairKillerAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

/-- **THE BRANCH HOLDS.**  `{0,1,3}` dominates strictly, and it is a one-slot
swap of the base triple. -/
theorem freePairKillerDesign_hasStrictTriple :
    (subsetSum freePairKillerDesign ({0, 1, 3} : Finset (Fin 6)) - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec hne => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 1, 3} : Finset (Fin 6)) fun label _ =>
      posSemidef_atomMatrix (freePairKillerDesign.atom label)).1).sub Matrix.isHermitian_one
  · rw [star_trivial, freePairKillerDesign_strictTripleGap_form]
    by_cases hlast : probeVec 2 = 0
    · by_cases hmid : probeVec 1 = 0
      · have hfirst : probeVec 0 ≠ 0 := by
          intro hfirstZero
          refine hne (funext fun coordIndex => ?_)
          fin_cases coordIndex
          · simpa using hfirstZero
          · simpa using hmid
          · simpa using hlast
        rw [hlast, hmid]
        have hsq : 0 < probeVec 0 ^ 2 := by positivity
        nlinarith
      · have hsq : 0 < probeVec 1 ^ 2 := by positivity
        rw [hlast]
        nlinarith [sq_nonneg (probeVec 0 + 11 / 17 * probeVec 1)]
    · have hsq : 0 < probeVec 2 ^ 2 := by positivity
      nlinarith [sq_nonneg (probeVec 0 + 11 / 17 * probeVec 1 + 2 / 85 * probeVec 2),
        sq_nonneg (probeVec 1 + 37 / 91 * probeVec 2)]

end Gtz

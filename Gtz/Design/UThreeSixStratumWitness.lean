import Gtz.Design.UThreeSixDisjunction
import Gtz.Design.LineFreeConicBridge
import Gtz.Design.OrthogonalConicAndTwinRefutation
import Gtz.Design.LiftCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# An on-stratum inhabitant of the `U(3,6)` antecedent, and the tight-space split

`Gtz.BaseTripleTightLineFreeOffConicWeakToStrict` quantifies over line-free,
off-conic `(6,3)` designs whose base triple `{0,1,2}` weakly dominates along an
explicit tight direction.  Every reduction proved against that antecedent is
worthless if the antecedent region is empty, and until now no point of it had
been exhibited: the balance family's shipped non-vacuity inhabitant
(`Gtz.selectiveAxisDesign`) carries three parallel pairs and is therefore OFF
the line-free stratum.

## What this file lands

* **Part 1-2.**  An explicit rational design meeting the FULL antecedent —
  line-free (twenty nonzero brackets), off-conic, base triple weakly but not
  strictly dominating, with `e3` an explicit tight direction.  Every atom is
  heavy, so the residual's heaviness pin is met too.

* **Part 3.**  The BALANCE FAMILY FIRES here.  Its sharp form
  (`Gtz.posDef_subsetSum_complementTriple_of_residualExceedsMaxWeight`) hands
  over the complement triple `{3,4,5}`, exactly the conclusion family one
  advertises.  The five Phase-2 reductions therefore have a witnessed branch.
  A NEGATIVE comes with it: the SCALAR form
  (`Gtz.posDef_subsetSum_complementTriple_of_baseTripleShare_lt`) does NOT fire
  here — the base share is `92/51`, far above the `47/51` the scalar test
  demands.  Only the sharp Loewner form reaches this point.

* **Part 4.**  The TIGHT-SPACE DICHOTOMY.  `Gtz.baseTripleGap_psd_singular_ne_zero_of_offConic`
  pins the base gap as nonzero, singular and semidefinite, so its tight space is
  a LINE or a PLANE and nothing else.  In the plane branch the residual may
  choose its tight direction orthogonal to ANY prescribed vector
  (`Gtz.HasFreeTightDirection`), in particular flat against any chosen atom — a
  freedom the line branch does not give.  BOTH BRANCHES ARE INHABITED ON THE
  FULL ANTECEDENT: the first witness realizes the line branch, and a second
  rational design `Gtz.planeBranchDesign`, whose base gap is a single rank-one
  atom, realizes the plane branch.  The scalar balance test fails at that point
  too, and family one fires there as well.

* **Part 5.**  The LIFT CRITERION at the tight direction.  The two planar base
  atoms form a live pair there, and the base triple's lift margin is EXACTLY
  ZERO — the same boundary behaviour the regular tetrahedron exhibits, for a
  structural reason isolated here as
  `Gtz.liftMarginOf_eq_zero_of_flatPair_of_normalThird`.  Swapping the third
  label to `5` moves the margin to `32175 > 0` and produces a second strictly
  dominating triple through `Gtz.posDef_tripleGap_iff_pos_liftMargin`.
-/

namespace Gtz

open Matrix

/-! ## Part 1: the design -/

/-- The witness's six atoms.  Labels `0,1` span the plane `z = 0`, label `2` IS
the unit normal of that plane, and `3,4,5` are generic. -/
noncomputable def uThreeSixStratumAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![-4, 2, 0]
  | 1 => ![2, 2, 0]
  | 2 => ![0, 0, 1]
  | 3 => ![3 / 2, 0, 1 / 2]
  | 4 => ![-1, -3, 1]
  | 5 => ![0, 2, 2]

/-- The witness's weights: exact two-hundred-and-fourths. -/
noncomputable def uThreeSixStratumWeight : Fin 6 → ℝ
  | 0 => 2 / 51
  | 1 => 7 / 204
  | 2 => 38 / 51
  | 3 => 4 / 51
  | 4 => 1 / 17
  | 5 => 3 / 68

/-- **The witness design.**  Parseval holds on the nose. -/
noncomputable def uThreeSixStratumDesign : WeightedDesign 6 3 where
  atom := uThreeSixStratumAtom
  weight := uThreeSixStratumWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [uThreeSixStratumWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [uThreeSixStratumWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [uThreeSixStratumAtom, uThreeSixStratumWeight, atomMatrix,
        Matrix.cons_val_two] <;>
      norm_num

/-! ## Part 2: the antecedent legs -/

/-- **LINE-FREE.**  All twenty distinct triples have nonzero bracket, so the
design realizes the empty line family on the nose. -/
theorem uThreeSixStratumDesign_hasLinePattern :
    HasLinePattern uThreeSixStratumDesign (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, uThreeSixStratumDesign,
            uThreeSixStratumAtom, Matrix.cons_val_two])
          (by decide)

/-- **OFF-CONIC.**  The only symmetric form annihilating all six atoms is zero.
The six quadratic equations are solved by elimination, so no `6x6` determinant
is needed; for the record the Veronese determinant is exactly `2448`. -/
theorem uThreeSixStratumDesign_hasNoCommonQuadric :
    HasNoCommonQuadric uThreeSixStratumDesign.atom := by
  intro form hsymmetric hquadric
  have hsym : ∀ rowIndex colIndex : Fin 3, form colIndex rowIndex = form rowIndex colIndex :=
    fun rowIndex colIndex => congrFun (congrFun hsymmetric rowIndex) colIndex
  have hzero := hquadric 0
  have hone := hquadric 1
  have htwo := hquadric 2
  have hthree := hquadric 3
  have hfour := hquadric 4
  have hfive := hquadric 5
  simp only [uThreeSixStratumDesign, uThreeSixStratumAtom, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hzero hone htwo hthree hfour hfive
  rw [hsym 0 1] at hzero hone hfour
  rw [hsym 0 2] at hthree hfour
  rw [hsym 1 2] at hfour hfive
  have hcornerZero : form 0 0 = 0 := by linarith
  have hmidZero : form 1 1 = 0 := by linarith
  have hlastZero : form 2 2 = 0 := by linarith
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

/-- The base triple's gap, entry by entry.  The third row and column vanish
identically. -/
theorem uThreeSixStratumDesign_baseTripleGap_eq :
    subsetSum uThreeSixStratumDesign ({0, 1, 2} : Finset (Fin 6)) - 1
      = !![(19 : ℝ), -4, 0; -4, 7, 0; 0, 0, 0] := by
  rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [uThreeSixStratumDesign, uThreeSixStratumAtom, atomMatrix, Matrix.sub_apply,
      Matrix.cons_val_two] <;>
    norm_num

/-- The base triple's gap as an explicit sum of squares. -/
theorem uThreeSixStratumDesign_baseTripleGap_form (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ ((subsetSum uThreeSixStratumDesign ({0, 1, 2} : Finset (Fin 6)) - 1)
        *ᵥ probeVec)
      = ((19 * probeVec 0 - 4 * probeVec 1) ^ 2 + 117 * probeVec 1 ^ 2) / 19 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [uThreeSixStratumDesign, uThreeSixStratumAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

/-- **WEAK DOMINATION.**  The base triple dominates. -/
theorem uThreeSixStratumDesign_dominates_baseTriple :
    Dominates uThreeSixStratumDesign ({0, 1, 2} : Finset (Fin 6)) := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 1, 2} : Finset (Fin 6)) fun baseLabel _ =>
      posSemidef_atomMatrix (uThreeSixStratumDesign.atom baseLabel)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, uThreeSixStratumDesign_baseTripleGap_form]
    positivity

/-- The tight direction handed to the residual: the unit normal `e3`, which is
also the design's own atom `2`. -/
def uThreeSixStratumTightDirection : Fin 3 → ℝ := ![0, 0, 1]

theorem uThreeSixStratumTightDirection_ne_zero : uThreeSixStratumTightDirection ≠ 0 := by
  intro hzero
  have hlast := congrFun hzero 2
  simp [uThreeSixStratumTightDirection] at hlast

theorem uThreeSixStratumTightDirection_dotProduct_self :
    uThreeSixStratumTightDirection ⬝ᵥ uThreeSixStratumTightDirection = 1 := by
  simp [uThreeSixStratumTightDirection, dotProduct, Fin.sum_univ_three]

/-- **THE TIGHT DIRECTION IS TIGHT.** -/
theorem uThreeSixStratumDesign_tightDirection_isTight :
    uThreeSixStratumTightDirection
        ⬝ᵥ ((subsetSum uThreeSixStratumDesign ({0, 1, 2} : Finset (Fin 6)) - 1)
          *ᵥ uThreeSixStratumTightDirection) = 0 := by
  rw [uThreeSixStratumDesign_baseTripleGap_form]
  simp [uThreeSixStratumTightDirection]

/-- The base triple does NOT dominate strictly, so the antecedent is met in its
genuine weak-but-not-strict form. -/
theorem uThreeSixStratumDesign_not_posDef_baseTripleGap :
    ¬ (subsetSum uThreeSixStratumDesign ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef :=
  not_posDef_of_tightDirection _ uThreeSixStratumTightDirection_ne_zero
    uThreeSixStratumDesign_tightDirection_isTight

/-- Every atom is heavy: the residual's leverage pin costs nothing here.  Atom
`2` is CRITICAL, with leverage exactly one. -/
theorem uThreeSixStratumDesign_one_le_leverage (label : Fin 6) :
    1 ≤ leverageOf (uThreeSixStratumDesign.atom label) := by
  fin_cases label <;>
    simp [uThreeSixStratumDesign, uThreeSixStratumAtom, leverageOf, Fin.sum_univ_three,
      Matrix.cons_val_two] <;>
    norm_num

/-- **THE ANTECEDENT IS INHABITED.**  Every hypothesis of
`Gtz.BaseTripleTightLineFreeOffConicWeakToStrict` holds at this design, together
with the heaviness pin and the failure of the base triple. -/
theorem uThreeSixStratumDesign_meetsBaseTripleTightAntecedent :
    HasLinePattern uThreeSixStratumDesign (lineFamilyPattern ([] : List (List (Fin 6))))
      ∧ HasNoCommonQuadric uThreeSixStratumDesign.atom
      ∧ Dominates uThreeSixStratumDesign ({0, 1, 2} : Finset (Fin 6))
      ∧ uThreeSixStratumTightDirection ≠ 0
      ∧ uThreeSixStratumTightDirection
          ⬝ᵥ ((subsetSum uThreeSixStratumDesign ({0, 1, 2} : Finset (Fin 6)) - 1)
            *ᵥ uThreeSixStratumTightDirection) = 0
      ∧ (∀ label : Fin 6, 1 ≤ leverageOf (uThreeSixStratumDesign.atom label))
      ∧ ¬ (subsetSum uThreeSixStratumDesign ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef :=
  ⟨uThreeSixStratumDesign_hasLinePattern, uThreeSixStratumDesign_hasNoCommonQuadric,
    uThreeSixStratumDesign_dominates_baseTriple, uThreeSixStratumTightDirection_ne_zero,
    uThreeSixStratumDesign_tightDirection_isTight, uThreeSixStratumDesign_one_le_leverage,
    uThreeSixStratumDesign_not_posDef_baseTripleGap⟩

/-! ## Part 3: the balance family fires -/

/-- The complement triple's largest weight is `4/51`, carried by label `3`. -/
theorem uThreeSixStratumDesign_complementTripleMaxWeight_eq :
    complementTripleMaxWeight uThreeSixStratumDesign = 4 / 51 := by
  simp only [complementTripleMaxWeight, uThreeSixStratumDesign, uThreeSixStratumWeight]
  rw [max_eq_left (by norm_num : (1 : ℝ) / 17 ≤ 4 / 51),
    max_eq_left (by norm_num : (3 : ℝ) / 68 ≤ 4 / 51)]

/-- The base residual's quadratic form, in coordinates. -/
theorem uThreeSixStratumDesign_baseResidual_form (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ (baseResidual uThreeSixStratumDesign ({0, 1, 2} : Finset (Fin 6))
        *ᵥ probeVec)
      = 4 / 17 * probeVec 0 ^ 2 + 6 / 17 * (probeVec 0 * probeVec 1)
        + 12 / 17 * probeVec 1 ^ 2 + 13 / 51 * probeVec 2 ^ 2 := by
  rw [dotProduct_baseResidual_mulVec_eq_sub_baseMass, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [uThreeSixStratumDesign, uThreeSixStratumAtom, uThreeSixStratumWeight, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]
  ring

/-- The residual minus the largest complement weight, as an explicit matrix. -/
noncomputable def uThreeSixStratumShiftedResidual : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(8 : ℝ) / 51, 9 / 51, 0; 9 / 51, 32 / 51, 0; 0, 0, 9 / 51]

/-- The shifted residual is positive definite, by Sylvester on its three leading
minors `8/51`, `175/2601` and `1575/132651`. -/
theorem uThreeSixStratumShiftedResidual_posDef : uThreeSixStratumShiftedResidual.PosDef := by
  rw [uThreeSixStratumShiftedResidual]
  refine posDef_of_leadingMinors_fin_three _ _ _ _ _ _ ?_ ?_ ?_ <;> norm_num

theorem uThreeSixStratumShiftedResidual_form (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ (uThreeSixStratumShiftedResidual *ᵥ probeVec)
      = 8 / 51 * probeVec 0 ^ 2 + 18 / 51 * (probeVec 0 * probeVec 1)
        + 32 / 51 * probeVec 1 ^ 2 + 9 / 51 * probeVec 2 ^ 2 := by
  simp [uThreeSixStratumShiftedResidual, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

/-- **THE SHARP BALANCE HYPOTHESIS HOLDS.**  The residual's quadratic form beats
`4/51` times the squared length at every nonzero probe. -/
theorem uThreeSixStratumDesign_residualExceedsMaxWeight (probeVec : Fin 3 → ℝ)
    (hprobeNe : probeVec ≠ 0) :
    complementTripleMaxWeight uThreeSixStratumDesign * (probeVec ⬝ᵥ probeVec)
      < probeVec ⬝ᵥ (baseResidual uThreeSixStratumDesign ({0, 1, 2} : Finset (Fin 6))
          *ᵥ probeVec) := by
  have hshifted := (Matrix.posDef_iff_dotProduct_mulVec.mp
    uThreeSixStratumShiftedResidual_posDef).2 hprobeNe
  rw [star_trivial, uThreeSixStratumShiftedResidual_form] at hshifted
  rw [uThreeSixStratumDesign_complementTripleMaxWeight_eq,
    uThreeSixStratumDesign_baseResidual_form]
  have hnormSq : probeVec ⬝ᵥ probeVec
      = probeVec 0 ^ 2 + probeVec 1 ^ 2 + probeVec 2 ^ 2 := by
    simp [dotProduct, Fin.sum_univ_three]; ring
  rw [hnormSq]
  linarith

/-- **FAMILY ONE FIRES ON THE STRATUM.**  The complement triple `{3,4,5}`
strictly dominates — the conclusion the balance family advertises, delivered at
a point that really is line-free, off-conic and base-tight. -/
theorem uThreeSixStratumDesign_posDef_complementTripleGap :
    (subsetSum uThreeSixStratumDesign ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef :=
  posDef_subsetSum_complementTriple_of_residualExceedsMaxWeight uThreeSixStratumDesign
    uThreeSixStratumDesign_residualExceedsMaxWeight

/-- The design's base share is `92/51`. -/
theorem uThreeSixStratumDesign_baseTripleShare_eq :
    ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare uThreeSixStratumDesign label
      = 92 / 51 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [atomShare, leverageOf, uThreeSixStratumDesign, uThreeSixStratumAtom,
    uThreeSixStratumWeight, Fin.sum_univ_three, Matrix.cons_val_two]
  norm_num

/-- **THE SCALAR BALANCE TEST FAILS HERE.**  `Gtz.posDef_subsetSum_complementTriple_of_baseTripleShare_lt`
demands a base share below `47/51`, and this design's is `92/51`.  So the scalar
relaxation is strictly weaker than the sharp Loewner form on the live stratum:
only `Gtz.posDef_subsetSum_complementTriple_of_residualExceedsMaxWeight` reaches
this point. -/
theorem uThreeSixStratumDesign_scalarBalanceTest_fails :
    ¬ (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare uThreeSixStratumDesign label
        < 1 - complementTripleMaxWeight uThreeSixStratumDesign) := by
  rw [uThreeSixStratumDesign_baseTripleShare_eq,
    uThreeSixStratumDesign_complementTripleMaxWeight_eq]
  norm_num

/-- The design has a strictly dominating triple, so the obligation's conclusion
holds here. -/
theorem uThreeSixStratumDesign_hasStrictDominator :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum uThreeSixStratumDesign selected - 1).PosDef :=
  ⟨{3, 4, 5}, by decide, uThreeSixStratumDesign_posDef_complementTripleGap⟩

/-- The witness is not a tie. -/
theorem uThreeSixStratumDesign_not_isTie : ¬ IsTie uThreeSixStratumDesign :=
  fun htie => htie.2 {3, 4, 5} (by decide) uThreeSixStratumDesign_posDef_complementTripleGap

/-! ## Part 4: the tight-space dichotomy

`Gtz.baseTripleGap_psd_singular_ne_zero_of_offConic` pins the `U(3,6)` base gap
as a NONZERO singular positive semidefinite form.  A nonzero semidefinite
`3x3` has a tight space of dimension one or two and nothing else, and the two
cases behave differently for the residual: a plane of tight directions lets the
residual pick its normal orthogonal to anything it likes. -/

/-- A direction on which a subset's gap form vanishes. -/
def IsTightDirectionOf {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (direction : Fin rank → ℝ) : Prop :=
  direction ⬝ᵥ ((subsetSum design selected - 1) *ᵥ direction) = 0

/-- Under domination, tightness is exactly membership in the gap's kernel. -/
theorem isTightDirectionOf_iff_mulVec_eq_zero {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (hdominates : Dominates design selected) (direction : Fin rank → ℝ) :
    IsTightDirectionOf design selected direction
      ↔ (subsetSum design selected - 1) *ᵥ direction = 0 := by
  rw [IsTightDirectionOf, ← star_trivial direction]
  exact Matrix.PosSemidef.dotProduct_mulVec_zero_iff hdominates direction

/-- The tight set is closed under linear combination. -/
theorem isTightDirectionOf_add_smul {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hdominates : Dominates design selected)
    {firstDir secondDir : Fin rank → ℝ} (hfirst : IsTightDirectionOf design selected firstDir)
    (hsecond : IsTightDirectionOf design selected secondDir) (firstScale secondScale : ℝ) :
    IsTightDirectionOf design selected (firstScale • firstDir + secondScale • secondDir) := by
  rw [isTightDirectionOf_iff_mulVec_eq_zero design selected hdominates] at hfirst hsecond ⊢
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hfirst, hsecond,
    smul_zero, smul_zero, add_zero]

/-- The tight space is a LINE through the given direction. -/
def HasTightLineAt {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (tightDir : Fin rank → ℝ) : Prop :=
  ∀ other : Fin rank → ℝ, IsTightDirectionOf design selected other →
    ∃ ratio : ℝ, other = ratio • tightDir

/-- **THE FREEDOM OF THE PLANE BRANCH.**  Whatever vector the argument wants to
avoid, a nonzero tight direction orthogonal to it is available. -/
def HasFreeTightDirection {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) : Prop :=
  ∀ probeVec : Fin rank → ℝ, ∃ freeDir : Fin rank → ℝ, freeDir ≠ 0
    ∧ IsTightDirectionOf design selected freeDir ∧ freeDir ⬝ᵥ probeVec = 0

/-- Two non-parallel tight directions give the plane branch's freedom. -/
theorem hasFreeTightDirection_of_nonparallel {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (hdominates : Dominates design selected) {firstDir secondDir : Fin rank → ℝ}
    (hfirstNe : firstDir ≠ 0) (hfirst : IsTightDirectionOf design selected firstDir)
    (hsecond : IsTightDirectionOf design selected secondDir)
    (hnonparallel : ∀ ratio : ℝ, secondDir ≠ ratio • firstDir) :
    HasFreeTightDirection design selected := by
  intro probeVec
  rcases Classical.em (firstDir ⬝ᵥ probeVec = 0) with hflat | hbent
  · exact ⟨firstDir, hfirstNe, hfirst, hflat⟩
  refine ⟨(secondDir ⬝ᵥ probeVec) • firstDir + (-(firstDir ⬝ᵥ probeVec)) • secondDir, ?_,
    isTightDirectionOf_add_smul design selected hdominates hfirst hsecond _ _, ?_⟩
  · intro hcombinationZero
    rw [neg_smul, add_neg_eq_zero] at hcombinationZero
    refine hnonparallel ((secondDir ⬝ᵥ probeVec) / (firstDir ⬝ᵥ probeVec)) ?_
    rw [div_eq_inv_mul, mul_smul, hcombinationZero, inv_smul_smul₀ hbent]
  · simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
    ring

/-- **THE TIGHT-SPACE DICHOTOMY.**  A dominating subset with a nonzero tight
direction either has its whole tight space on that one line, or has a tight
direction orthogonal to every prescribed vector.  Classical, no dimension
theory. -/
theorem hasTightLineAt_or_hasFreeTightDirection {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (hdominates : Dominates design selected) {tightDir : Fin rank → ℝ}
    (htightNe : tightDir ≠ 0) (htight : IsTightDirectionOf design selected tightDir) :
    HasTightLineAt design selected tightDir ∨ HasFreeTightDirection design selected := by
  rcases Classical.em (HasTightLineAt design selected tightDir) with hline | hnotLine
  · exact Or.inl hline
  refine Or.inr ?_
  rw [HasTightLineAt] at hnotLine
  push Not at hnotLine
  obtain ⟨otherDir, hotherTight, hotherNonparallel⟩ := hnotLine
  exact hasFreeTightDirection_of_nonparallel design selected hdominates htightNe htight
    hotherTight fun ratio hparallel => hotherNonparallel ratio hparallel

/-- A nonzero semidefinite gap has a direction that is NOT tight, so the plane
branch really is a plane and not the whole space. -/
theorem exists_not_isTightDirectionOf_of_gap_ne_zero {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (hdominates : Dominates design selected)
    (hgapNe : subsetSum design selected - 1 ≠ 0) :
    ∃ bentDir : Fin rank → ℝ, ¬ IsTightDirectionOf design selected bentDir := by
  by_contra hallTight
  push Not at hallTight
  refine hgapNe ?_
  ext rowIndex colIndex
  have hkernel := (isTightDirectionOf_iff_mulVec_eq_zero design selected hdominates
    (Pi.single colIndex 1)).mp (hallTight (Pi.single colIndex 1))
  have hentry := congrFun hkernel rowIndex
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hentry

/-- **THE `U(3,6)` RANK SPLIT.**  On the residual's antecedent the base gap is
nonzero, singular and semidefinite; so either its tight space is the single line
through the given tight direction, or it is a genuine plane — a whole circle of
tight directions, with a direction available orthogonal to anything, while some
direction still fails to be tight.  Nothing else can happen. -/
theorem uThreeSix_baseTripleTightSpace_dichotomy (design : WeightedDesign 6 3)
    (hoffConic : HasNoCommonQuadric design.atom)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir
      ∨ (HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))
          ∧ ∃ bentDir : Fin 3 → ℝ,
            ¬ IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) bentDir) := by
  have hgapNe := (baseTripleGap_psd_singular_ne_zero_of_offConic design hoffConic hdominates
    htight).2.2
  rcases hasTightLineAt_or_hasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))
    hdominates htightNe htight with hline | hfree
  · exact Or.inl hline
  · exact Or.inr ⟨hfree, exists_not_isTightDirectionOf_of_gap_ne_zero design
      ({0, 1, 2} : Finset (Fin 6)) hdominates hgapNe⟩

/-- **THE WITNESS SITS IN THE LINE BRANCH.**  Its base gap has the `2x2` plane
block nonsingular, so the tight space is exactly the line through `e3`. -/
theorem uThreeSixStratumDesign_hasTightLineAt :
    HasTightLineAt uThreeSixStratumDesign ({0, 1, 2} : Finset (Fin 6))
      uThreeSixStratumTightDirection := by
  intro other hother
  rw [IsTightDirectionOf, uThreeSixStratumDesign_baseTripleGap_form] at hother
  have hsquares : (19 * other 0 - 4 * other 1) ^ 2 + 117 * other 1 ^ 2 = 0 := by
    field_simp at hother
    linarith
  have hcornerSquare : (19 * other 0 - 4 * other 1) ^ 2 = 0 := by
    linarith [sq_nonneg (19 * other 0 - 4 * other 1), sq_nonneg (other 1)]
  have hmidSquare : other 1 ^ 2 = 0 := by
    linarith [sq_nonneg (19 * other 0 - 4 * other 1), sq_nonneg (other 1)]
  have hmidZero : other 1 = 0 := sq_eq_zero_iff.mp hmidSquare
  have hcornerZero : other 0 = 0 := by
    have hlinear : 19 * other 0 - 4 * other 1 = 0 := sq_eq_zero_iff.mp hcornerSquare
    rw [hmidZero] at hlinear
    linarith
  refine ⟨other 2, ?_⟩
  funext coord
  fin_cases coord <;>
    simp [uThreeSixStratumTightDirection, hcornerZero, hmidZero]

/-! ### The plane branch is not obstructed

The plane branch is exactly the case where the base gap is a single rank-one
atom.  Two facts make it a live possibility rather than a formality: such a gap
really does hand over the whole plane of tight directions, and a base triple
realizing one need not be orthogonal — so
`Gtz.not_hasNoCommonQuadric_of_orthogonalTriple`, the only shipped obstruction
that bites on triples, does not exclude it. -/

/-- **A RANK-ONE GAP GIVES THE WHOLE PLANE.**  Stated with the gap's vector along
the last axis, which costs no generality: any rank-one gap becomes this after an
orthogonal change of coordinates. -/
theorem hasFreeTightDirection_of_gap_eq_lastAxisAtom {size : ℕ}
    (design : WeightedDesign size 3) (selected : Finset (Fin size)) (gapScale : ℝ)
    (hgap : subsetSum design selected - 1 = atomMatrix ![0, 0, gapScale]) :
    HasFreeTightDirection design selected := by
  have hdominates : Dominates design selected := by
    rw [Dominates, hgap]
    exact posSemidef_atomMatrix _
  have hflatIsTight : ∀ direction : Fin 3 → ℝ, direction 2 = 0 →
      IsTightDirectionOf design selected direction := by
    intro direction hlast
    rw [IsTightDirectionOf, hgap, dotProduct_atomMatrix_mulVec]
    simp [dotProduct, Fin.sum_univ_three, hlast]
  refine hasFreeTightDirection_of_nonparallel design selected hdominates
    (firstDir := ![1, 0, 0]) (secondDir := ![0, 1, 0]) ?_
    (hflatIsTight _ (by simp)) (hflatIsTight _ (by simp)) ?_
  · intro hzero
    have hentry := congrFun hzero 0
    simp at hentry
  · intro ratio hparallel
    have hentry := congrFun hparallel 1
    simp at hentry

/-- **THE OPERATIONAL FORM OF THE PLANE BRANCH.**  Whichever atom the argument
names, the plane branch supplies a tight direction that atom is FLAT against.
Composed with `Gtz.shadowPairing_self_eq_leverageOf_of_normalReading_eq_zero`
this turns the chosen atom's shadow leverage into its leverage, which is the
hypothesis shape of the lift criterion's line-normal collapse. -/
theorem exists_flat_tightDirection_at_label {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hfree : HasFreeTightDirection design selected)
    (label : Fin size) :
    ∃ freeDir : Fin 3 → ℝ, freeDir ≠ 0 ∧ IsTightDirectionOf design selected freeDir
      ∧ normalReading design freeDir label = 0 := by
  obtain ⟨freeDir, hfreeNe, hfreeTight, hflat⟩ := hfree (design.atom label)
  exact ⟨freeDir, hfreeNe, hfreeTight, by rw [normalReading, dotProduct_comm]; exact hflat⟩

/-- **THE PLANE-BRANCH WITNESS'S ATOMS.**  Labels `0,1,2` are the columns of
`diag(1,1,5/3)` times a rational rotation, so their gap is a single rank-one
atom; labels `3,4,5` are integral. -/
noncomputable def planeBranchAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![2 / 3, 1 / 3, 10 / 9]
  | 1 => ![-(2 / 3), 2 / 3, 5 / 9]
  | 2 => ![1 / 3, 2 / 3, -(10 / 9)]
  | 3 => ![-2, -2, -2]
  | 4 => ![2, -2, 0]
  | 5 => ![1, 1, -1]

/-- Exact forty-firsts; the base triple carries three equal weights. -/
noncomputable def planeBranchWeight : Fin 6 → ℝ
  | 0 => 9 / 41
  | 1 => 9 / 41
  | 2 => 9 / 41
  | 3 => 2 / 41
  | 4 => 4 / 41
  | 5 => 8 / 41

/-- **THE PLANE-BRANCH WITNESS.** -/
noncomputable def planeBranchDesign : WeightedDesign 6 3 where
  atom := planeBranchAtom
  weight := planeBranchWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [planeBranchWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [planeBranchWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [planeBranchAtom, planeBranchWeight, atomMatrix, Matrix.cons_val_two] <;>
      norm_num

theorem planeBranchDesign_hasLinePattern :
    HasLinePattern planeBranchDesign (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, planeBranchDesign,
            planeBranchAtom, Matrix.cons_val_two])
          (by decide)

/-- Off-conic, again by elimination.  (Veronese determinant `-26240/729`.) -/
theorem planeBranchDesign_hasNoCommonQuadric :
    HasNoCommonQuadric planeBranchDesign.atom := by
  intro form hsymmetric hquadric
  have hsym : ∀ rowIndex colIndex : Fin 3, form colIndex rowIndex = form rowIndex colIndex :=
    fun rowIndex colIndex => congrFun (congrFun hsymmetric rowIndex) colIndex
  have hzero := hquadric 0
  have hone := hquadric 1
  have htwo := hquadric 2
  have hthree := hquadric 3
  have hfour := hquadric 4
  have hfive := hquadric 5
  simp only [planeBranchDesign, planeBranchAtom, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hzero hone htwo hthree hfour hfive
  rw [hsym 0 1] at hzero hone htwo hthree hfour hfive
  rw [hsym 0 2] at hzero hone htwo hthree hfive
  rw [hsym 1 2] at hzero hone htwo hthree hfive
  have hcornerZero : form 0 0 = 0 := by linarith
  have hmidZero : form 1 1 = 0 := by linarith
  have hlastZero : form 2 2 = 0 := by linarith
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

/-- **THE BASE GAP IS ONE RANK-ONE ATOM.**  Not merely singular: the whole
`xy`-plane is tight. -/
theorem planeBranchDesign_baseTripleGap_eq :
    subsetSum planeBranchDesign ({0, 1, 2} : Finset (Fin 6)) - 1
      = atomMatrix ![0, 0, 4 / 3] := by
  rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [planeBranchDesign, planeBranchAtom, atomMatrix, Matrix.sub_apply,
      Matrix.cons_val_two] <;>
    norm_num

theorem planeBranchDesign_dominates_baseTriple :
    Dominates planeBranchDesign ({0, 1, 2} : Finset (Fin 6)) := by
  rw [Dominates, planeBranchDesign_baseTripleGap_eq]
  exact posSemidef_atomMatrix _

/-- The witness's declared tight direction: the first axis, one point of the
whole tight circle. -/
def planeBranchTightDirection : Fin 3 → ℝ := ![1, 0, 0]

theorem planeBranchTightDirection_ne_zero : planeBranchTightDirection ≠ 0 := by
  intro hzero
  have hfirst := congrFun hzero 0
  simp [planeBranchTightDirection] at hfirst

theorem planeBranchDesign_tightDirection_isTight :
    IsTightDirectionOf planeBranchDesign ({0, 1, 2} : Finset (Fin 6))
      planeBranchTightDirection := by
  rw [IsTightDirectionOf, planeBranchDesign_baseTripleGap_eq, dotProduct_atomMatrix_mulVec]
  simp [planeBranchTightDirection, dotProduct, Fin.sum_univ_three]

theorem planeBranchDesign_not_posDef_baseTripleGap :
    ¬ (subsetSum planeBranchDesign ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef :=
  not_posDef_of_tightDirection _ planeBranchTightDirection_ne_zero
    planeBranchDesign_tightDirection_isTight

theorem planeBranchDesign_one_le_leverage (label : Fin 6) :
    1 ≤ leverageOf (planeBranchDesign.atom label) := by
  fin_cases label <;>
    simp [planeBranchDesign, planeBranchAtom, leverageOf, Fin.sum_univ_three,
      Matrix.cons_val_two] <;>
    norm_num

/-- **THE PLANE BRANCH IS INHABITED.**  The dichotomy's second alternative holds
here: a whole circle of tight directions, one orthogonal to whatever the
argument names. -/
theorem planeBranchDesign_hasFreeTightDirection :
    HasFreeTightDirection planeBranchDesign ({0, 1, 2} : Finset (Fin 6)) :=
  hasFreeTightDirection_of_gap_eq_lastAxisAtom planeBranchDesign
    ({0, 1, 2} : Finset (Fin 6)) (4 / 3) planeBranchDesign_baseTripleGap_eq

/-- The base triple is pairwise non-orthogonal, so
`Gtz.not_hasNoCommonQuadric_of_orthogonalTriple` never had a chance to exclude
it — consistent with the off-conicity just proved. -/
theorem planeBranchDesign_baseTriple_not_orthogonal :
    planeBranchDesign.atom 0 ⬝ᵥ planeBranchDesign.atom 1 ≠ 0
      ∧ planeBranchDesign.atom 0 ⬝ᵥ planeBranchDesign.atom 2 ≠ 0
      ∧ planeBranchDesign.atom 1 ⬝ᵥ planeBranchDesign.atom 2 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [planeBranchDesign, planeBranchAtom, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two]

/-- **THE PLANE-BRANCH POINT MEETS THE FULL ANTECEDENT.** -/
theorem planeBranchDesign_meetsBaseTripleTightAntecedent :
    HasLinePattern planeBranchDesign (lineFamilyPattern ([] : List (List (Fin 6))))
      ∧ HasNoCommonQuadric planeBranchDesign.atom
      ∧ Dominates planeBranchDesign ({0, 1, 2} : Finset (Fin 6))
      ∧ planeBranchTightDirection ≠ 0
      ∧ planeBranchTightDirection
          ⬝ᵥ ((subsetSum planeBranchDesign ({0, 1, 2} : Finset (Fin 6)) - 1)
            *ᵥ planeBranchTightDirection) = 0
      ∧ (∀ label : Fin 6, 1 ≤ leverageOf (planeBranchDesign.atom label))
      ∧ ¬ (subsetSum planeBranchDesign ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef :=
  ⟨planeBranchDesign_hasLinePattern, planeBranchDesign_hasNoCommonQuadric,
    planeBranchDesign_dominates_baseTriple, planeBranchTightDirection_ne_zero,
    planeBranchDesign_tightDirection_isTight, planeBranchDesign_one_le_leverage,
    planeBranchDesign_not_posDef_baseTripleGap⟩

/-- The plane-branch witness's complement max weight. -/
theorem planeBranchDesign_complementTripleMaxWeight_eq :
    complementTripleMaxWeight planeBranchDesign = 8 / 41 := by
  simp only [complementTripleMaxWeight, planeBranchDesign, planeBranchWeight]
  rw [max_eq_right (by norm_num : (2 : ℝ) / 41 ≤ 4 / 41),
    max_eq_right (by norm_num : (4 : ℝ) / 41 ≤ 8 / 41)]

theorem planeBranchDesign_baseResidual_form (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ (baseResidual planeBranchDesign ({0, 1, 2} : Finset (Fin 6)) *ᵥ probeVec)
      = 32 / 41 * probeVec 0 ^ 2 + 32 / 41 * probeVec 1 ^ 2 + 16 / 41 * probeVec 2 ^ 2 := by
  rw [dotProduct_baseResidual_mulVec_eq_sub_baseMass, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [planeBranchDesign, planeBranchAtom, planeBranchWeight, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]
  ring

noncomputable def planeBranchShiftedResidual : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(24 : ℝ) / 41, 0, 0; 0, 24 / 41, 0; 0, 0, 8 / 41]

theorem planeBranchShiftedResidual_posDef : planeBranchShiftedResidual.PosDef := by
  rw [planeBranchShiftedResidual]
  refine posDef_of_leadingMinors_fin_three _ _ _ _ _ _ ?_ ?_ ?_ <;> norm_num

theorem planeBranchShiftedResidual_form (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ (planeBranchShiftedResidual *ᵥ probeVec)
      = 24 / 41 * probeVec 0 ^ 2 + 24 / 41 * probeVec 1 ^ 2 + 8 / 41 * probeVec 2 ^ 2 := by
  simp [planeBranchShiftedResidual, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

theorem planeBranchDesign_residualExceedsMaxWeight (probeVec : Fin 3 → ℝ)
    (hprobeNe : probeVec ≠ 0) :
    complementTripleMaxWeight planeBranchDesign * (probeVec ⬝ᵥ probeVec)
      < probeVec ⬝ᵥ (baseResidual planeBranchDesign ({0, 1, 2} : Finset (Fin 6))
          *ᵥ probeVec) := by
  have hshifted := (Matrix.posDef_iff_dotProduct_mulVec.mp
    planeBranchShiftedResidual_posDef).2 hprobeNe
  rw [star_trivial, planeBranchShiftedResidual_form] at hshifted
  rw [planeBranchDesign_complementTripleMaxWeight_eq, planeBranchDesign_baseResidual_form]
  have hnormSq : probeVec ⬝ᵥ probeVec
      = probeVec 0 ^ 2 + probeVec 1 ^ 2 + probeVec 2 ^ 2 := by
    simp [dotProduct, Fin.sum_univ_three]; ring
  rw [hnormSq]
  linarith

/-- **FAMILY ONE FIRES IN THE PLANE BRANCH TOO.** -/
theorem planeBranchDesign_posDef_complementTripleGap :
    (subsetSum planeBranchDesign ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef :=
  posDef_subsetSum_complementTriple_of_residualExceedsMaxWeight planeBranchDesign
    planeBranchDesign_residualExceedsMaxWeight

theorem planeBranchDesign_baseTripleShare_eq :
    ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare planeBranchDesign label = 43 / 41 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [atomShare, leverageOf, planeBranchDesign, planeBranchAtom, planeBranchWeight,
    Fin.sum_univ_three, Matrix.cons_val_two]
  norm_num

/-- The scalar balance test fails at the plane-branch point as well: `43/41`
against the demanded `33/41`.  Two independent points of the stratum, the same
verdict. -/
theorem planeBranchDesign_scalarBalanceTest_fails :
    ¬ (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare planeBranchDesign label
        < 1 - complementTripleMaxWeight planeBranchDesign) := by
  rw [planeBranchDesign_baseTripleShare_eq, planeBranchDesign_complementTripleMaxWeight_eq]
  norm_num

theorem planeBranchDesign_not_isTie : ¬ IsTie planeBranchDesign :=
  fun htie => htie.2 {3, 4, 5} (by decide) planeBranchDesign_posDef_complementTripleGap

/-- **BOTH BRANCHES OF THE DICHOTOMY ARE INHABITED ON THE FULL ANTECEDENT.**
The line branch at `Gtz.uThreeSixStratumDesign`, the plane branch at
`Gtz.planeBranchDesign`; neither alternative of
`Gtz.uThreeSix_baseTripleTightSpace_dichotomy` is vacuous. -/
theorem uThreeSix_bothTightSpaceBranches_inhabited :
    (HasTightLineAt uThreeSixStratumDesign ({0, 1, 2} : Finset (Fin 6))
        uThreeSixStratumTightDirection
      ∧ HasNoCommonQuadric uThreeSixStratumDesign.atom
      ∧ Dominates uThreeSixStratumDesign ({0, 1, 2} : Finset (Fin 6)))
    ∧ (HasFreeTightDirection planeBranchDesign ({0, 1, 2} : Finset (Fin 6))
      ∧ HasNoCommonQuadric planeBranchDesign.atom
      ∧ Dominates planeBranchDesign ({0, 1, 2} : Finset (Fin 6))) :=
  ⟨⟨uThreeSixStratumDesign_hasTightLineAt, uThreeSixStratumDesign_hasNoCommonQuadric,
      uThreeSixStratumDesign_dominates_baseTriple⟩,
    ⟨planeBranchDesign_hasFreeTightDirection, planeBranchDesign_hasNoCommonQuadric,
      planeBranchDesign_dominates_baseTriple⟩⟩

/-! ## Part 5: the lift criterion at the tight direction -/

/-- **A STRUCTURAL BOUNDARY POINT OF THE LIFT CRITERION.**  If both pair members
are orthogonal to the unit normal and the third atom IS the normal — zero shadow,
unit reading — then the lift margin vanishes identically.  A tie must sit on the
boundary of a sharp criterion, and so must this configuration. -/
theorem liftMarginOf_eq_zero_of_flatPair_of_normalThird
    (shadowFirstNorm shadowCross shadowSecondNorm : ℝ) :
    liftMarginOf shadowFirstNorm shadowCross shadowSecondNorm 0 0 0 0 0 1 = 0 := by
  simp only [liftMarginOf, liftReadingOf, liftLeverageOf, liftDemandOf,
    shadowGapDeterminantOf]
  ring

/-- The shadow Gram of the two planar base atoms at the tight direction. -/
theorem uThreeSixStratumDesign_shadowPairing_basePair :
    shadowPairing uThreeSixStratumDesign uThreeSixStratumTightDirection 0 0 = 20
      ∧ shadowPairing uThreeSixStratumDesign uThreeSixStratumTightDirection 0 1 = -4
      ∧ shadowPairing uThreeSixStratumDesign uThreeSixStratumTightDirection 1 1 = 8 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [shadowPairing, normalReading, uThreeSixStratumDesign, uThreeSixStratumAtom,
      uThreeSixStratumTightDirection, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

/-- The planar base pair strictly dominates the shadow design at the tight
direction: corner `19`, determinant `117`. -/
theorem uThreeSixStratumDesign_shadowGapDeterminant_basePair :
    shadowGapDeterminant uThreeSixStratumDesign uThreeSixStratumTightDirection 0 1 = 117 := by
  obtain ⟨hcorner, hcross, hdiag⟩ := uThreeSixStratumDesign_shadowPairing_basePair
  rw [shadowGapDeterminant, hcorner, hcross, hdiag, shadowGapDeterminantOf]
  norm_num

theorem uThreeSixStratumDesign_shadowCorner_basePair_pos :
    0 < shadowPairing uThreeSixStratumDesign uThreeSixStratumTightDirection 0 0 - 1 := by
  rw [uThreeSixStratumDesign_shadowPairing_basePair.1]
  norm_num

/-- **EXACT BOUNDARY.**  At the tight direction the base triple's lift margin is
exactly zero — the criterion's sharp boundary, hit on the nose by a design that
is NOT a tie.  The reason is structural: the base pair is flat at `e3` and the
third base atom IS `e3`. -/
theorem uThreeSixStratumDesign_liftMargin_baseTriple_eq_zero :
    liftMargin uThreeSixStratumDesign uThreeSixStratumTightDirection 0 1 2 = 0 := by
  norm_num [liftMargin, shadowPairing, normalReading, uThreeSixStratumDesign,
    uThreeSixStratumAtom, uThreeSixStratumTightDirection, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two, liftMarginOf, liftReadingOf, liftLeverageOf, liftDemandOf,
    shadowGapDeterminantOf]

/-- Swapping the third label to `5` moves the margin to `32175`.  Note
`32175 = 117 * 275`: the shadow-gap determinant times the triple gap's
determinant, exactly as the lift identity predicts. -/
theorem uThreeSixStratumDesign_liftMargin_zeroOneFive_eq :
    liftMargin uThreeSixStratumDesign uThreeSixStratumTightDirection 0 1 5 = 32175 := by
  norm_num [liftMargin, shadowPairing, normalReading, uThreeSixStratumDesign,
    uThreeSixStratumAtom, uThreeSixStratumTightDirection, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two, liftMarginOf, liftReadingOf, liftLeverageOf, liftDemandOf,
    shadowGapDeterminantOf]

/-- **A SECOND STRICT DOMINATOR, THROUGH THE CRITERION.**  The triple `{0,1,5}`
dominates strictly, obtained from the lift criterion at the tight direction the
antecedent already hands over. -/
theorem uThreeSixStratumDesign_posDef_zeroOneFiveGap :
    (subsetSum uThreeSixStratumDesign ({0, 1, 5} : Finset (Fin 6)) - 1).PosDef := by
  refine (posDef_tripleGap_iff_pos_liftMargin uThreeSixStratumDesign
    uThreeSixStratumTightDirection_dotProduct_self 0 1 5 (by decide) (by decide) (by decide)
    uThreeSixStratumDesign_shadowCorner_basePair_pos
    (by rw [uThreeSixStratumDesign_shadowGapDeterminant_basePair]; norm_num)).mpr ?_
  rw [uThreeSixStratumDesign_liftMargin_zeroOneFive_eq]
  norm_num

/-- The same pair against the complement atom `4` gives `-23634 = 117 * (-202)`:
the criterion discriminates, it does not merely certify. -/
theorem uThreeSixStratumDesign_liftMargin_zeroOneFour_eq :
    liftMargin uThreeSixStratumDesign uThreeSixStratumTightDirection 0 1 4 = -23634 := by
  norm_num [liftMargin, shadowPairing, normalReading, uThreeSixStratumDesign,
    uThreeSixStratumAtom, uThreeSixStratumTightDirection, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two, liftMarginOf, liftReadingOf, liftLeverageOf, liftDemandOf,
    shadowGapDeterminantOf]

/-- **A NEGATIVE, THROUGH THE SAME CRITERION.**  `{0,1,4}` does NOT dominate
strictly.  So at the tight direction the base pair decides all four completions,
accepting exactly one of them. -/
theorem uThreeSixStratumDesign_not_posDef_zeroOneFourGap :
    ¬ (subsetSum uThreeSixStratumDesign ({0, 1, 4} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  have hmargin := (posDef_tripleGap_iff_pos_liftMargin uThreeSixStratumDesign
    uThreeSixStratumTightDirection_dotProduct_self 0 1 4 (by decide) (by decide) (by decide)
    uThreeSixStratumDesign_shadowCorner_basePair_pos
    (by rw [uThreeSixStratumDesign_shadowGapDeterminant_basePair]; norm_num)).mp hposDef
  rw [uThreeSixStratumDesign_liftMargin_zeroOneFour_eq] at hmargin
  norm_num at hmargin

/-- **THE CRITERION SEES THE BASE TRIPLE FAIL.**  Read the other way, the exact
zero of the margin reproves that `{0,1,2}` is not strict — an independent route
to `Gtz.uThreeSixStratumDesign_not_posDef_baseTripleGap`, through the criterion
rather than through the tight direction. -/
theorem uThreeSixStratumDesign_criterion_rejects_baseTriple :
    ¬ (subsetSum uThreeSixStratumDesign ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  have hmargin := (posDef_tripleGap_iff_pos_liftMargin uThreeSixStratumDesign
    uThreeSixStratumTightDirection_dotProduct_self 0 1 2 (by decide) (by decide) (by decide)
    uThreeSixStratumDesign_shadowCorner_basePair_pos
    (by rw [uThreeSixStratumDesign_shadowGapDeterminant_basePair]; norm_num)).mp hposDef
  rw [uThreeSixStratumDesign_liftMargin_baseTriple_eq_zero] at hmargin
  exact lt_irrefl 0 hmargin

/-! ## Part 6: the scalar balance test is not vacuous either

Both witnesses above defeat the scalar form of family one, which invites the
conclusion that the scalar relaxation never reaches the line-free stratum.  It
does.  A third rational antecedent point has base share `62/121` against a
threshold of `203/363`, so
`Gtz.posDef_subsetSum_complementTriple_of_baseTripleShare_lt` fires there on its
own — no Loewner comparison needed.  The scalar branch and the sharp branch are
therefore both inhabited, with the sharp one strictly larger. -/

/-- The scalar-branch witness's atoms. -/
noncomputable def scalarBranchAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![-2, 0, 0]
  | 1 => ![-4, 4, 0]
  | 2 => ![0, 0, 1]
  | 3 => ![0, -1, 5 / 4]
  | 4 => ![-1, -(3 / 4), -(1 / 2)]
  | 5 => ![-4, 5, 4]

/-- Exact one-thousand-four-hundred-and-fifty-seconds. -/
noncomputable def scalarBranchWeight : Fin 6 → ℝ
  | 0 => 103 / 1452
  | 1 => 5 / 1452
  | 2 => 43 / 363
  | 3 => 128 / 363
  | 4 => 160 / 363
  | 5 => 5 / 363

/-- **THE SCALAR-BRANCH WITNESS.** -/
noncomputable def scalarBranchDesign : WeightedDesign 6 3 where
  atom := scalarBranchAtom
  weight := scalarBranchWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [scalarBranchWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [scalarBranchWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [scalarBranchAtom, scalarBranchWeight, atomMatrix, Matrix.cons_val_two] <;>
      norm_num

theorem scalarBranchDesign_hasLinePattern :
    HasLinePattern scalarBranchDesign (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, scalarBranchDesign,
            scalarBranchAtom, Matrix.cons_val_two])
          (by decide)

/-- Off-conic; the symmetry relations go to `linarith` as extra equations rather
than through rewriting, which is the robust form of the elimination.  (Veronese
determinant `2904`.) -/
theorem scalarBranchDesign_hasNoCommonQuadric :
    HasNoCommonQuadric scalarBranchDesign.atom := by
  intro form hsymmetric hquadric
  have hsym : ∀ rowIndex colIndex : Fin 3, form colIndex rowIndex = form rowIndex colIndex :=
    fun rowIndex colIndex => congrFun (congrFun hsymmetric rowIndex) colIndex
  have hsymCross := hsym 0 1
  have hsymUp := hsym 0 2
  have hsymSide := hsym 1 2
  have hzero := hquadric 0
  have hone := hquadric 1
  have htwo := hquadric 2
  have hthree := hquadric 3
  have hfour := hquadric 4
  have hfive := hquadric 5
  simp only [scalarBranchDesign, scalarBranchAtom, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hzero hone htwo hthree hfour hfive
  have hcornerZero : form 0 0 = 0 := by linarith
  have hmidZero : form 1 1 = 0 := by linarith
  have hlastZero : form 2 2 = 0 := by linarith
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
      | exact hsymCross.trans hcrossZero
      | exact hsymUp.trans hupZero
      | exact hsymSide.trans hsideZero

theorem scalarBranchDesign_baseTripleGap_form (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ ((subsetSum scalarBranchDesign ({0, 1, 2} : Finset (Fin 6)) - 1)
        *ᵥ probeVec)
      = ((19 * probeVec 0 - 16 * probeVec 1) ^ 2 + 29 * probeVec 1 ^ 2) / 19 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [scalarBranchDesign, scalarBranchAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

theorem scalarBranchDesign_dominates_baseTriple :
    Dominates scalarBranchDesign ({0, 1, 2} : Finset (Fin 6)) := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 1, 2} : Finset (Fin 6)) fun baseLabel _ =>
      posSemidef_atomMatrix (scalarBranchDesign.atom baseLabel)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, scalarBranchDesign_baseTripleGap_form]
    positivity

theorem scalarBranchDesign_tightDirection_isTight :
    uThreeSixStratumTightDirection
        ⬝ᵥ ((subsetSum scalarBranchDesign ({0, 1, 2} : Finset (Fin 6)) - 1)
          *ᵥ uThreeSixStratumTightDirection) = 0 := by
  rw [scalarBranchDesign_baseTripleGap_form]
  simp [uThreeSixStratumTightDirection]

theorem scalarBranchDesign_not_posDef_baseTripleGap :
    ¬ (subsetSum scalarBranchDesign ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef :=
  not_posDef_of_tightDirection _ uThreeSixStratumTightDirection_ne_zero
    scalarBranchDesign_tightDirection_isTight

theorem scalarBranchDesign_one_le_leverage (label : Fin 6) :
    1 ≤ leverageOf (scalarBranchDesign.atom label) := by
  fin_cases label <;>
    simp [scalarBranchDesign, scalarBranchAtom, leverageOf, Fin.sum_univ_three,
      Matrix.cons_val_two] <;>
    norm_num

theorem scalarBranchDesign_complementTripleMaxWeight_eq :
    complementTripleMaxWeight scalarBranchDesign = 160 / 363 := by
  simp only [complementTripleMaxWeight, scalarBranchDesign, scalarBranchWeight]
  rw [max_eq_right (by norm_num : (128 : ℝ) / 363 ≤ 160 / 363),
    max_eq_left (by norm_num : (5 : ℝ) / 363 ≤ 160 / 363)]

theorem scalarBranchDesign_baseTripleShare_eq :
    ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare scalarBranchDesign label
      = 62 / 121 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [atomShare, leverageOf, scalarBranchDesign, scalarBranchAtom, scalarBranchWeight,
    Fin.sum_univ_three, Matrix.cons_val_two]
  norm_num

/-- **THE SCALAR TEST FIRES HERE.**  `62/121 < 203/363`. -/
theorem scalarBranchDesign_scalarBalanceTest_holds :
    ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare scalarBranchDesign label
      < 1 - complementTripleMaxWeight scalarBranchDesign := by
  rw [scalarBranchDesign_baseTripleShare_eq, scalarBranchDesign_complementTripleMaxWeight_eq]
  norm_num

/-- The cheapest reduction in the file delivers a strict dominator at this
point, with no Loewner comparison anywhere. -/
theorem scalarBranchDesign_posDef_complementTripleGap :
    (subsetSum scalarBranchDesign ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef :=
  posDef_subsetSum_complementTriple_of_baseTripleShare_lt scalarBranchDesign
    scalarBranchDesign_scalarBalanceTest_holds

theorem scalarBranchDesign_not_isTie : ¬ IsTie scalarBranchDesign :=
  fun htie => htie.2 {3, 4, 5} (by decide) scalarBranchDesign_posDef_complementTripleGap

/-- **THE SCALAR-BRANCH POINT MEETS THE FULL ANTECEDENT.** -/
theorem scalarBranchDesign_meetsBaseTripleTightAntecedent :
    HasLinePattern scalarBranchDesign (lineFamilyPattern ([] : List (List (Fin 6))))
      ∧ HasNoCommonQuadric scalarBranchDesign.atom
      ∧ Dominates scalarBranchDesign ({0, 1, 2} : Finset (Fin 6))
      ∧ uThreeSixStratumTightDirection ≠ 0
      ∧ uThreeSixStratumTightDirection
          ⬝ᵥ ((subsetSum scalarBranchDesign ({0, 1, 2} : Finset (Fin 6)) - 1)
            *ᵥ uThreeSixStratumTightDirection) = 0
      ∧ (∀ label : Fin 6, 1 ≤ leverageOf (scalarBranchDesign.atom label))
      ∧ ¬ (subsetSum scalarBranchDesign ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef :=
  ⟨scalarBranchDesign_hasLinePattern, scalarBranchDesign_hasNoCommonQuadric,
    scalarBranchDesign_dominates_baseTriple, uThreeSixStratumTightDirection_ne_zero,
    scalarBranchDesign_tightDirection_isTight, scalarBranchDesign_one_le_leverage,
    scalarBranchDesign_not_posDef_baseTripleGap⟩

/-- **THE SCALAR RELAXATION IS STRICTLY WEAKER, AND BOTH SIDES ARE INHABITED.**
Family one's scalar test fires at `Gtz.scalarBranchDesign` and fails at
`Gtz.uThreeSixStratumDesign`, where the sharp Loewner test fires instead. -/
theorem scalarBalanceTest_strictlyWeaker_and_inhabited :
    (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare scalarBranchDesign label
        < 1 - complementTripleMaxWeight scalarBranchDesign)
      ∧ ¬ (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare uThreeSixStratumDesign label
        < 1 - complementTripleMaxWeight uThreeSixStratumDesign)
      ∧ (subsetSum uThreeSixStratumDesign ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef :=
  ⟨scalarBranchDesign_scalarBalanceTest_holds, uThreeSixStratumDesign_scalarBalanceTest_fails,
    uThreeSixStratumDesign_posDef_complementTripleGap⟩

end Gtz

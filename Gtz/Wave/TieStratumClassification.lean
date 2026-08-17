/-
# The `(6,3)` tie strata, and the wedge Parseval law

Every theorem in this module is UNCONDITIONAL.  None of them is equivalent to
`Gtz.HingeHoldsAtSize 6 3`.  Read `Gtz/Wave/OnPathRegistryCollapse.lean` first:
a Prop of the shape `∀ design, IsPrimitiveDesign design → IsTie design → …` is
IMPLIED by the hinge, so proving one unconditionally is progress and proving the
hinge from one is not possible.  This module carves strata OFF the open cell.
It does not reformulate the open cell.

## What this module closes

* **The stressed arm.**  A `(6,3)` tie that carries a nonzero stress has a
  parallel pair.  The trichotomy's branch (ii) and branch (iii) are both closed
  unconditionally in the tree, so only branch (i) survives, and branch (i) IS
  stress-freeness.  Nobody had assembled the two closed branches into the
  positive statement.
* **The conic stratum.**  Six directions on a common conic carry a stress, so
  every `(6,3)` tie on a conic has a parallel pair.  Equivalently: the six
  directions of a PRIMITIVE `(6,3)` tie are a basis of the symmetric three by
  three matrices, and lie on NO conic.
* **The coplanar quadruple.**  Four atoms in one plane and a cross axis on the
  other two give a line-pair conic, hence a stress.  So no plane holds four
  atoms of a primitive `(6,3)` tie, and at least three atoms sit off every
  plane.  This sharpens the landed `Gtz.two_le_card_offPlane_of_isTie` by one.
* **The direction count.**  A design whose atoms occupy fewer lines than labels
  has a parallel pair.  This needs no tie and no rank.

## The new law

`Gtz.wedgeParseval` states that the fifteen cross products of a rank-three
design form a Parseval frame with weights `t_c t_d`:

    sum over c, sum over d of t_c t_d [a_c, a_d, x]^2  =  2 (x . x)

for EVERY probe `x`.  The second exterior power of a weighted design is a
weighted design.  The tree carried only the level-one reading
(`Gtz.sum_weight_mul_atomBracket_sq`, Parseval at ONE fixed cross axis); this is
the level-two reading, at an arbitrary probe, and it is a different identity.

Three consequences follow.

* `Gtz.weight_mul_crossAxisBudget_le_one` — the PAIR share ceiling
  `t_c t_d (l_c l_d - <a_c, a_d>^2) <= 1`, the exact analogue one level up of
  `Gtz.weighted_leverage_le_one`, sharp at the orthonormal design.
* `Gtz.sum_share_sq_le_rank` — the SHARE SECOND MOMENT law
  `sum over c of (t_c l_c)^2 <= rank`, at every rank and every size, sharp
  exactly at the orthonormal design.
* `Gtz.sum_pair_crossAxisBudget_eq` — the exact pair total
  `sum over c, sum over d of t_c t_d (l_c l_d - <a_c, a_d>^2) = rank^2 - rank`.

Reading the wedge law at each atom and averaging closes the ladder at
`Gtz.volumeParseval`:

    sum over a, b, c of t_a t_b t_c [a_a, a_b, a_c]^2  =  6

which is weighted Cauchy-Binet at rank three, proved by three contractions of
Parseval with no determinant theory.  `Gtz.cauchyBinetLadder` states all three
layers together, with right sides `1`, `2` and `6`.  `Gtz.exists_tripleBracket_sq_ge_six`
reads off the VOLUME FLOOR: every rank-three weighted design, at every size, has
three labels whose bracket has square at least six.

## Why six differs from five

`Gtz.not_hingeHoldsAtSize_five_three` is a theorem: the `(5,3)` diamond is a
tie with no parallel pair.  This module gives the reason the same construction
cannot reach six.

* At five directions a common conic ALWAYS exists (`Gtz.exists_commonQuadric_five`):
  pad with the zero vector and count.  So the off-conic stratum is EMPTY at
  size five.
* At seven directions a nonzero stress ALWAYS exists
  (`Gtz.exists_stress_seven`): seven symmetric matrices in a six-dimensional
  space are dependent.  So the stress-free stratum is EMPTY at size seven.
* At six, and only at six, stress-free and off-conic are the SAME condition and
  the stratum is nonempty.

The open `(6,3)` cell is that single stratum, and it has no counterpart at five.

## The leverage arithmetic, and where it stops

`Gtz.sum_inv_leverage_lt_four_of_isTie_sixThree` is the sharp harmonic law
`sum over c of 1 / l_c < 4` at a `(6,3)` tie, from which the count "at least
three atoms are strictly heavy" follows in two lines.
`Gtz.shareArithmetic_is_consistent` says where the route stops: the whole
scalar system a tie imposes on weights and leverages — positivity, unit weight
total, the leverage floor, the strict share ceiling, the trace value, the
harmonic law and the second moment law — is satisfied by the uniform point.
No contradiction lives in the scalar data alone.
-/
import Gtz.Wave.OnPathRegistryCollapse
import Gtz.Design.LineFreeConicBridge
import Gtz.Quantitative.HingeStressNarrowing
import Gtz.Design.StratumTieFreeClasses
import Gtz.Design.DepthCapAxisParseval
import Gtz.Ties.RankTwoMassCircuit
import Gtz.Reduction.PolarPlaneTurn
import Gtz.Reduction.PolarCrossWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. The stressed arm of the `(6,3)` trichotomy is closed

`Gtz.sixThree_stress_trichotomy` splits every `(6,3)` design three ways.  Branch
(ii) is discharged by `Gtz.balancedStratumSelection_six_holds` and branch (iii)
by `Gtz.twoPoleStratumSelection_six_unconditional`, both unconditional.  So the
FIRST branch is the only survivor, and its complement is closed.  That
complement is the statement below. -/

/-- **EVERY `(6,3)` TIE THAT CARRIES A NONZERO STRESS HAS A PARALLEL PAIR.**
Unconditional.  A nonzero stress excludes branch (i) of the trichotomy, and the
two remaining branches are closed in the tree.

This is the positive form of the reduction the campaign only ever ran backwards:
`Gtz.hingeHoldsAtSize_sixThree_of_stressFreeHinge` consumes the same two
capstones but needs branch (i) as a hypothesis.  Here branch (i) is EXCLUDED by
the hypothesis instead of assumed, so nothing open is used. -/
theorem sixThree_hasParallelPair_of_isTie_of_stress (design : WeightedDesign 6 3)
    (htie : IsTie design) {stress : Fin 6 → ℝ} (hstressNe : stress ≠ 0)
    (hstress : (∑ c, stress c • atomMatrix (design.atom c)) = 0) :
    HasParallelPair design := by
  rcases sixThree_stress_trichotomy design with
    hindependent | ⟨balancedStress, hbalanced, hfull, _, _, _, _⟩
      | ⟨coplanarStress, probe, hcoplanarNe, hprobeNe, hcoplanar, hsupport⟩
  · exact absurd (hindependent stress hstress) hstressNe
  · exact sixThree_hasParallelPair_of_isTie_of_balancedStress balancedStratumSelection_six_holds
      design htie hbalanced hfull
  · exact sixThree_hasParallelPair_of_isTie_of_coplanarStress_unconditional design htie
      hcoplanarNe hprobeNe hcoplanar hsupport

/-- **A PRIMITIVE `(6,3)` TIE IS STRESS-FREE.**  The contrapositive of the
previous theorem, in the vocabulary of `Gtz.IsStressFreeDesign`.  Every
counterexample to the `(6,3)` hinge, if one exists, has six atom matrices that
are a BASIS of the symmetric three by three matrices. -/
theorem isStressFreeDesign_of_isPrimitiveDesign_of_isTie (design : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign design) (htie : IsTie design) :
    IsStressFreeDesign design := by
  intro stress hstress
  by_contra hstressNe
  exact (isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive
    (sixThree_hasParallelPair_of_isTie_of_stress design htie hstressNe hstress)

/-- **NO PRIMITIVE `(6,3)` DESIGN WITH A STRESS IS A TIE.**  The same fact stated
as a stratum emptiness. -/
theorem sixThree_not_isTie_of_isPrimitiveDesign_of_stress (design : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign design) {stress : Fin 6 → ℝ} (hstressNe : stress ≠ 0)
    (hstress : (∑ c, stress c • atomMatrix (design.atom c)) = 0) : ¬ IsTie design :=
  fun htie => hstressNe (isStressFreeDesign_of_isPrimitiveDesign_of_isTie design hprimitive
    htie stress hstress)

/-! ## 2. The conic stratum is closed

Six points of the projective plane lie on a conic exactly when the six Veronese
images are dependent, which is exactly a nonzero stress
(`Gtz.isStressFreeDesign_iff_hasNoCommonQuadric`).  So section 1 closes the
whole conic locus at once. -/

/-- **EVERY `(6,3)` TIE WHOSE SIX DIRECTIONS LIE ON A COMMON CONIC HAS A PARALLEL
PAIR.**  Unconditional.  The conic manufactures the stress and section 1 does the
rest. -/
theorem sixThree_hasParallelPair_of_isTie_of_commonQuadric (design : WeightedDesign 6 3)
    (htie : IsTie design) {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form)
    (hnonzero : form ≠ 0)
    (hquadric : ∀ label, design.atom label ⬝ᵥ (form *ᵥ design.atom label) = 0) :
    HasParallelPair design := by
  obtain ⟨stress, hstressNe, hstress⟩ :=
    exists_stress_of_commonQuadric design.atom hsymmetric hnonzero hquadric
  exact sixThree_hasParallelPair_of_isTie_of_stress design htie hstressNe hstress

/-- **THE SIX DIRECTIONS OF A PRIMITIVE `(6,3)` TIE LIE ON NO CONIC.**  The
off-conic condition, which the campaign carries as a HYPOTHESIS on the line-free
class (`Gtz.BaseTripleTightLineFreeOffConicHeavyNeedleResidual`), is a THEOREM at
every primitive tie.  So the off-conic hypothesis of that class costs nothing:
it is implied by the antecedents already present. -/
theorem hasNoCommonQuadric_of_isPrimitiveDesign_of_isTie (design : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign design) (htie : IsTie design) :
    HasNoCommonQuadric design.atom :=
  (isStressFreeDesign_iff_hasNoCommonQuadric design).mp
    (isStressFreeDesign_of_isPrimitiveDesign_of_isTie design hprimitive htie)

/-- **THE CONIC STRATUM CARRIES NO PRIMITIVE TIE.**  The stratum statement, in
the shape a stratum ledger reads. -/
theorem sixThree_not_isTie_of_isPrimitiveDesign_of_commonQuadric (design : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign design) {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymmetric : formᵀ = form) (hnonzero : form ≠ 0)
    (hquadric : ∀ label, design.atom label ⬝ᵥ (form *ᵥ design.atom label) = 0) :
    ¬ IsTie design :=
  fun htie => hnonzero (hasNoCommonQuadric_of_isPrimitiveDesign_of_isTie design hprimitive htie
    form hsymmetric hquadric)

/-! ## 3. Plane coverings and the coplanar quadruple

A pair of planes covering all six atoms is a degenerate conic, so the two-plane
stratum closes by section 2.  The coplanar QUADRUPLE closes too, because the two
atoms left over supply the second plane through their own cross axis. -/

/-- **TWO PLANES COVERING ALL SIX ATOMS CLOSE THE TIE.**  Unconditional. -/
theorem sixThree_hasParallelPair_of_isTie_of_twoPlaneCover (design : WeightedDesign 6 3)
    (htie : IsTie design) {firstNormal secondNormal : Fin 3 → ℝ}
    (hfirstNe : firstNormal ≠ 0) (hsecondNe : secondNormal ≠ 0)
    (hcover : ∀ label, firstNormal ⬝ᵥ design.atom label = 0
      ∨ secondNormal ⬝ᵥ design.atom label = 0) :
    HasParallelPair design := by
  obtain ⟨stress, hstressNe, hstress⟩ :=
    exists_stress_of_twoPlanes design hfirstNe hsecondNe hcover
  exact sixThree_hasParallelPair_of_isTie_of_stress design htie hstressNe hstress

/-- **A PLANE THAT MISSES AT MOST TWO ATOMS CLOSES THE TIE.**  Unconditional.
The two missed labels are not parallel at a primitive design, so their cross
axis is nonzero and is a second plane containing exactly them.  The two planes
then cover all six labels. -/
theorem sixThree_hasParallelPair_of_isTie_of_planeMissingPair (design : WeightedDesign 6 3)
    (htie : IsTie design) {normalVec : Fin 3 → ℝ} (hnormalNe : normalVec ≠ 0)
    (firstOff secondOff : Fin 6) (hdistinct : firstOff ≠ secondOff)
    (hplane : ∀ label, label ≠ firstOff → label ≠ secondOff →
      normalVec ⬝ᵥ design.atom label = 0) :
    HasParallelPair design := by
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  have haxisNe : bracketNormal (design.atom firstOff) (design.atom secondOff) ≠ 0 :=
    bracketNormal_atom_ne_zero_of_isPrimitiveDesign (by norm_num) design hprimitive
      firstOff secondOff hdistinct
  refine hnoPair (sixThree_hasParallelPair_of_isTie_of_twoPlaneCover design htie hnormalNe
    haxisNe fun label => ?_)
  by_cases hfirst : label = firstOff
  · subst hfirst
    exact Or.inr (bracketNormal_dotProduct_left _ _)
  · by_cases hsecond : label = secondOff
    · subst hsecond
      exact Or.inr (bracketNormal_dotProduct_right _ _)
    · exact Or.inl (hplane label hfirst hsecond)

/-- A set of at most two labels of `Fin 6` sits inside a pair of distinct
labels. -/
private theorem exists_pair_superset_of_card_lt_three (offSet : Finset (Fin 6))
    (hsmall : offSet.card < 3) :
    ∃ firstOff secondOff : Fin 6, firstOff ≠ secondOff ∧ offSet ⊆ {firstOff, secondOff} := by
  classical
  have hsucc : ∀ label : Fin 6, label ≠ label + 1 := by decide
  have hcases : offSet.card = 0 ∨ offSet.card = 1 ∨ offSet.card = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · refine ⟨0, 1, by decide, ?_⟩
    rw [Finset.card_eq_zero.mp hzero]
    exact Finset.empty_subset _
  · obtain ⟨onlyLabel, hsingleton⟩ := Finset.card_eq_one.mp hone
    refine ⟨onlyLabel, onlyLabel + 1, hsucc onlyLabel, ?_⟩
    rw [hsingleton]
    exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
  · obtain ⟨firstLabel, secondLabel, hdistinct, hpair⟩ := Finset.card_eq_two.mp htwo
    exact ⟨firstLabel, secondLabel, hdistinct, by rw [hpair]⟩

/-- **AT LEAST THREE ATOMS OF A PRIMITIVE `(6,3)` TIE SIT OFF EVERY PLANE.**
Unconditional, and one better than the landed `Gtz.two_le_card_offPlane_of_isTie`.
The two theorems are independent: that one prices the off-plane leverage share,
this one manufactures a line-pair conic. -/
theorem three_le_card_offPlane_of_isPrimitiveDesign_of_isTie (design : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign design) (htie : IsTie design)
    (coplanarSet : Finset (Fin 6)) {normalVec : Fin 3 → ℝ} (hnormalNe : normalVec ≠ 0)
    (hcoplanar : ∀ label ∈ coplanarSet, design.atom label ⬝ᵥ normalVec = 0) :
    3 ≤ coplanarSetᶜ.card := by
  classical
  by_contra hsmall
  push_neg at hsmall
  obtain ⟨firstOff, secondOff, hdistinct, hsubset⟩ :=
    exists_pair_superset_of_card_lt_three coplanarSetᶜ hsmall
  refine (isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive ?_
  refine sixThree_hasParallelPair_of_isTie_of_planeMissingPair design htie hnormalNe
    firstOff secondOff hdistinct fun label hfirst hsecond => ?_
  have hmember : label ∈ coplanarSet := by
    by_contra hout
    have hmemCompl : label ∈ coplanarSetᶜ := Finset.mem_compl.mpr hout
    rcases Finset.mem_insert.mp (hsubset hmemCompl) with heq | heq
    · exact hfirst heq
    · exact hsecond (Finset.mem_singleton.mp heq)
  rw [dotProduct_comm]
  exact hcoplanar label hmember

/-- **NO PLANE HOLDS FOUR ATOMS OF A PRIMITIVE `(6,3)` TIE.**  The complementary
reading: every four atoms of such a design SPAN the whole of three-space. -/
theorem card_coplanar_le_three_of_isPrimitiveDesign_of_isTie (design : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign design) (htie : IsTie design)
    (coplanarSet : Finset (Fin 6)) {normalVec : Fin 3 → ℝ} (hnormalNe : normalVec ≠ 0)
    (hcoplanar : ∀ label ∈ coplanarSet, design.atom label ⬝ᵥ normalVec = 0) :
    coplanarSet.card ≤ 3 := by
  classical
  have hfloor := three_le_card_offPlane_of_isPrimitiveDesign_of_isTie design hprimitive htie
    coplanarSet hnormalNe hcoplanar
  have htotal : coplanarSet.card + coplanarSetᶜ.card = 6 := by
    have := Finset.card_add_card_compl coplanarSet
    simpa using this
  omega

/-! ## 4. The direction count

A LINE assignment is a map to a set of representative vectors together with a
per-label scale.  Fewer lines than labels forces two labels onto one line, and
two labels on one line are a parallel pair.  No tie hypothesis and no rank
hypothesis are used, and the scales make the statement strictly more general
than the tree's `Gtz.hasParallelPair_of_atomFactorsThroughSmallerIndex`, which
is the case where every scale is one. -/

/-- **FEWER LINES THAN LABELS FORCES A PARALLEL PAIR.**  Unconditional, at every
size and rank. -/
theorem hasParallelPair_of_atomLineFactorization {size rank lineCount : ℕ}
    (design : WeightedDesign size rank) (lineOf : Fin size → Fin lineCount)
    (lineVector : Fin lineCount → (Fin rank → ℝ)) (lineScale : Fin size → ℝ)
    (hfactor : ∀ label, design.atom label = lineScale label • lineVector (lineOf label))
    (hfewer : lineCount < size) : HasParallelPair design := by
  have hnotInjective : ¬ Function.Injective lineOf := by
    intro hinjective
    have hcard := Fintype.card_le_of_injective _ hinjective
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨leftLabel, rightLabel, hsameLine, hdistinct⟩ :=
    Function.not_injective_iff.mp hnotInjective
  by_cases hscale : lineScale leftLabel = 0
  · refine ⟨rightLabel, leftLabel, 0, Ne.symm hdistinct, ?_⟩
    rw [zero_smul, hfactor leftLabel, hscale, zero_smul]
  · refine ⟨leftLabel, rightLabel, lineScale rightLabel / lineScale leftLabel, hdistinct, ?_⟩
    rw [hfactor rightLabel, hfactor leftLabel, ← hsameLine, smul_smul]
    congr 1
    field_simp

/-- **AT MOST FIVE LINES AT SIX LABELS FORCES A PARALLEL PAIR.**  The `(6,3)`
instance.  Combined with section 1 this says: the six directions of a primitive
`(6,3)` tie occupy six distinct lines, and by section 3 no four of them are
coplanar. -/
theorem sixThree_hasParallelPair_of_fiveLines (design : WeightedDesign 6 3)
    (lineOf : Fin 6 → Fin 5) (lineVector : Fin 5 → (Fin 3 → ℝ)) (lineScale : Fin 6 → ℝ)
    (hfactor : ∀ label, design.atom label = lineScale label • lineVector (lineOf label)) :
    HasParallelPair design :=
  hasParallelPair_of_atomLineFactorization design lineOf lineVector lineScale hfactor
    (by norm_num)

/-! ## 5. The wedge Parseval law

The identity below is the level-two reading of Parseval.  The tree carries the
level-one reading `Gtz.sum_weight_mul_atomBracket_sq`, which fixes the pair and
sums over the third label.  This one fixes the PROBE and sums over the pair.

The proof is four contractions of Parseval against the Gram expansion of a
squared bracket.  No determinant theory, no Cauchy-Binet and no exterior
algebra. -/

/-- **THE GRAM EXPANSION OF A SQUARED BRACKET.**  The square of a three by three
determinant is the determinant of the Gram matrix of its rows. -/
theorem tripleBracket_sq_eq_gram (leftVec midVec probe : Fin 3 → ℝ) :
    tripleBracket leftVec midVec probe ^ 2
      = (leftVec ⬝ᵥ leftVec) * (midVec ⬝ᵥ midVec) * (probe ⬝ᵥ probe)
        + 2 * ((leftVec ⬝ᵥ midVec) * (leftVec ⬝ᵥ probe) * (midVec ⬝ᵥ probe))
        - (leftVec ⬝ᵥ leftVec) * (midVec ⬝ᵥ probe) ^ 2
        - (midVec ⬝ᵥ midVec) * (leftVec ⬝ᵥ probe) ^ 2
        - (leftVec ⬝ᵥ midVec) ^ 2 * (probe ⬝ᵥ probe) := by
  simp only [tripleBracket_eq, dotProduct, Fin.sum_univ_three]
  ring

/-- Parseval, in the dot-product spelling this section uses. -/
theorem sum_weight_mul_dotProduct_sq (D : WeightedDesign m k) (probe : Fin k → ℝ) :
    (∑ label, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2) = probe ⬝ᵥ probe :=
  (dotProduct_self_eq_sum_weight_mul_sq D probe).symm

/-- Parseval polarised, in the same spelling. -/
theorem sum_weight_mul_dotProduct_pair (D : WeightedDesign m k) (probeLeft probeRight : Fin k → ℝ) :
    (∑ label, D.weight label * ((D.atom label ⬝ᵥ probeLeft) * (D.atom label ⬝ᵥ probeRight)))
      = probeLeft ⬝ᵥ probeRight :=
  (dotProduct_eq_sum_weight_mul_atomPair D probeLeft probeRight).symm

/-- The trace of Parseval, in the same spelling. -/
theorem sum_weight_mul_dotProduct_self (D : WeightedDesign m k) :
    (∑ label, D.weight label * (D.atom label ⬝ᵥ D.atom label)) = (k : ℝ) := by
  have htrace := sum_weighted_leverage D
  simpa only [leverageOf_eq_dotProduct] using htrace

/-- **THE WEDGE PARSEVAL LAW.**  The fifteen cross products of a rank-three
design, weighted by the products of the two labels' weights, resolve twice the
identity.  In other words the SECOND EXTERIOR POWER of a weighted design is
again a weighted design.

Hypothesis-free: no heaviness, no primitivity, no distinctness, no tie.  The
diagonal terms vanish on their own, so the content is the fifteen unordered
pairs. -/
theorem wedgeParseval (D : WeightedDesign m 3) (probe : Fin 3 → ℝ) :
    (∑ leftLabel, ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
        * tripleBracket (D.atom leftLabel) (D.atom rightLabel) probe ^ 2)
      = 2 * (probe ⬝ᵥ probe) := by
  have hinner : ∀ leftLabel : Fin m,
      (∑ rightLabel, D.weight leftLabel * D.weight rightLabel
          * tripleBracket (D.atom leftLabel) (D.atom rightLabel) probe ^ 2)
        = D.weight leftLabel * ((D.atom leftLabel ⬝ᵥ D.atom leftLabel) * (probe ⬝ᵥ probe)
            - (D.atom leftLabel ⬝ᵥ probe) ^ 2) := by
    intro leftLabel
    have hexpand : ∀ rightLabel : Fin m,
        D.weight leftLabel * D.weight rightLabel
            * tripleBracket (D.atom leftLabel) (D.atom rightLabel) probe ^ 2
          = ((D.atom leftLabel ⬝ᵥ D.atom leftLabel) * (probe ⬝ᵥ probe) * D.weight leftLabel)
                * (D.weight rightLabel * (D.atom rightLabel ⬝ᵥ D.atom rightLabel))
            + (2 * (D.atom leftLabel ⬝ᵥ probe) * D.weight leftLabel)
                * (D.weight rightLabel * ((D.atom rightLabel ⬝ᵥ D.atom leftLabel)
                    * (D.atom rightLabel ⬝ᵥ probe)))
            - ((D.atom leftLabel ⬝ᵥ D.atom leftLabel) * D.weight leftLabel)
                * (D.weight rightLabel * (D.atom rightLabel ⬝ᵥ probe) ^ 2)
            - ((D.atom leftLabel ⬝ᵥ probe) ^ 2 * D.weight leftLabel)
                * (D.weight rightLabel * (D.atom rightLabel ⬝ᵥ D.atom rightLabel))
            - ((probe ⬝ᵥ probe) * D.weight leftLabel)
                * (D.weight rightLabel * (D.atom rightLabel ⬝ᵥ D.atom leftLabel) ^ 2) := by
      intro rightLabel
      rw [tripleBracket_sq_eq_gram, dotProduct_comm (D.atom leftLabel) (D.atom rightLabel)]
      ring
    rw [Finset.sum_congr rfl fun rightLabel _ => hexpand rightLabel]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_weight_mul_dotProduct_self D, sum_weight_mul_dotProduct_pair D (D.atom leftLabel) probe,
      sum_weight_mul_dotProduct_sq D probe, sum_weight_mul_dotProduct_sq D (D.atom leftLabel)]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun leftLabel _ => hinner leftLabel]
  have hsplit : (∑ label, D.weight label
      * ((D.atom label ⬝ᵥ D.atom label) * (probe ⬝ᵥ probe) - (D.atom label ⬝ᵥ probe) ^ 2))
      = (∑ label, D.weight label * (D.atom label ⬝ᵥ D.atom label)) * (probe ⬝ᵥ probe)
        - ∑ label, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2 := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by ring
  rw [hsplit, sum_weight_mul_dotProduct_self D, sum_weight_mul_dotProduct_sq D probe]
  push_cast
  ring

/-! ### The pair share ceiling

`Gtz.weighted_leverage_le_one` says a single weighted atom cannot exceed the
identity.  The wedge law gives the same statement one level up, at a PAIR. -/

/-- Swapping the two pair slots leaves the squared bracket alone. -/
theorem tripleBracket_sq_swap (leftVec midVec probe : Fin 3 → ℝ) :
    tripleBracket leftVec midVec probe ^ 2 = tripleBracket midVec leftVec probe ^ 2 := by
  simp only [tripleBracket_eq]
  ring

/-- The bracket read at the pair's own cross axis is the axis budget. -/
theorem tripleBracket_crossAxis_eq_budget (D : WeightedDesign m 3)
    (firstLabel secondLabel : Fin m) :
    tripleBracket (D.atom firstLabel) (D.atom secondLabel) (crossAxis D firstLabel secondLabel)
      = crossAxisBudget D firstLabel secondLabel := by
  rw [tripleBracket_eq_bracketNormal_dotProduct, ← crossAxis, crossAxis_dotProduct_self]

/-- **THE PAIR SHARE CEILING.**  For every pair of labels of every rank-three
design,

    t_c * t_d * (l_c * l_d - <a_c, a_d>^2)  <=  1.

The exact analogue one level up of `Gtz.weighted_leverage_le_one`, and sharp:
the orthonormal three-atom design attains it.  Hypothesis-free. -/
theorem weight_mul_crossAxisBudget_le_one (D : WeightedDesign m 3)
    (firstLabel secondLabel : Fin m) :
    D.weight firstLabel * D.weight secondLabel * crossAxisBudget D firstLabel secondLabel ≤ 1 := by
  classical
  rcases eq_or_ne firstLabel secondLabel with hsame | hdistinct
  · have hzero : crossAxisBudget D firstLabel secondLabel = 0 := by
      rw [← crossAxis_dotProduct_self, crossAxis, hsame, bracketNormal_self]
      simp
    rw [hzero, mul_zero]
    norm_num
  · set axis := crossAxis D firstLabel secondLabel with haxis
    set budget := crossAxisBudget D firstLabel secondLabel with hbudget
    have hbudgetNonneg : 0 ≤ budget := crossAxisBudget_nonneg D firstLabel secondLabel
    set rowSum : Fin m → ℝ := fun leftLabel =>
      ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
        * tripleBracket (D.atom leftLabel) (D.atom rightLabel) axis ^ 2 with hrowSum
    have hrowNonneg : ∀ leftLabel, 0 ≤ rowSum leftLabel := by
      intro leftLabel
      refine Finset.sum_nonneg fun rightLabel _ => ?_
      exact mul_nonneg (mul_nonneg (D.weight_pos leftLabel).le (D.weight_pos rightLabel).le)
        (sq_nonneg _)
    have hpairLe : rowSum firstLabel + rowSum secondLabel ≤ ∑ leftLabel, rowSum leftLabel := by
      have hsubset : ({firstLabel, secondLabel} : Finset (Fin m)) ⊆ Finset.univ :=
        Finset.subset_univ _
      have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun leftLabel _ _ => hrowNonneg leftLabel)
      rwa [Finset.sum_pair hdistinct] at hsum
    have hfirstTerm : D.weight firstLabel * D.weight secondLabel * budget ^ 2 ≤ rowSum firstLabel := by
      have hmem : secondLabel ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
      have hle := Finset.single_le_sum
        (f := fun rightLabel => D.weight firstLabel * D.weight rightLabel
          * tripleBracket (D.atom firstLabel) (D.atom rightLabel) axis ^ 2)
        (fun rightLabel _ => mul_nonneg (mul_nonneg (D.weight_pos firstLabel).le
          (D.weight_pos rightLabel).le) (sq_nonneg _)) hmem
      rwa [tripleBracket_crossAxis_eq_budget D firstLabel secondLabel, ← hbudget] at hle
    have hsecondTerm :
        D.weight firstLabel * D.weight secondLabel * budget ^ 2 ≤ rowSum secondLabel := by
      have hmem : firstLabel ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
      have hle := Finset.single_le_sum
        (f := fun rightLabel => D.weight secondLabel * D.weight rightLabel
          * tripleBracket (D.atom secondLabel) (D.atom rightLabel) axis ^ 2)
        (fun rightLabel _ => mul_nonneg (mul_nonneg (D.weight_pos secondLabel).le
          (D.weight_pos rightLabel).le) (sq_nonneg _)) hmem
      rw [← tripleBracket_sq_swap (D.atom firstLabel) (D.atom secondLabel) axis,
        tripleBracket_crossAxis_eq_budget D firstLabel secondLabel, ← hbudget] at hle
      calc D.weight firstLabel * D.weight secondLabel * budget ^ 2
          = D.weight secondLabel * D.weight firstLabel * budget ^ 2 := by ring
        _ ≤ rowSum secondLabel := hle
    have htotal : (∑ leftLabel, rowSum leftLabel) = 2 * (axis ⬝ᵥ axis) := wedgeParseval D axis
    have haxisSq : axis ⬝ᵥ axis = budget := by
      rw [haxis, hbudget, crossAxis_dotProduct_self]
    rw [htotal, haxisSq] at hpairLe
    have hbound : D.weight firstLabel * D.weight secondLabel * budget ^ 2 ≤ budget := by
      linarith [hfirstTerm, hsecondTerm, hpairLe]
    rcases eq_or_lt_of_le hbudgetNonneg with hzero | hpos
    · rw [← hzero, mul_zero]
      norm_num
    · nlinarith [hbound, hpos]

/-! ### The pair total and the share second moment -/

/-- **THE SQUARED PAIRING TOTAL.**  At every rank and every size,

    sum over c, sum over d of t_c t_d <a_c, a_d>^2  =  rank.

This is Parseval read against each atom in turn.  It is the squared Frobenius
norm of the identity, spelled in the design's own data. -/
theorem sum_weight_mul_pairing_sq (D : WeightedDesign m k) :
    (∑ leftLabel, ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
        * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2) = (k : ℝ) := by
  have hinner : ∀ leftLabel : Fin m,
      (∑ rightLabel, D.weight leftLabel * D.weight rightLabel
          * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2)
        = D.weight leftLabel * (D.atom leftLabel ⬝ᵥ D.atom leftLabel) := by
    intro leftLabel
    have hstep : ∀ rightLabel : Fin m,
        D.weight leftLabel * D.weight rightLabel
            * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2
          = D.weight leftLabel
            * (D.weight rightLabel * (D.atom rightLabel ⬝ᵥ D.atom leftLabel) ^ 2) := by
      intro rightLabel
      rw [dotProduct_comm (D.atom leftLabel) (D.atom rightLabel)]
      ring
    rw [Finset.sum_congr rfl fun rightLabel _ => hstep rightLabel, ← Finset.mul_sum,
      sum_weight_mul_dotProduct_sq D (D.atom leftLabel)]
  rw [Finset.sum_congr rfl fun leftLabel _ => hinner leftLabel,
    sum_weight_mul_dotProduct_self D]

/-- **THE SHARE SECOND MOMENT LAW.**  At every rank and every size,

    sum over c of (t_c * l_c)^2  <=  rank.

The shares of `Gtz.share_bracket_strict_of_isTie_sixThree` are individually
below one; this bounds their squares in TOTAL, and the bound is sharp: the
orthonormal design of `rank` atoms has every share equal to one.  The defect is
exactly twice the off-diagonal squared pairing total. -/
theorem sum_share_sq_le_rank (D : WeightedDesign m k) :
    (∑ label, (D.weight label * leverageOf (D.atom label)) ^ 2) ≤ (k : ℝ) := by
  classical
  have hdiagonal : ∀ leftLabel : Fin m,
      (D.weight leftLabel * leverageOf (D.atom leftLabel)) ^ 2
        ≤ ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
            * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2 := by
    intro leftLabel
    have hnonneg : ∀ rightLabel ∈ (Finset.univ : Finset (Fin m)),
        0 ≤ D.weight leftLabel * D.weight rightLabel
          * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2 :=
      fun rightLabel _ => mul_nonneg (mul_nonneg (D.weight_pos leftLabel).le
        (D.weight_pos rightLabel).le) (sq_nonneg _)
    have hle := Finset.single_le_sum hnonneg (Finset.mem_univ leftLabel)
    calc (D.weight leftLabel * leverageOf (D.atom leftLabel)) ^ 2
        = D.weight leftLabel * D.weight leftLabel
            * (D.atom leftLabel ⬝ᵥ D.atom leftLabel) ^ 2 := by
          rw [leverageOf_eq_dotProduct]; ring
      _ ≤ _ := hle
  calc (∑ label, (D.weight label * leverageOf (D.atom label)) ^ 2)
      ≤ ∑ leftLabel, ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
          * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2 :=
        Finset.sum_le_sum fun leftLabel _ => hdiagonal leftLabel
    _ = (k : ℝ) := sum_weight_mul_pairing_sq D

/-- **THE PAIR TOTAL.**  At every rank and every size,

    sum over c, sum over d of t_c t_d (l_c l_d - <a_c, a_d>^2)  =  rank^2 - rank.

At rank three this is the trace of the wedge Parseval law: the fifteen unordered
pairs carry total wedge leverage three. -/
theorem sum_pair_crossAxisBudget_eq (D : WeightedDesign m k) :
    (∑ leftLabel, ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
        * ((D.atom leftLabel ⬝ᵥ D.atom leftLabel) * (D.atom rightLabel ⬝ᵥ D.atom rightLabel)
          - (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2)) = (k : ℝ) ^ 2 - (k : ℝ) := by
  have hsplit : ∀ leftLabel : Fin m,
      (∑ rightLabel, D.weight leftLabel * D.weight rightLabel
          * ((D.atom leftLabel ⬝ᵥ D.atom leftLabel) * (D.atom rightLabel ⬝ᵥ D.atom rightLabel)
            - (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2))
        = (∑ rightLabel, D.weight leftLabel * D.weight rightLabel
              * ((D.atom leftLabel ⬝ᵥ D.atom leftLabel)
                * (D.atom rightLabel ⬝ᵥ D.atom rightLabel)))
          - ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
              * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2 := by
    intro leftLabel
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun rightLabel _ => by ring
  rw [Finset.sum_congr rfl fun leftLabel _ => hsplit leftLabel, Finset.sum_sub_distrib,
    sum_weight_mul_pairing_sq D]
  have hfirst : (∑ leftLabel, ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
      * ((D.atom leftLabel ⬝ᵥ D.atom leftLabel) * (D.atom rightLabel ⬝ᵥ D.atom rightLabel)))
      = (k : ℝ) ^ 2 := by
    have hinner : ∀ leftLabel : Fin m,
        (∑ rightLabel, D.weight leftLabel * D.weight rightLabel
            * ((D.atom leftLabel ⬝ᵥ D.atom leftLabel) * (D.atom rightLabel ⬝ᵥ D.atom rightLabel)))
          = (D.weight leftLabel * (D.atom leftLabel ⬝ᵥ D.atom leftLabel)) * (k : ℝ) := by
      intro leftLabel
      have hstep : ∀ rightLabel : Fin m,
          D.weight leftLabel * D.weight rightLabel
              * ((D.atom leftLabel ⬝ᵥ D.atom leftLabel)
                * (D.atom rightLabel ⬝ᵥ D.atom rightLabel))
            = (D.weight leftLabel * (D.atom leftLabel ⬝ᵥ D.atom leftLabel))
              * (D.weight rightLabel * (D.atom rightLabel ⬝ᵥ D.atom rightLabel)) := by
        intro rightLabel; ring
      rw [Finset.sum_congr rfl fun rightLabel _ => hstep rightLabel, ← Finset.mul_sum,
        sum_weight_mul_dotProduct_self D]
    rw [Finset.sum_congr rfl fun leftLabel _ => hinner leftLabel, ← Finset.sum_mul,
      sum_weight_mul_dotProduct_self D]
    ring
  rw [hfirst]

/-! ### The third layer, and the volume floor

Reading the wedge law at each atom in turn and averaging closes the ladder.  The
result is weighted Cauchy-Binet at rank three, proved with no determinant theory
and no exterior algebra: three contractions of Parseval. -/

/-- **THE VOLUME PARSEVAL LAW.**  The third and last layer of the ladder:

    sum over a, b, c of t_a t_b t_c [a_a, a_b, a_c]^2  =  6.

Six is `3!`, the volume of the identity counted with orientations.  One line
from `Gtz.wedgeParseval`, read at each atom and averaged.  Hypothesis-free.

This is weighted Cauchy-Binet at rank three: the twenty unordered triples of a
`(6,3)` design carry total weighted squared volume one. -/
theorem volumeParseval (D : WeightedDesign m 3) :
    (∑ probeLabel, D.weight probeLabel
        * ∑ leftLabel, ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
            * tripleBracket (D.atom leftLabel) (D.atom rightLabel) (D.atom probeLabel) ^ 2)
      = 6 := by
  have hstep : ∀ probeLabel : Fin m,
      D.weight probeLabel
          * (∑ leftLabel, ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
              * tripleBracket (D.atom leftLabel) (D.atom rightLabel) (D.atom probeLabel) ^ 2)
        = 2 * (D.weight probeLabel * (D.atom probeLabel ⬝ᵥ D.atom probeLabel)) := by
    intro probeLabel
    rw [wedgeParseval D (D.atom probeLabel)]
    ring
  rw [Finset.sum_congr rfl fun probeLabel _ => hstep probeLabel, ← Finset.mul_sum,
    sum_weight_mul_dotProduct_self D]
  norm_num

/-- **THE VOLUME FLOOR.**  Every weighted rank-three design has three labels
whose bracket has square at least six.  Hypothesis-free, at every size.

The average of the squared bracket against the product weight is exactly six by
`Gtz.volumeParseval`, and the product weight is a probability distribution on
ordered triples, so some triple is at least the average.  Six is positive, so the
three labels are automatically distinct and the triple is a basis. -/
theorem exists_tripleBracket_sq_ge_six (D : WeightedDesign m 3) :
    ∃ leftLabel rightLabel probeLabel : Fin m,
      6 ≤ tripleBracket (D.atom leftLabel) (D.atom rightLabel) (D.atom probeLabel) ^ 2 := by
  classical
  by_contra hall
  push_neg at hall
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset (Fin m)) with hempty | hne
    · exfalso
      have hsum := D.weight_sum_one
      rw [hempty, Finset.sum_empty] at hsum
      exact zero_ne_one hsum
    · exact hne
  have hinner : ∀ leftLabel : Fin m,
      (∑ rightLabel : Fin m, D.weight leftLabel * D.weight rightLabel * (6 : ℝ))
        = D.weight leftLabel * 6 := by
    intro leftLabel
    have hrewrite : ∀ rightLabel : Fin m,
        D.weight leftLabel * D.weight rightLabel * (6 : ℝ)
          = (D.weight leftLabel * 6) * D.weight rightLabel := fun _ => by ring
    rw [Finset.sum_congr rfl fun rightLabel _ => hrewrite rightLabel, ← Finset.mul_sum,
      D.weight_sum_one, mul_one]
  have hmid : (∑ leftLabel : Fin m, ∑ rightLabel : Fin m,
      D.weight leftLabel * D.weight rightLabel * (6 : ℝ)) = 6 := by
    rw [Finset.sum_congr rfl fun leftLabel _ => hinner leftLabel, ← Finset.sum_mul,
      D.weight_sum_one, one_mul]
  have hlevelOne : ∀ leftLabel probeLabel : Fin m,
      (∑ rightLabel, D.weight leftLabel * D.weight rightLabel
          * tripleBracket (D.atom leftLabel) (D.atom rightLabel) (D.atom probeLabel) ^ 2)
        < ∑ rightLabel : Fin m, D.weight leftLabel * D.weight rightLabel * (6 : ℝ) := by
    intro leftLabel probeLabel
    refine Finset.sum_lt_sum_of_nonempty hnonempty fun rightLabel _ => ?_
    exact mul_lt_mul_of_pos_left (hall leftLabel rightLabel probeLabel)
      (mul_pos (D.weight_pos leftLabel) (D.weight_pos rightLabel))
  have hlevelTwo : ∀ probeLabel : Fin m,
      (∑ leftLabel, ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
          * tripleBracket (D.atom leftLabel) (D.atom rightLabel) (D.atom probeLabel) ^ 2)
        < ∑ leftLabel : Fin m, ∑ rightLabel : Fin m,
            D.weight leftLabel * D.weight rightLabel * (6 : ℝ) :=
    fun probeLabel => Finset.sum_lt_sum_of_nonempty hnonempty
      fun leftLabel _ => hlevelOne leftLabel probeLabel
  have hlevelThree : (∑ probeLabel, D.weight probeLabel
        * ∑ leftLabel, ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
            * tripleBracket (D.atom leftLabel) (D.atom rightLabel) (D.atom probeLabel) ^ 2)
      < ∑ probeLabel : Fin m, D.weight probeLabel
        * ∑ leftLabel : Fin m, ∑ rightLabel : Fin m,
            D.weight leftLabel * D.weight rightLabel * (6 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hnonempty fun probeLabel _ =>
      mul_lt_mul_of_pos_left (hlevelTwo probeLabel) (D.weight_pos probeLabel)
  have hright : (∑ probeLabel : Fin m, D.weight probeLabel
      * ∑ leftLabel : Fin m, ∑ rightLabel : Fin m,
          D.weight leftLabel * D.weight rightLabel * (6 : ℝ)) = 6 := by
    have hstep : ∀ probeLabel : Fin m,
        D.weight probeLabel * (∑ leftLabel : Fin m, ∑ rightLabel : Fin m,
            D.weight leftLabel * D.weight rightLabel * (6 : ℝ))
          = D.weight probeLabel * 6 := fun probeLabel => by rw [hmid]
    rw [Finset.sum_congr rfl fun probeLabel _ => hstep probeLabel, ← Finset.sum_mul,
      D.weight_sum_one, one_mul]
  rw [volumeParseval D, hright] at hlevelThree
  exact lt_irrefl 6 hlevelThree

/-- **THE CAUCHY-BINET LADDER AT RANK THREE, AS ONE THEOREM.**  Three layers,
one proof technique, no determinant theory.  Layer one is Parseval, layer two is
the wedge law, layer three is the volume law.  The right sides are `1`, `2` and
`6`: the number of ordered selections of `0`, `1` and `2` further slots. -/
theorem cauchyBinetLadder (D : WeightedDesign m 3) (probe : Fin 3 → ℝ) :
    (∑ label, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2) = probe ⬝ᵥ probe
      ∧ (∑ leftLabel, ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
          * tripleBracket (D.atom leftLabel) (D.atom rightLabel) probe ^ 2)
        = 2 * (probe ⬝ᵥ probe)
      ∧ (∑ probeLabel, D.weight probeLabel
          * ∑ leftLabel, ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
              * tripleBracket (D.atom leftLabel) (D.atom rightLabel) (D.atom probeLabel) ^ 2)
        = 6 :=
  ⟨sum_weight_mul_dotProduct_sq D probe, wedgeParseval D probe, volumeParseval D⟩

/-! ## 6. Why six differs from five, and from seven

`Gtz.not_hingeHoldsAtSize_five_three` is a theorem, so the hinge is genuinely a
size-six statement.  The two theorems below say exactly which stratum appears at
six and at no other size. -/

/-- Five directions padded by the zero vector. -/
noncomputable def zeroPaddedDirections (atoms : Fin 5 → (Fin 3 → ℝ)) : Fin 6 → (Fin 3 → ℝ) :=
  fun label => if hlabel : (label : ℕ) < 5 then atoms ⟨(label : ℕ), hlabel⟩ else 0

/-- The padded family agrees with the original on the first five labels. -/
theorem zeroPaddedDirections_apply (atoms : Fin 5 → (Fin 3 → ℝ)) (index : Fin 5) :
    zeroPaddedDirections atoms ⟨(index : ℕ), by omega⟩ = atoms index := by
  rw [zeroPaddedDirections]
  simp only [index.isLt, dif_pos]

/-- The padded family reads zero at the last label. -/
theorem zeroPaddedDirections_last (atoms : Fin 5 → (Fin 3 → ℝ)) :
    zeroPaddedDirections atoms 5 = 0 := by
  rw [zeroPaddedDirections]
  norm_num

/-- **FIVE DIRECTIONS ALWAYS LIE ON A CONIC.**  Unconditional, with no design
structure at all.  Pad with the zero vector, which lies on every conic, and read
the six-point duality: the padded family carries a stress at its zero slot, so
it is not stress-free, so it has a common quadric.

This is the reason the `(5,3)` diamond cannot be repaired into a `(6,3)`
counterexample.  The off-conic stratum, which section 2 shows is the ONLY place
a primitive `(6,3)` tie can live, does not exist at size five. -/
theorem exists_commonQuadric_five (atoms : Fin 5 → (Fin 3 → ℝ)) :
    ∃ form : Matrix (Fin 3) (Fin 3) ℝ, formᵀ = form ∧ form ≠ 0
      ∧ ∀ index, atoms index ⬝ᵥ (form *ᵥ atoms index) = 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  set padded := zeroPaddedDirections atoms with hpadded
  have hnoConic : ∀ conic : Matrix (Fin 3) (Fin 3) ℝ, conicᵀ = conic →
      (∀ index, padded index ⬝ᵥ (conic *ᵥ padded index) = 0) → conic = 0 := by
    intro conic hsymmetric hvanish
    by_contra hnonzero
    obtain ⟨index, hindex⟩ := hnone conic hsymmetric hnonzero
    refine hindex ?_
    have hshift := hvanish ⟨(index : ℕ), by omega⟩
    rwa [hpadded, zeroPaddedDirections_apply atoms index] at hshift
  have hstressFree := (stressFree_iff_no_conic_sixThree padded).mpr hnoConic
  have hstress : (∑ label, (fun index : Fin 6 => if index = (5 : Fin 6) then (1 : ℝ) else 0) label
      • atomMatrix (padded label)) = 0 := by
    refine Finset.sum_eq_zero fun label _ => ?_
    by_cases hlabel : label = (5 : Fin 6)
    · subst hlabel
      rw [hpadded, zeroPaddedDirections_last atoms, atomMatrix_zero, smul_zero]
    · simp only [if_neg hlabel, zero_smul]
  have hzero := hstressFree _ hstress
  have hentry := congrFun hzero (5 : Fin 6)
  simp at hentry

/-- **SEVEN DIRECTIONS ALWAYS CARRY A STRESS.**  Seven symmetric three by three
matrices live in a six-dimensional space, so they are dependent.  The stress-free
stratum does not exist at size seven. -/
theorem exists_stress_seven (atoms : Fin 7 → (Fin 3 → ℝ)) :
    ∃ stress : Fin 7 → ℝ, stress ≠ 0 ∧ (∑ label, stress label • atomMatrix (atoms label)) = 0 :=
  exists_dependency_of_symmetric_family (fun label => atomMatrix (atoms label))
    (fun label => transpose_eq_of_isHermitian (posSemidef_atomMatrix (atoms label)).1)
    (by norm_num)

/-- **THE SIZE GAP, AS ONE STATEMENT.**  Read the three clauses together.

At five, a conic through the directions always exists, so the stratum section 2
closes is EVERYTHING and the stratum section 2 leaves open is EMPTY.  At seven a
stress always exists, so section 1 closes everything.  At six the two conditions
coincide and the stratum is the whole remaining `(6,3)` question.  Six is the
only size at rank three where a design's atom matrices can be a BASIS of the
symmetric three by three matrices. -/
theorem sizeGap_at_rank_three :
    (∀ atoms : Fin 5 → (Fin 3 → ℝ), ∃ form : Matrix (Fin 3) (Fin 3) ℝ,
        formᵀ = form ∧ form ≠ 0 ∧ ∀ index, atoms index ⬝ᵥ (form *ᵥ atoms index) = 0)
      ∧ (∀ atoms : Fin 7 → (Fin 3 → ℝ), ∃ stress : Fin 7 → ℝ,
          stress ≠ 0 ∧ (∑ label, stress label • atomMatrix (atoms label)) = 0)
      ∧ (∀ design : WeightedDesign 6 3, IsPrimitiveDesign design → IsTie design →
          IsStressFreeDesign design ∧ HasNoCommonQuadric design.atom) :=
  ⟨exists_commonQuadric_five, exists_stress_seven,
    fun design hprimitive htie =>
      ⟨isStressFreeDesign_of_isPrimitiveDesign_of_isTie design hprimitive htie,
        hasNoCommonQuadric_of_isPrimitiveDesign_of_isTie design hprimitive htie⟩⟩

/-! ## 7. The leverage arithmetic, sharp, and its stopping point

A tie supplies two scalar facts about every atom: the leverage floor
`1 <= l_c` (`Gtz.leverage_one_le_of_isTie_sixThree`) and the strict share
ceiling `t_c l_c < 1` (`Gtz.share_lt_one_of_isTie`).  Together with the two
Parseval scalars they force a HARMONIC bound on the leverages. -/

/-- **THE HARMONIC LEVERAGE LAW, design-free.**  Weights and leverages with a
unit weight total, trace value `rank` at least two, every leverage at least one
and every share strictly below one satisfy

    sum over c of 1 / l_c  <  size - rank + 1.

Nothing here is about geometry: it is the exact scalar content of the two tie
facts against the two Parseval scalars. -/
theorem sum_inv_lt_of_share_lt_one {size : ℕ} (weight leverage : Fin size → ℝ) (rank : ℝ)
    (hleverage : ∀ label, 1 ≤ leverage label)
    (hshare : ∀ label, weight label * leverage label < 1)
    (hweightSum : (∑ label, weight label) = 1)
    (hrankSum : (∑ label, weight label * leverage label) = rank)
    (hrank : 2 ≤ rank) :
    (∑ label, (leverage label)⁻¹) < (size : ℝ) - rank + 1 := by
  have hpos : ∀ label, (0 : ℝ) < leverage label :=
    fun label => lt_of_lt_of_le zero_lt_one (hleverage label)
  have hinvLe : ∀ label, (leverage label)⁻¹ ≤ 1 := by
    intro label
    rw [inv_le_one_iff₀]
    exact Or.inr (hleverage label)
  have hcancel : ∀ label, weight label * leverage label * (leverage label)⁻¹ = weight label := by
    intro label
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (hpos label)), mul_one]
  have hpointwise : ∀ label,
      weight label * leverage label - weight label ≤ 1 - (leverage label)⁻¹ := by
    intro label
    have hstep := mul_le_mul_of_nonneg_right (le_of_lt (hshare label))
      (sub_nonneg.mpr (hinvLe label))
    have hexpand : weight label * leverage label * (1 - (leverage label)⁻¹)
        = weight label * leverage label - weight label := by
      rw [mul_sub, mul_one, hcancel label]
    rw [hexpand, one_mul] at hstep
    exact hstep
  have hheavy : ∃ label, 1 < leverage label := by
    by_contra hall
    push_neg at hall
    have heq : ∀ label, leverage label = 1 :=
      fun label => le_antisymm (hall label) (hleverage label)
    have hcollapse : (∑ label, weight label * leverage label) = 1 := by
      rw [Finset.sum_congr rfl fun label _ => by rw [heq label, mul_one], hweightSum]
    rw [hrankSum] at hcollapse
    linarith
  obtain ⟨heavyLabel, hheavyLt⟩ := hheavy
  have hstrict : weight heavyLabel * leverage heavyLabel - weight heavyLabel
      < 1 - (leverage heavyLabel)⁻¹ := by
    have hinvLt : (leverage heavyLabel)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      exact Or.inr hheavyLt
    have hstep := mul_lt_mul_of_pos_right (hshare heavyLabel) (sub_pos.mpr hinvLt)
    have hexpand : weight heavyLabel * leverage heavyLabel * (1 - (leverage heavyLabel)⁻¹)
        = weight heavyLabel * leverage heavyLabel - weight heavyLabel := by
      rw [mul_sub, mul_one, hcancel heavyLabel]
    rw [hexpand, one_mul] at hstep
    exact hstep
  have hsumLt := Finset.sum_lt_sum
    (f := fun label => weight label * leverage label - weight label)
    (g := fun label => 1 - (leverage label)⁻¹)
    (fun label _ => hpointwise label)
    ⟨heavyLabel, Finset.mem_univ _, hstrict⟩
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hrankSum, hweightSum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsumLt
  linarith

/-- **THE HARMONIC LEVERAGE LAW AT A `(6,3)` TIE.**  The reciprocals of the six
leverages total strictly less than four.  Each reciprocal is at most one, so the
trivial bound is six; this is sharp enough to force the count below. -/
theorem sum_inv_leverage_lt_four_of_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D) :
    (∑ label, (leverageOf (D.atom label))⁻¹) < 4 := by
  have hbound := sum_inv_lt_of_share_lt_one (size := 6)
    (fun label => D.weight label) (fun label => leverageOf (D.atom label)) 3
    (fun label => leverage_one_le_of_isTie_sixThree D htie label)
    (fun label => share_lt_one_of_isTie (by norm_num) D htie label)
    D.weight_sum_one (sum_weighted_leverage D) (by norm_num)
  norm_num at hbound
  exact hbound

/-- **AT LEAST THREE ATOMS OF A `(6,3)` TIE ARE STRICTLY HEAVY.**  Two lines from
the harmonic law: the reciprocals of the light atoms are exactly one, so the
strictly heavy atoms alone must absorb a total excess above two, and each of them
absorbs less than one. -/
theorem three_le_card_strictlyHeavy_of_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D) :
    3 ≤ (Finset.univ.filter fun label => 1 < leverageOf (D.atom label)).card := by
  classical
  set heavySet := Finset.univ.filter fun label => 1 < leverageOf (D.atom label) with hheavySet
  have hharmonic := sum_inv_leverage_lt_four_of_isTie_sixThree D htie
  have hexcess : ∀ label, (0 : ℝ) ≤ 1 - (leverageOf (D.atom label))⁻¹ := by
    intro label
    have hfloor := leverage_one_le_of_isTie_sixThree D htie label
    have hpos : (0 : ℝ) < leverageOf (D.atom label) := lt_of_lt_of_le zero_lt_one hfloor
    have hinvLe : (leverageOf (D.atom label))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      exact Or.inr hfloor
    linarith
  have hlightZero : ∀ label ∈ heavySetᶜ, 1 - (leverageOf (D.atom label))⁻¹ = 0 := by
    intro label hlabel
    have hnotHeavy : ¬ (1 < leverageOf (D.atom label)) := by
      have := Finset.mem_compl.mp hlabel
      rw [hheavySet] at this
      simpa using this
    have heq : leverageOf (D.atom label) = 1 :=
      le_antisymm (not_lt.mp hnotHeavy) (leverage_one_le_of_isTie_sixThree D htie label)
    rw [heq, inv_one, sub_self]
  have htotal : (∑ label, (1 - (leverageOf (D.atom label))⁻¹))
      = 6 - ∑ label, (leverageOf (D.atom label))⁻¹ := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    norm_num
  have hsplit := Finset.sum_add_sum_compl heavySet
    (fun label => 1 - (leverageOf (D.atom label))⁻¹)
  have hcomplZero : (∑ label ∈ heavySetᶜ, (1 - (leverageOf (D.atom label))⁻¹)) = 0 :=
    Finset.sum_eq_zero hlightZero
  rw [hcomplZero, add_zero, htotal] at hsplit
  have hheavyTotal : (2 : ℝ) < ∑ label ∈ heavySet, (1 - (leverageOf (D.atom label))⁻¹) := by
    rw [hsplit]; linarith
  have hcap : (∑ label ∈ heavySet, (1 - (leverageOf (D.atom label))⁻¹))
      ≤ (heavySet.card : ℝ) := by
    have hbound : ∀ label ∈ heavySet, 1 - (leverageOf (D.atom label))⁻¹ ≤ 1 := by
      intro label _
      have hfloor := leverage_one_le_of_isTie_sixThree D htie label
      have hpos : (0 : ℝ) < leverageOf (D.atom label) := lt_of_lt_of_le zero_lt_one hfloor
      have : (0 : ℝ) < (leverageOf (D.atom label))⁻¹ := inv_pos.mpr hpos
      linarith
    calc (∑ label ∈ heavySet, (1 - (leverageOf (D.atom label))⁻¹))
        ≤ ∑ _label ∈ heavySet, (1 : ℝ) := Finset.sum_le_sum hbound
      _ = (heavySet.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcardReal : (2 : ℝ) < (heavySet.card : ℝ) := lt_of_lt_of_le hheavyTotal hcap
  have hcardNat : 2 < heavySet.card := by exact_mod_cast hcardReal
  omega

/-- **WHERE THE SCALAR ROUTE STOPS.**  Every scalar law a `(6,3)` tie imposes on
its weights and leverages — positivity, the unit weight total, the leverage
floor, the strict share ceiling, the trace value three, the harmonic law of this
section and the share second moment law of section 5 — is satisfied at the
uniform point `t_c = 1/6`, `l_c = 3`.

So the scalar data of a tie is CONSISTENT.  No contradiction lives in the
leverages and weights alone, and every further step has to read the geometry:
the pairings, the brackets, or the stress. -/
theorem shareArithmetic_is_consistent :
    ∃ weight leverage : Fin 6 → ℝ,
      (∀ label, 0 < weight label)
        ∧ (∑ label, weight label) = 1
        ∧ (∀ label, 1 ≤ leverage label)
        ∧ (∀ label, weight label * leverage label < 1)
        ∧ (∑ label, weight label * leverage label) = 3
        ∧ (∑ label, (leverage label)⁻¹) < 4
        ∧ (∑ label, (weight label * leverage label) ^ 2) ≤ 3 := by
  refine ⟨fun _ => 1 / 6, fun _ => 3, fun _ => by norm_num, ?_, fun _ => by norm_num,
    fun _ => by norm_num, ?_, ?_, ?_⟩
  · simp only [Fin.sum_univ_six]; norm_num
  · simp only [Fin.sum_univ_six]; norm_num
  · simp only [Fin.sum_univ_six]; norm_num
  · simp only [Fin.sum_univ_six]; norm_num

/-! ## 8. The invariant dichotomy: a finite label on the twenty triples

`Gtz.subsetSum_posDef_iff_tripleInvariants` decides strict domination by three
polynomial invariants of a triple: the gap trace, the gap second invariant and
the gap determinant.  A tie says NO triple dominates strictly, so at every one
of the twenty triples at least one invariant is nonpositive.

The leverage floor discharges the FIRST invariant for free.  Every leverage of a
`(6,3)` tie is at least one, so a triple carrying one strictly heavy atom has
gap trace strictly positive.  What is left is a TWO-valued label on the triples:
second invariant nonpositive, or determinant nonpositive.

`Gtz.three_le_card_strictlyHeavy_of_isTie_sixThree` says at least three atoms are
strictly heavy, so at most three are not, so at most ONE of the twenty triples
fails to carry the label.  That turns a continuum into a finite case split with
nineteen labelled positions, and the split is unconditional. -/

/-- **THE INVARIANT DICHOTOMY AT A `(6,3)` TIE.**  Unconditional.  At every
triple of distinct labels carrying at least one strictly heavy atom, the gap's
second invariant or the gap's determinant is nonpositive.

The first invariant never fires at such a triple, so the tie's refusal to
dominate strictly is carried entirely by the other two.  This is the finite cut
the moduli grading does not give: nineteen of the twenty triples take one of two
values, and the value is a polynomial sign in the leverages, the pair areas and
the bracket. -/
theorem invariantDichotomy_of_isTie_sixThree (design : WeightedDesign 6 3) (htie : IsTie design)
    (firstLabel secondLabel thirdLabel : Fin 6)
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel)
    (hstrictlyHeavy : 1 < leverageOf (design.atom firstLabel)
      ∨ 1 < leverageOf (design.atom secondLabel)
      ∨ 1 < leverageOf (design.atom thirdLabel)) :
    triplePairAreaSum (design.atom firstLabel) (design.atom secondLabel)
            (design.atom thirdLabel)
          - 2 * tripleLeverageSum (design.atom firstLabel) (design.atom secondLabel)
              (design.atom thirdLabel) + 3 ≤ 0
      ∨ atomBracket design firstLabel secondLabel thirdLabel ^ 2
            - triplePairAreaSum (design.atom firstLabel) (design.atom secondLabel)
                (design.atom thirdLabel)
            + tripleLeverageSum (design.atom firstLabel) (design.atom secondLabel)
                (design.atom thirdLabel) - 1 ≤ 0 := by
  classical
  by_contra hboth
  push_neg at hboth
  obtain ⟨harea, hdeterminant⟩ := hboth
  have hfirstFloor := leverage_one_le_of_isTie_sixThree design htie firstLabel
  have hsecondFloor := leverage_one_le_of_isTie_sixThree design htie secondLabel
  have hthirdFloor := leverage_one_le_of_isTie_sixThree design htie thirdLabel
  have htrace : 0 < tripleLeverageSum (design.atom firstLabel) (design.atom secondLabel)
      (design.atom thirdLabel) - 3 := by
    simp only [tripleLeverageSum]
    rcases hstrictlyHeavy with hstrict | hstrict | hstrict <;> linarith
  have hposDef := (subsetSum_posDef_iff_tripleInvariants design firstLabel secondLabel
    thirdLabel hfirstSecond hfirstThird hsecondThird).mpr ⟨htrace, harea, hdeterminant⟩
  have hcard : ({firstLabel, secondLabel, thirdLabel} : Finset (Fin 6)).card = 3 := by
    have hnotFirst : firstLabel ∉ ({secondLabel, thirdLabel} : Finset (Fin 6)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hfirstSecond, hfirstThird⟩
    have hnotSecond : secondLabel ∉ ({thirdLabel} : Finset (Fin 6)) := by
      simp only [Finset.mem_singleton]
      exact hsecondThird
    rw [Finset.card_insert_of_notMem hnotFirst, Finset.card_insert_of_notMem hnotSecond,
      Finset.card_singleton]
  exact htie.2 _ hcard hposDef

/-! ## 9. The ledger of this module -/

/-- **THE CLOSED STRATA, AS ONE THEOREM.**  Four geometric conditions on a
`(6,3)` design, each of which forces a tie to carry a parallel pair, all
unconditional.  A counterexample to `Gtz.HingeHoldsAtSize 6 3`, if one exists,
avoids every one of them. -/
theorem sixThree_closedStrata (design : WeightedDesign 6 3) (htie : IsTie design) :
    ((∃ stress : Fin 6 → ℝ, stress ≠ 0
        ∧ (∑ c, stress c • atomMatrix (design.atom c)) = 0) → HasParallelPair design)
      ∧ ((∃ form : Matrix (Fin 3) (Fin 3) ℝ, formᵀ = form ∧ form ≠ 0
          ∧ ∀ label, design.atom label ⬝ᵥ (form *ᵥ design.atom label) = 0) →
            HasParallelPair design)
      ∧ ((∃ firstNormal secondNormal : Fin 3 → ℝ, firstNormal ≠ 0 ∧ secondNormal ≠ 0
          ∧ ∀ label, firstNormal ⬝ᵥ design.atom label = 0
            ∨ secondNormal ⬝ᵥ design.atom label = 0) → HasParallelPair design)
      ∧ ((∃ (normalVec : Fin 3 → ℝ) (firstOff secondOff : Fin 6), normalVec ≠ 0
          ∧ firstOff ≠ secondOff
          ∧ ∀ label, label ≠ firstOff → label ≠ secondOff →
            normalVec ⬝ᵥ design.atom label = 0) → HasParallelPair design) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨stress, hstressNe, hstress⟩
    exact sixThree_hasParallelPair_of_isTie_of_stress design htie hstressNe hstress
  · rintro ⟨form, hsymmetric, hnonzero, hquadric⟩
    exact sixThree_hasParallelPair_of_isTie_of_commonQuadric design htie hsymmetric hnonzero
      hquadric
  · rintro ⟨firstNormal, secondNormal, hfirstNe, hsecondNe, hcover⟩
    exact sixThree_hasParallelPair_of_isTie_of_twoPlaneCover design htie hfirstNe hsecondNe hcover
  · rintro ⟨normalVec, firstOff, secondOff, hnormalNe, hdistinct, hplane⟩
    exact sixThree_hasParallelPair_of_isTie_of_planeMissingPair design htie hnormalNe firstOff
      secondOff hdistinct hplane

/-- **THE SHAPE OF A `(6,3)` COUNTEREXAMPLE.**  Every primitive `(6,3)` tie has
six atom matrices that are a basis of the symmetric three by three matrices, six
directions on no conic, no four of them coplanar, at least three strictly heavy
leverages, reciprocal leverage total below four and share second moment at most
three.  All six clauses are unconditional. -/
theorem sixThree_primitiveTie_normalForm (design : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign design) (htie : IsTie design) :
    IsStressFreeDesign design
      ∧ HasNoCommonQuadric design.atom
      ∧ (∀ (coplanarSet : Finset (Fin 6)) (normalVec : Fin 3 → ℝ), normalVec ≠ 0 →
          (∀ label ∈ coplanarSet, design.atom label ⬝ᵥ normalVec = 0) → coplanarSet.card ≤ 3)
      ∧ 3 ≤ (Finset.univ.filter fun label => 1 < leverageOf (design.atom label)).card
      ∧ (∑ label, (leverageOf (design.atom label))⁻¹) < 4
      ∧ (∑ label, (design.weight label * leverageOf (design.atom label)) ^ 2) ≤ 3 := by
  refine ⟨isStressFreeDesign_of_isPrimitiveDesign_of_isTie design hprimitive htie,
    hasNoCommonQuadric_of_isPrimitiveDesign_of_isTie design hprimitive htie,
    fun coplanarSet normalVec hnormalNe hcoplanar =>
      card_coplanar_le_three_of_isPrimitiveDesign_of_isTie design hprimitive htie coplanarSet
        hnormalNe hcoplanar,
    three_le_card_strictlyHeavy_of_isTie_sixThree design htie,
    sum_inv_leverage_lt_four_of_isTie_sixThree design htie, ?_⟩
  have hbound := sum_share_sq_le_rank design
  norm_num at hbound
  exact hbound

end Gtz

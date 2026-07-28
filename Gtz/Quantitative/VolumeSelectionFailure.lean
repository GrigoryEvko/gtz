/-
# The maximal-volume rule does not select a dominating subset

The selection principle asserts that a dominating `k`-subset exists; the classical
maximal-volume principle of Goreinov and Tyrtyshnikov names one, and the paper's open
problem `prob:effective` asks whether the one it names actually dominates **at uniform
weights** — the case its own `(7,3)` witness leaves standing, because what breaks
there is the weighting by `∏_{c ∈ C} t_c` and not the determinant.

**This file answers that question NO**, with an exactly rational witness at `(4,2)` and
all four weights equal to `1/4`.

## What is refuted, and what is not

The rule under attack is: *among the `k`-subsets take one of maximal volume
`det S_C` and use it*.  `volumeScore` is that score and `IsStrictVolumeMaximiser` is
"this subset is the unique argmax", strict so that no reading of the rule can escape by
choosing a different maximiser.

REFUTED: `volumeMaximiser_can_fail_to_dominate_atUniformWeights`; in the shape a rule has,
`not_forall_strictVolumeMaximiser_dominates_atSizeFour`; and in the paper's own score
`Gtz.shadowDeterminant`, `shadowDeterminantMaximiser_can_fail_to_dominate_atUniformWeights`.
The last is what makes the answer independent of which reading of "maximal volume" the
question intends.

NOT refuted, and nothing here says otherwise: `GtzWeighted`.  At BOTH witnesses a
dominating `2`-subset is exhibited, so each is a counterexample to the RULE and to
nothing else.  Rank two is in any case settled — `Gtz.gtz_rank_two` proves
`GtzWeightedAll 2` — which is exactly why these witnesses are safe: they live where the
existence of a dominating subset is a theorem, so they can carry no information about
`(6,3)` or `(7,3)` and cannot be misread as carrying any.

## The uniform witness — the one that answers the paper

`uniformVolumeRuleDesign` at `(4,2)`: atoms of denominator `25`, all weights `1/4`,
Parseval exact.  The six volume scores are

    {0,1} ↦ 56644/15625    {0,2} ↦ 64/25         {0,3} ↦ 54756/15625
    {1,2} ↦ 54756/15625    {1,3} ↦ 64/25         {2,3} ↦ 3844/15625

so `{0,1}` is the strict maximiser, beating the runner-up by `1888/15625`.  Its atom
sum is DIAGONAL, `S = diag(98/25, 578/625)`, so its least eigenvalue is the rational
`578/625` with no surd anywhere and the coordinate direction `(0,1)` alone refutes
domination, at `578/625 − 1 = −47/625`.  Both `{0,3}` and `{1,2}` dominate, each with
gap `[[1, ∓88/125], [∓88/125, 1]]` of determinant `7881/15625`.

The value `578/625 = 0.9248` sits ABOVE the maximal-volume principle's own uniform-weight
floor `m/(1 + k(m−k)) = 4/5` and below `1`, so the witness contradicts nothing the
principle proves; it lands in the gap the principle leaves, which the paper notes is
nonempty exactly when `k ≥ 2` and `m ≥ k+2`.

At uniform weights the two readings of "maximal volume" COINCIDE, and that is proved here
rather than left to the reader: `weightScaledVolumeScore_eq_shadowDeterminant` identifies
the weight-scaled determinant with the volume-sampling probability at `|C| = k`, and
`uniformVolumeRuleDesign_weightScaledVolumeScore_eq` computes the scale factor to be the
constant `1/16`, which cannot move an argmax.  So this single witness settles both
readings at once.

## The general-weight witness — complementary to the paper's, not a duplicate

`corankOneVolumeRuleDesign` at `(3,2)`: corank one, `m = k+1`, the region where
`GtzWeighted` is a theorem and `Gtz.Ties.CorankOneTieCriterion` classifies the ties
completely.  The three volume scores are `6561/1600`, `6561/1600`, `59049/10000`, so `{1,2}` is the
strict maximiser, beating the tie of the other two by `72171/40000`.  It fails on the
integer direction `(1,4)` at `−4/5`; `{0,2}` dominates, with gap
`[[56/25, 81/100], [81/100, 749/1600]]` of determinant `157/400`.

What makes it worth having next to the paper's `(7,3)` proposition is the DIAGNOSIS.
There the weight-scaled score is the one that misfires.  Here it is the determinant:
`weightScaledVolumeScore` — the same determinant scaled by `∏_{c ∈ C} t_c` — takes the
values `7/24`, `7/12`, `1/8`, so ITS strict maximiser is `{0,2}`, and `{0,2}` dominates
(`corankOneVolumeRuleDesign_weightScaledVolumeMaximiser_dominates`).  So at this design
the weighting is innocent and the bare determinant is what fails, which is the exact
complement of the paper's reading of its own witness.

## Deliberately absent

* No minimality claim.  The theorem is that the rule fails at these sizes; that no
  smaller or simpler witness exists is not asserted, and was not proved.
* No claim that the general-weight failure of the DETERMINANT rule is a new phenomenon at
  rank three or beyond.  Both witnesses here are rank two, where domination is decided.
* No claim about any rule other than the volume rule.  In particular maximizing
  `λ_min(S_C)` is untouched, and cannot be refuted: its argmax dominates whenever any
  subset does.
* No claim about the algorithmic half of `prob:effective` — whether some polynomial rule
  exhibits a dominating subset.  Refuting one named rule is not an impossibility theorem,
  and nothing here is one.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.ExchangeInvariant
import Gtz.Reduction.RayleighCertificate
import Gtz.Ties.SelectionObstruction

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-! ## The score the rule maximizes -/

/-- **The unweighted volume score** of a subset: `det S_C`, the determinant of the
selected atoms' Gram sum.  For `|C| = k` this is the squared volume `det(G_C)²` of the
selected atom rows, so "a subset of maximal volume" in the sense of Goreinov and
Tyrtyshnikov is exactly "a subset of maximal `volumeScore`". -/
noncomputable def volumeScore {m k : ℕ} (D : WeightedDesign m k) (C : Finset (Fin m)) : ℝ :=
  (subsetSum D C).det

/-- **The weight-scaled volume score**: the same determinant scaled by the product of the
selected weights.  At `|C| = k` this IS the volume-sampling probability
`Gtz.shadowDeterminant` — see `weightScaledVolumeScore_eq_shadowDeterminant` — so the two
readings of "a subset of maximal volume" are exactly `volumeScore` and this. -/
noncomputable def weightScaledVolumeScore {m k : ℕ} (D : WeightedDesign m k)
    (C : Finset (Fin m)) : ℝ :=
  (∏ atomIndex ∈ C, D.weight atomIndex) * volumeScore D C

/-- **`C` is the strict volume maximiser**: a `k`-subset that every other `k`-subset
falls strictly below.  Strictness is what removes the escape "the rule was free to
return a different maximiser". -/
def IsStrictVolumeMaximiser {m k : ℕ} (D : WeightedDesign m k) (C : Finset (Fin m)) : Prop :=
  C.card = k ∧ ∀ other : Finset (Fin m), other.card = k → other ≠ C →
    volumeScore D other < volumeScore D C

/-- The weight-scaled analogue, so that the two readings of the rule can be compared at
one design rather than conflated. -/
def IsStrictWeightScaledVolumeMaximiser {m k : ℕ} (D : WeightedDesign m k)
    (C : Finset (Fin m)) : Prop :=
  C.card = k ∧ ∀ other : Finset (Fin m), other.card = k → other ≠ C →
    weightScaledVolumeScore D other < weightScaledVolumeScore D C

/-! ## The two scores, identified

`Gtz.shadowDeterminant` is the score the paper's own general-weight witness refutes.  It
is `weightScaledVolumeScore` at selection size exactly the rank, so both readings of the
rule are available below in one vocabulary and neither can be silently substituted for the
other. -/

/-- **The weight-scaled score is the volume-sampling probability** at selection size
exactly the rank.  `shadowDeterminant_eq_weightProduct_mul_detSq` supplies the evaluation
and `transpose_mul_selectedAtomRows` turns the squared row determinant into
`det S_C`. -/
theorem weightScaledVolumeScore_eq_shadowDeterminant {m k : ℕ} (D : WeightedDesign m k)
    {selected : Finset (Fin m)} (pick : Fin k → Fin m) (hinj : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = selected) :
    weightScaledVolumeScore D selected = shadowDeterminant D selected := by
  rw [weightScaledVolumeScore, volumeScore,
    shadowDeterminant_eq_weightProduct_mul_detSq D pick hinj himage, ← himage,
    ← transpose_mul_selectedAtomRows D pick hinj, Matrix.det_mul, Matrix.det_transpose,
    ← pow_two, Finset.prod_image fun left _ right _ hlr => hinj hlr]

/-- The subset-indexed form, with the selection supplied by the subset's own order
embedding. -/
theorem weightScaledVolumeScore_eq_shadowDeterminant_ofCard {m k : ℕ}
    (D : WeightedDesign m k) {selected : Finset (Fin m)} (hcard : selected.card = k) :
    weightScaledVolumeScore D selected = shadowDeterminant D selected :=
  weightScaledVolumeScore_eq_shadowDeterminant D (selected.orderEmbOfFin hcard)
    (selected.orderEmbOfFin hcard).injective (image_orderEmbOfFin hcard)

/-! ## The pair kit at rank two -/

/-- A two-element subset sum is the sum of its two atoms. -/
theorem subsetSum_pair {m k : ℕ} (D : WeightedDesign m k) {first second : Fin m}
    (hne : first ≠ second) :
    subsetSum D {first, second}
      = atomMatrix (D.atom first) + atomMatrix (D.atom second) := by
  rw [subsetSum, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]

/-- **Cauchy–Binet at rank two**: the volume score of a pair is the square of the `2 × 2`
minor of its two atoms.  Every volume comparison below is therefore a comparison of two
squared minors, which `norm_num` settles on rationals. -/
theorem volumeScore_pair {m : ℕ} (D : WeightedDesign m 2) {first second : Fin m}
    (hne : first ≠ second) :
    volumeScore D {first, second}
      = (D.atom first 0 * D.atom second 1 - D.atom first 1 * D.atom second 0) ^ 2 := by
  rw [volumeScore, subsetSum_pair D hne, Matrix.det_fin_two]
  simp only [Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply]
  ring

/-- The weight-scaled score of a pair, in the same closed form. -/
theorem weightScaledVolumeScore_pair {m : ℕ} (D : WeightedDesign m 2)
    {first second : Fin m} (hne : first ≠ second) :
    weightScaledVolumeScore D {first, second}
      = D.weight first * D.weight second
        * (D.atom first 0 * D.atom second 1 - D.atom first 1 * D.atom second 0) ^ 2 := by
  rw [weightScaledVolumeScore, volumeScore_pair D hne,
    Finset.prod_insert (by simpa using hne), Finset.prod_singleton]

/-- The two-atom reading of `not_dominates_of_negativeDirection`: one explicit direction
at which the two selected atoms fail to majorize the identity form refutes domination. -/
theorem not_dominates_pair_of_negativeDirection {m dim : ℕ} (D : WeightedDesign m dim)
    {first second : Fin m} (hne : first ≠ second) (testVec : Fin dim → ℝ)
    (hnegative : (D.atom first ⬝ᵥ testVec) ^ 2 + (D.atom second ⬝ᵥ testVec) ^ 2
        < testVec ⬝ᵥ testVec) :
    ¬ Dominates D {first, second} := by
  refine not_dominates_of_negativeDirection D _ testVec ?_
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  linarith

/-- The converse at a pair: two atoms that majorize the identity form at every direction
dominate.  The Hermitian half is free, a sum of atoms being symmetric. -/
theorem dominates_pair_of_coercive {m dim : ℕ} (D : WeightedDesign m dim)
    {first second : Fin m} (hne : first ≠ second)
    (hcoercive : ∀ testVec : Fin dim → ℝ, testVec ⬝ᵥ testVec
        ≤ (D.atom first ⬝ᵥ testVec) ^ 2 + (D.atom second ⬝ᵥ testVec) ^ 2) :
    Dominates D {first, second} := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe => ?_⟩
  · exact ((Matrix.posSemidef_sum ({first, second} : Finset (Fin m))
      fun atomIndex _ => posSemidef_atomMatrix (D.atom atomIndex)).1).sub
        Matrix.isHermitian_one
  · rw [star_trivial, dominationGap_form,
      Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
    linarith [hcoercive probe]

/-- **The three `2`-subsets of `Fin 3`**, enumerated by decision. -/
theorem finset_card_two_cases_atSizeThree (C : Finset (Fin 3)) (hcard : C.card = 2) :
    C = {0, 1} ∨ C = {0, 2} ∨ C = {1, 2} := by
  revert hcard
  revert C
  decide

/-- **The six `2`-subsets of `Fin 4`**, enumerated by decision. -/
theorem finset_card_two_cases_atSizeFour (C : Finset (Fin 4)) (hcard : C.card = 2) :
    C = {0, 1} ∨ C = {0, 2} ∨ C = {0, 3} ∨ C = {1, 2} ∨ C = {1, 3} ∨ C = {2, 3} := by
  revert hcard
  revert C
  decide

/-! ## The general-weight witness at `(3,2)`: corank one, where the determinant fails
and the weighting does not

Three atoms whose entries have denominator dividing `40`, weights
`(56/81, 25/243, 50/243)`.  The design is corank
one — `m = k + 1` — so it sits inside the region the campaign considers closed: rank two
is a theorem and the corank-one ties are completely classified.  The volume rule fails
there anyway. -/

/-- The three atoms of the corank-one volume witness. -/
noncomputable def corankOneVolumeRuleAtom : Fin 3 → Fin 2 → ℝ :=
  ![![0, (9/8)], ![(9/5), -(9/10)], ![(9/5), (9/20)]]

/-- The exactly rational corank-one `(3,2)` design whose strict volume maximiser does not
dominate. -/
noncomputable def corankOneVolumeRuleDesign : WeightedDesign 3 2 where
  atom := corankOneVolumeRuleAtom
  weight := ![56/81, 25/243, 50/243]
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_three, smul_eq_mul, corankOneVolumeRuleAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- The volume score at `{0,1}`: the minor is `−81/40`. -/
theorem corankOneVolumeRuleDesign_volumeScore_zeroOne :
    volumeScore corankOneVolumeRuleDesign {0, 1} = 6561/1600 := by
  rw [volumeScore_pair corankOneVolumeRuleDesign (show (0 : Fin 3) ≠ 1 by decide)]
  simp only [corankOneVolumeRuleDesign, corankOneVolumeRuleAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- The volume score at `{0,2}`: the minor is `−81/40`, the same as at `{0,1}`. -/
theorem corankOneVolumeRuleDesign_volumeScore_zeroTwo :
    volumeScore corankOneVolumeRuleDesign {0, 2} = 6561/1600 := by
  rw [volumeScore_pair corankOneVolumeRuleDesign (show (0 : Fin 3) ≠ 2 by decide)]
  simp only [corankOneVolumeRuleDesign, corankOneVolumeRuleAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- The volume score at `{1,2}`: the minor is `243/100`, and this is the maximum. -/
theorem corankOneVolumeRuleDesign_volumeScore_oneTwo :
    volumeScore corankOneVolumeRuleDesign {1, 2} = 59049/10000 := by
  rw [volumeScore_pair corankOneVolumeRuleDesign (show (1 : Fin 3) ≠ 2 by decide)]
  simp only [corankOneVolumeRuleDesign, corankOneVolumeRuleAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- **`{1,2}` is the strict volume maximiser**, `59049/10000` against `6561/1600` twice —
a margin of `72171/40000`.  Computed at every `2`-subset, not asserted. -/
theorem corankOneVolumeRuleDesign_isStrictVolumeMaximiser :
    IsStrictVolumeMaximiser corankOneVolumeRuleDesign {1, 2} := by
  refine ⟨by decide, fun other hcard hne => ?_⟩
  rcases finset_card_two_cases_atSizeThree other hcard with rfl | rfl | rfl
  · rw [corankOneVolumeRuleDesign_volumeScore_zeroOne,
      corankOneVolumeRuleDesign_volumeScore_oneTwo]
    norm_num
  · rw [corankOneVolumeRuleDesign_volumeScore_zeroTwo,
      corankOneVolumeRuleDesign_volumeScore_oneTwo]
    norm_num
  · exact absurd rfl hne

/-- **The volume maximiser does not dominate**: the integer direction `(1,4)` sees total
squared projection `81/5` against `|x|² = 17`, a gap of `−4/5`. -/
theorem corankOneVolumeRuleDesign_not_dominates_oneTwo :
    ¬ Dominates corankOneVolumeRuleDesign {1, 2} := by
  refine not_dominates_pair_of_negativeDirection corankOneVolumeRuleDesign
    (show (1 : Fin 3) ≠ 2 by decide) ![1, 4] ?_
  simp only [corankOneVolumeRuleDesign, corankOneVolumeRuleAtom, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- **Another subset does dominate**, so this is a counterexample to the RULE and not to
`GtzWeighted`.  The gap form of `{0,2}` is `(224x₀ + 81x₁)²/22400 + (157/896)x₁²`, a
manifest sum of squares; the gap determinant is `157/400`. -/
theorem corankOneVolumeRuleDesign_dominates_zeroTwo :
    Dominates corankOneVolumeRuleDesign {0, 2} := by
  refine dominates_pair_of_coercive corankOneVolumeRuleDesign
    (show (0 : Fin 3) ≠ 2 by decide) fun testVec => ?_
  simp only [corankOneVolumeRuleDesign, corankOneVolumeRuleAtom, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  nlinarith [sq_nonneg (224 * testVec 0 + 81 * testVec 1), sq_nonneg (testVec 1),
    sq_nonneg (testVec 0)]

/-! ### The weighting is innocent here

Scaling the same determinants by `∏_{c ∈ C} t_c` moves the argmax onto a subset that
DOES dominate, so at this design the failure is the determinant and not the weighting —
the exact complement of the diagnosis attached to the paper's `(7,3)` proposition. -/

/-- The weight-scaled score at `{0,1}`. -/
theorem corankOneVolumeRuleDesign_weightScaledVolumeScore_zeroOne :
    weightScaledVolumeScore corankOneVolumeRuleDesign {0, 1} = 7/24 := by
  rw [weightScaledVolumeScore_pair corankOneVolumeRuleDesign
    (show (0 : Fin 3) ≠ 1 by decide)]
  simp only [corankOneVolumeRuleDesign, corankOneVolumeRuleAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- The weight-scaled score at `{0,2}`, and this is the maximum. -/
theorem corankOneVolumeRuleDesign_weightScaledVolumeScore_zeroTwo :
    weightScaledVolumeScore corankOneVolumeRuleDesign {0, 2} = 7/12 := by
  rw [weightScaledVolumeScore_pair corankOneVolumeRuleDesign
    (show (0 : Fin 3) ≠ 2 by decide)]
  simp only [corankOneVolumeRuleDesign, corankOneVolumeRuleAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- The weight-scaled score at `{1,2}` — the unweighted maximiser drops to last place. -/
theorem corankOneVolumeRuleDesign_weightScaledVolumeScore_oneTwo :
    weightScaledVolumeScore corankOneVolumeRuleDesign {1, 2} = 1/8 := by
  rw [weightScaledVolumeScore_pair corankOneVolumeRuleDesign
    (show (1 : Fin 3) ≠ 2 by decide)]
  simp only [corankOneVolumeRuleDesign, corankOneVolumeRuleAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- **The weight-scaled maximiser is `{0,2}`**, `7/12` against `7/24` and `1/8`. -/
theorem corankOneVolumeRuleDesign_isStrictWeightScaledVolumeMaximiser :
    IsStrictWeightScaledVolumeMaximiser corankOneVolumeRuleDesign {0, 2} := by
  refine ⟨by decide, fun other hcard hne => ?_⟩
  rcases finset_card_two_cases_atSizeThree other hcard with rfl | rfl | rfl
  · rw [corankOneVolumeRuleDesign_weightScaledVolumeScore_zeroOne,
      corankOneVolumeRuleDesign_weightScaledVolumeScore_zeroTwo]
    norm_num
  · exact absurd rfl hne
  · rw [corankOneVolumeRuleDesign_weightScaledVolumeScore_oneTwo,
      corankOneVolumeRuleDesign_weightScaledVolumeScore_zeroTwo]
    norm_num

/-- **The weight-scaled maximiser dominates here.**  So the general-weight failure of the
volume rule at this design is a failure of the DETERMINANT, with the weighting by
`∏_{c ∈ C} t_c` selecting correctly — the paper's `(7,3)` proposition fails the other
way round, and the two witnesses are complementary rather than duplicate. -/
theorem corankOneVolumeRuleDesign_weightScaledVolumeMaximiser_dominates :
    IsStrictWeightScaledVolumeMaximiser corankOneVolumeRuleDesign {0, 2}
      ∧ Dominates corankOneVolumeRuleDesign {0, 2} :=
  ⟨corankOneVolumeRuleDesign_isStrictWeightScaledVolumeMaximiser,
    corankOneVolumeRuleDesign_dominates_zeroTwo⟩

/-! ## The uniform witness at `(4,2)` — the case the paper singles out

Four atoms of denominator `25`, all weights `1/4`.  At uniform weights `∏_{c ∈ C} t_c` is
the same number for every `2`-subset, so the two readings of "maximal volume" have the
same argmax and this one design refutes both. -/

/-- The four atoms of the uniform-weight volume witness. -/
noncomputable def uniformVolumeRuleAtom : Fin 4 → Fin 2 → ℝ :=
  ![![-(7/5), (17/25)], ![-(7/5), -(17/25)], ![(1/5), -(31/25)], ![-(1/5), -(31/25)]]

/-- The exactly rational `(4,2)` design at UNIFORM weights whose strict volume maximiser
does not dominate. -/
noncomputable def uniformVolumeRuleDesign : WeightedDesign 4 2 where
  atom := uniformVolumeRuleAtom
  weight := ![1/4, 1/4, 1/4, 1/4]
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_four, smul_eq_mul, uniformVolumeRuleAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- **The weights are exactly uniform** — every atom carries `1/4`. -/
theorem uniformVolumeRuleDesign_weight_eq (atomIndex : Fin 4) :
    uniformVolumeRuleDesign.weight atomIndex = 1/4 := by
  fin_cases atomIndex <;> rfl

/-- The volume score at `{0,1}`: the minor is `238/125`, and this is the maximum. -/
theorem uniformVolumeRuleDesign_volumeScore_zeroOne :
    volumeScore uniformVolumeRuleDesign {0, 1} = 56644/15625 := by
  rw [volumeScore_pair uniformVolumeRuleDesign (show (0 : Fin 4) ≠ 1 by decide)]
  simp only [uniformVolumeRuleDesign, uniformVolumeRuleAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- The volume score at `{0,2}`: the minor is `8/5`. -/
theorem uniformVolumeRuleDesign_volumeScore_zeroTwo :
    volumeScore uniformVolumeRuleDesign {0, 2} = 64/25 := by
  rw [volumeScore_pair uniformVolumeRuleDesign (show (0 : Fin 4) ≠ 2 by decide)]
  simp only [uniformVolumeRuleDesign, uniformVolumeRuleAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- The volume score at `{0,3}`: the minor is `234/125`, the runner-up. -/
theorem uniformVolumeRuleDesign_volumeScore_zeroThree :
    volumeScore uniformVolumeRuleDesign {0, 3} = 54756/15625 := by
  rw [volumeScore_pair uniformVolumeRuleDesign (show (0 : Fin 4) ≠ 3 by decide)]
  simp only [uniformVolumeRuleDesign, uniformVolumeRuleAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_three, Matrix.tail_cons]
  norm_num

/-- The volume score at `{1,2}`: the minor is `234/125`, tied for runner-up. -/
theorem uniformVolumeRuleDesign_volumeScore_oneTwo :
    volumeScore uniformVolumeRuleDesign {1, 2} = 54756/15625 := by
  rw [volumeScore_pair uniformVolumeRuleDesign (show (1 : Fin 4) ≠ 2 by decide)]
  simp only [uniformVolumeRuleDesign, uniformVolumeRuleAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- The volume score at `{1,3}`: the minor is `8/5`. -/
theorem uniformVolumeRuleDesign_volumeScore_oneThree :
    volumeScore uniformVolumeRuleDesign {1, 3} = 64/25 := by
  rw [volumeScore_pair uniformVolumeRuleDesign (show (1 : Fin 4) ≠ 3 by decide)]
  simp only [uniformVolumeRuleDesign, uniformVolumeRuleAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_three, Matrix.tail_cons]
  norm_num

/-- The volume score at `{2,3}`: the minor is `−62/125`, the smallest. -/
theorem uniformVolumeRuleDesign_volumeScore_twoThree :
    volumeScore uniformVolumeRuleDesign {2, 3} = 3844/15625 := by
  rw [volumeScore_pair uniformVolumeRuleDesign (show (2 : Fin 4) ≠ 3 by decide)]
  simp only [uniformVolumeRuleDesign, uniformVolumeRuleAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons]
  norm_num

/-- **`{0,1}` is the strict volume maximiser**, `56644/15625` against the runner-up
`54756/15625` — a margin of `1888/15625`.  All six scores are computed. -/
theorem uniformVolumeRuleDesign_isStrictVolumeMaximiser :
    IsStrictVolumeMaximiser uniformVolumeRuleDesign {0, 1} := by
  refine ⟨by decide, fun other hcard hne => ?_⟩
  rw [uniformVolumeRuleDesign_volumeScore_zeroOne]
  rcases finset_card_two_cases_atSizeFour other hcard with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hne
  · rw [uniformVolumeRuleDesign_volumeScore_zeroTwo]; norm_num
  · rw [uniformVolumeRuleDesign_volumeScore_zeroThree]; norm_num
  · rw [uniformVolumeRuleDesign_volumeScore_oneTwo]; norm_num
  · rw [uniformVolumeRuleDesign_volumeScore_oneThree]; norm_num
  · rw [uniformVolumeRuleDesign_volumeScore_twoThree]; norm_num

/-- At uniform weights the weight-scaled score is the unweighted one divided by `16`:
`∏_{c ∈ C} t_c = (1/4)²` for every `2`-subset, whatever the subset.  This is why one
witness settles both readings of the rule here. -/
theorem uniformVolumeRuleDesign_weightScaledVolumeScore_eq (C : Finset (Fin 4))
    (hcard : C.card = 2) :
    weightScaledVolumeScore uniformVolumeRuleDesign C
      = (1/16) * volumeScore uniformVolumeRuleDesign C := by
  rw [weightScaledVolumeScore,
    Finset.prod_congr rfl fun atomIndex _ => uniformVolumeRuleDesign_weight_eq atomIndex,
    Finset.prod_const, hcard]
  norm_num

/-- **`{0,1}` is the strict maximiser of the weight-scaled score too**: the uniform weights
carry the unweighted comparison across unchanged. -/
theorem uniformVolumeRuleDesign_isStrictWeightScaledVolumeMaximiser :
    IsStrictWeightScaledVolumeMaximiser uniformVolumeRuleDesign {0, 1} := by
  obtain ⟨hcardMaximiser, hstrict⟩ := uniformVolumeRuleDesign_isStrictVolumeMaximiser
  refine ⟨hcardMaximiser, fun other hcard hne => ?_⟩
  rw [uniformVolumeRuleDesign_weightScaledVolumeScore_eq other hcard,
    uniformVolumeRuleDesign_weightScaledVolumeScore_eq {0, 1} hcardMaximiser]
  linarith [hstrict other hcard hne]

/-- **The volume maximiser does not dominate.**  Its atom sum is DIAGONAL,
`diag(98/25, 578/625)`, so the coordinate direction `(0,1)` alone decides it: total
squared projection `578/625` against `|x|² = 1`, a gap of `−47/625`.  The least
eigenvalue is therefore the rational `578/625` and no surd appears anywhere. -/
theorem uniformVolumeRuleDesign_not_dominates_zeroOne :
    ¬ Dominates uniformVolumeRuleDesign {0, 1} := by
  refine not_dominates_pair_of_negativeDirection uniformVolumeRuleDesign
    (show (0 : Fin 4) ≠ 1 by decide) ![0, 1] ?_
  simp only [uniformVolumeRuleDesign, uniformVolumeRuleAtom, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **`{0,3}` dominates**: gap form `(125x₀ − 88x₁)²/15625 + (7881/15625)x₁²`, gap
determinant `7881/15625`. -/
theorem uniformVolumeRuleDesign_dominates_zeroThree :
    Dominates uniformVolumeRuleDesign {0, 3} := by
  refine dominates_pair_of_coercive uniformVolumeRuleDesign
    (show (0 : Fin 4) ≠ 3 by decide) fun testVec => ?_
  simp only [uniformVolumeRuleDesign, uniformVolumeRuleAtom, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_three, Matrix.tail_cons]
  nlinarith [sq_nonneg (125 * testVec 0 - 88 * testVec 1), sq_nonneg (testVec 1),
    sq_nonneg (testVec 0)]

/-- **`{1,2}` dominates too**, by the mirror sum of squares
`(125x₀ + 88x₁)²/15625 + (7881/15625)x₁²`. -/
theorem uniformVolumeRuleDesign_dominates_oneTwo :
    Dominates uniformVolumeRuleDesign {1, 2} := by
  refine dominates_pair_of_coercive uniformVolumeRuleDesign
    (show (1 : Fin 4) ≠ 2 by decide) fun testVec => ?_
  simp only [uniformVolumeRuleDesign, uniformVolumeRuleAtom, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  nlinarith [sq_nonneg (125 * testVec 0 + 88 * testVec 1), sq_nonneg (testVec 1),
    sq_nonneg (testVec 0)]

/-! ## The headline statements

Each names a design, its strict volume maximiser, and a subset that does dominate.  The
last conjunct is what keeps the statement a refutation of the RULE: `GtzWeighted` holds
at both witnesses, exhibited. -/

/-- **THE MAXIMAL-VOLUME RULE CAN FAIL TO DOMINATE — at general weights, at corank one.**
There is a weighted `(3,2)` design whose UNIQUE volume-maximising `2`-subset does not
dominate while another `2`-subset does.  The cell is `m = k + 1`, where `GtzWeighted` is
a theorem and the ties are completely classified, so nothing here bears on the open
`(6,3)` and `(7,3)`; what fails is the selection rule alone. -/
theorem volumeMaximiser_can_fail_to_dominate :
    ∃ (D : WeightedDesign 3 2) (maximiser dominator : Finset (Fin 3)),
      IsStrictVolumeMaximiser D maximiser
      ∧ ¬ Dominates D maximiser
      ∧ dominator.card = 2 ∧ Dominates D dominator :=
  ⟨corankOneVolumeRuleDesign, {1, 2}, {0, 2},
    corankOneVolumeRuleDesign_isStrictVolumeMaximiser,
    corankOneVolumeRuleDesign_not_dominates_oneTwo,
    by decide, corankOneVolumeRuleDesign_dominates_zeroTwo⟩

/-- **THE MAXIMAL-VOLUME RULE CAN FAIL TO DOMINATE AT UNIFORM WEIGHTS.**  This is the
question the paper's `prob:effective` leaves standing apart from the conjecture — its own
general-weight witness breaks the weighting by `∏_{c ∈ C} t_c` rather than the
determinant, so the uniform case, where those two scores have the same argmax, stayed
open.  The answer is NO: at this `(4,2)` design all four weights are `1/4`, the strict
volume maximiser `{0,1}` fails on the coordinate direction `(0,1)` at gap `−47/625` — its
atom sum being `diag(98/25, 578/625)`, so `578/625 < 1` is the whole obstruction — and
`{0,3}` dominates.  Again a refutation of the RULE, not of `GtzWeighted`: the dominating
subset is exhibited in the statement. -/
theorem volumeMaximiser_can_fail_to_dominate_atUniformWeights :
    ∃ (D : WeightedDesign 4 2) (maximiser dominator : Finset (Fin 4)),
      (∀ atomIndex : Fin 4, D.weight atomIndex = 1/4)
      ∧ IsStrictVolumeMaximiser D maximiser
      ∧ ¬ Dominates D maximiser
      ∧ dominator.card = 2 ∧ Dominates D dominator :=
  ⟨uniformVolumeRuleDesign, {0, 1}, {0, 3},
    uniformVolumeRuleDesign_weight_eq,
    uniformVolumeRuleDesign_isStrictVolumeMaximiser,
    uniformVolumeRuleDesign_not_dominates_zeroOne,
    by decide, uniformVolumeRuleDesign_dominates_zeroThree⟩

/-- **THE VOLUME-SAMPLING MAXIMISER CAN FAIL TO DOMINATE AT UNIFORM WEIGHTS** — the same
witness, restated in `Gtz.shadowDeterminant`, the score the paper's own general-weight
proposition uses.  So the answer does not turn on which reading of "a subset of maximal
volume" is meant: at uniform weights the two scores have the same strict argmax, and it
does not dominate while another `2`-subset does. -/
theorem shadowDeterminantMaximiser_can_fail_to_dominate_atUniformWeights :
    ∃ (D : WeightedDesign 4 2) (maximiser dominator : Finset (Fin 4)),
      (∀ atomIndex : Fin 4, D.weight atomIndex = 1/4)
      ∧ maximiser.card = 2
      ∧ (∀ other : Finset (Fin 4), other.card = 2 → other ≠ maximiser →
          shadowDeterminant D other < shadowDeterminant D maximiser)
      ∧ ¬ Dominates D maximiser
      ∧ dominator.card = 2 ∧ Dominates D dominator := by
  obtain ⟨hcardMaximiser, hstrict⟩ :=
    uniformVolumeRuleDesign_isStrictWeightScaledVolumeMaximiser
  refine ⟨uniformVolumeRuleDesign, {0, 1}, {0, 3}, uniformVolumeRuleDesign_weight_eq,
    hcardMaximiser, fun other hcard hne => ?_,
    uniformVolumeRuleDesign_not_dominates_zeroOne, by decide,
    uniformVolumeRuleDesign_dominates_zeroThree⟩
  rw [← weightScaledVolumeScore_eq_shadowDeterminant_ofCard uniformVolumeRuleDesign hcard,
    ← weightScaledVolumeScore_eq_shadowDeterminant_ofCard uniformVolumeRuleDesign
      hcardMaximiser]
  exact hstrict other hcard hne

/-- **The rule, refuted in the shape a rule has**, at `(3,2)`: "the strict volume
maximiser dominates" is not a theorem. -/
theorem not_forall_strictVolumeMaximiser_dominates_atSizeThree :
    ¬ ∀ (D : WeightedDesign 3 2) (C : Finset (Fin 3)),
        IsStrictVolumeMaximiser D C → Dominates D C := by
  intro hrule
  exact corankOneVolumeRuleDesign_not_dominates_oneTwo
    (hrule corankOneVolumeRuleDesign {1, 2}
      corankOneVolumeRuleDesign_isStrictVolumeMaximiser)

/-- **The rule, refuted in the shape a rule has**, at `(4,2)`.  Uniformity of the weights
sits INSIDE the refuted statement, so restricting the rule to uniform weights — the
restriction under which it was still open — does not rescue it. -/
theorem not_forall_strictVolumeMaximiser_dominates_atSizeFour :
    ¬ ∀ (D : WeightedDesign 4 2) (C : Finset (Fin 4)),
        (∀ atomIndex : Fin 4, D.weight atomIndex = 1/4) →
        IsStrictVolumeMaximiser D C → Dominates D C := by
  intro hrule
  exact uniformVolumeRuleDesign_not_dominates_zeroOne
    (hrule uniformVolumeRuleDesign {0, 1} uniformVolumeRuleDesign_weight_eq
      uniformVolumeRuleDesign_isStrictVolumeMaximiser)

end Gtz

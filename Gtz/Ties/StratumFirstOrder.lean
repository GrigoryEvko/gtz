/-
# The split-tetrahedron tie stratum is first-order rigid — second order is NOT

`Gtz.Ties.SevenThreeTieLocus` pins the `(7,3)` split tetrahedron as an exact tie: of
its `35` triples exactly `20` dominate, all with margin exactly `0`, and none
dominates strictly.  That answers "does anything dominate HERE".  This file answers
the next question — "can a perturbation destroy it" — at FIRST order, and answers it
NO, with an explicit rational certificate.  It also answers the obvious follow-up at
SECOND order, and there the answer is YES: an explicit admissible velocity is shipped
that is critical for a triple and destroys that triple anyway.

## The certificate

Write `v_0 … v_3` for the four tetrahedron directions (`tetraAtom`, `|v_d|² = 3`,
`v_c ⬝ᵥ v_d = -1` off the diagonal, `∑_d v_d = 0`) and `T_0 … T_19` for the twenty
rainbow triples (`rainbowSevenTriple`), each carrying three distinct directions and
missing a fourth, `v_{miss T}`.  That the table IS the rainbow family is DECIDED, not
asserted: the twenty entries are pairwise distinct (`rainbowSevenTriple_injective`) and
a subset is in the table exactly when it has three atoms carrying three distinct
directions (`rainbowSevenTriple_eq_rainbowFamily`).  The multipliers are

  `λ_T = 1/32` on the eight triples missing the unsplit direction, `1/16` on the twelve
  containing the unsplit atom,

and `splitSevenDesign_farkasIdentity` is the certificate firing:

  `∑_T λ_T · (velocity of T's gap form at v_{miss T}) = 2 ∑_c t_c ⟨g_c, dg_c⟩`,

whose right side vanishes on every tangent direction, because every leverage here is
exactly `3` and the weight velocity is traceless
(`splitSevenDesign_velocityPairing_zero`).  Twenty STRICTLY POSITIVE multipliers
summing something to zero forbid all twenty summands from being negative
(`rainbowSeven_exists_nonnegative_velocity`) and force one strictly positive as soon
as any is nonzero (`rainbowSeven_exists_positive_velocity`).

## What "no first-order descent" actually buys

The velocities are velocities of the gap FORM at the frozen probe `v_{miss T}`, not of
the smallest eigenvalue.  One direction of the bridge is elementary and IS mechanized
here: a strictly negative velocity really destroys the triple, because a negative form
at ANY fixed probe already breaks positive semidefiniteness —
`rainbowSevenTriple_ray_not_posSemidef_of_velocity_neg`, read off the exact expansion
`rainbowSevenTriple_rayGapForm_missedDirection`.  So the certificate does block the
elementary route to a nearby counterexample: no admissible velocity drives all twenty
triples down at once.

The converse direction is NOT available and is not claimed.  A nonnegative — even
strictly positive — form velocity does not keep a triple dominating, because the bottom
eigenvector moves too.  `rainbowSeven_exists_positive_velocity` says a form goes up; it
does NOT say a triple survives.

## A refuted second-order claim, and the counterexample shipped in its place

An earlier draft shipped `rainbowSeven_secondOrder_positive`: at a velocity killing a
triple's first-order term, the gap form AT THE FROZEN TIE DIRECTION moves strictly up
at order two, its quadratic coefficient being a sum of squares.  The statement is true
and worthless — it is the leading term of a difference whose second term it never
bounds — and reading it as second-order rigidity is simply wrong.  It has been DELETED
and replaced by an exact refutation of that reading:

  `stratumCriticalAtomVelocity` (`dg_0 = e_0`, `dg_1 = −e_0`, the other five zero) with
  `stratumCriticalWeightVelocity` (`dt_0 = −1/8`, `dt_1 = 1/8`) has zero mass velocity
  (`stratumCriticalVelocity_mass_zero`) and zero Parseval-trace velocity
  (`stratumCriticalVelocity_parsevalTrace_zero`), is CRITICAL for triple `0`
  (`stratumCriticalVelocity_gapFormVelocity_zero`), and has frozen-form second-order
  coefficient exactly `2 > 0` (`stratumCriticalVelocity_frozenQuadratic_eq_two`) — the
  deleted theorem's own conclusion.  Yet the perturbed gap is
  `!![2 + 2s², 2s − 1, 2s + 1; 2s − 1, 2, 1; 2s + 1, 1, 2]` with determinant `−2s²`
  (`stratumCriticalRay_gap_det`), so it FAILS positive semidefiniteness at every nonzero
  step (`stratumCriticalRay_not_posSemidef`).  The frozen form rises while the smallest
  eigenvalue crosses below zero.

That velocity is more than trace-tangent: with that `dt` it annihilates the FULL matrix
Parseval velocity `∑_c (dt_c g_c g_cᵀ + t_c (dg_c g_cᵀ + g_c dg_cᵀ))`, so it is a genuine
tangent direction of the design manifold and not an artifact of a weak hypothesis.  That
last computation is exact rational arithmetic done BY HAND and is NOT mechanized; the
theorems below only need the trace, which is proved.

## Where the multipliers come from — a coincidence here, not a mechanism

`rainbowSevenMultiplier_eq_det_projectionBlock` proves `λ_T = det(P_T)`, the principal
minor of the design's projection form, i.e. the volume-sampling probability of `T`.
That is a true identity AT THIS DESIGN and it is not the reason the certificate works:

* the certificate cone here is 7-dimensional and the SYMMETRIC certificate in it is
  UNIQUE.  With total mass `1` fixed (`rainbowSevenMultiplier_sum_one`), the order-48
  stabiliser of the split tetrahedron already forces any symmetric certificate to be
  this vector.  So `det(P_T)` is not predicting the numbers, it is coinciding with the
  only numbers available.  [MEASURED: exact rational linear algebra outside Lean.
  Neither the cone dimension nor the uniqueness is mechanized.]
* off this point the identification FAILS.  At other exactly-rational designs on the
  same tie stratum, and at this design with an uneven split, `∑_T det(P_T) · grad_T` is
  a NONZERO rational vector.  Certificates still exist there; they are not the
  volume-sampling measure.  [MEASURED.]

Read `λ_T = det(P_T)` as: at this design, the unique symmetric certificate happens to be
the determinantal measure.  `sum_det_projectionMinors_rank` gives total mass `1` over all
thirty-five subsets, so the fifteen rank-deficient triples carry nothing — still a
reading of two facts side by side.  `rainbowSevenTriple_injective` and
`rainbowSevenTriple_eq_rainbowFamily` close the combinatorial two thirds of it; the
determinant reindexing from `rainbowSevenPick` to the `Subtype.val` pick of
`sum_det_projectionMinors_rank` remains unmechanized.

## Why this is linear algebra, not calculus

No derivative is taken anywhere.  A design's atoms enter the gap form QUADRATICALLY and
the trace identity `∑_c t_c |g_c|² = k` CUBICALLY, so moving along the ray
`g + s · dg` gives polynomials in `s` with exact coefficients:
`gapForm_ray_expansion` and `traceIdentity_ray_expansion`.  `gapFormVelocity` and
`parsevalTraceVelocity` are those `s`-linear coefficients by definition, so calling
them "first order" is a theorem about a polynomial, not a reading.

## The margin facts, and which of them are reproofs

* the closed form `S_T = 4·I − v_d v_dᵀ` (`splitSevenDesign_subsetSum_rainbow`), gap
  `3·I − v_d v_dᵀ`, hence domination by ONE Cauchy–Schwarz against `|v_d|² = 3` for all
  twenty at once (`rainbowSevenTriple_dominates`);
* the gap spectrum `{0, 3, 3}` mechanized on both sides: the gap kills `v_d`
  (`rainbowSevenTriple_tightEigenvector`) and acts as `3` on `v_d^⊥`
  (`rainbowSevenTriple_gap_mulVec_of_orthogonal`).  The smallest eigenvalue of `S_T` is
  exactly `1` as a THEOREM (`rainbowSevenTriple_lambdaMinMat_eq_one`), through the
  repo's own `dominates_iff_one_le_lambdaMinMat` / `one_lt_lambdaMinMat_iff_posDef` —
  previous drafts asserted it only in prose;
* the fifteen failures with an EXPLICIT witness: a direction-repeating triple spans at
  most two tetrahedron directions, and the common normal of that pair
  (`tetraNormalDirection`) sits in the kernel of the atom sum, giving gap form `−2`
  (`splitSevenDesign_twoDirection_gapForm_negative`);
* REPROOFS, labelled as such.  `rainbowSevenTriple_dominates` reproves
  `splitSevenDesign_dominates_of_rainbowDirections`
  (`Gtz.Quantitative.DecisionAtlasSevenThree`); `rainbowSevenTriple_not_posDef` reproves
  `splitSevenDesign_no_strictDominator` and
  `splitSevenDesign_repeatedDirection_fails_at_pairNormal` reproves
  `splitSevenDesign_not_dominates_of_repeatedDirection`, both from
  `Gtz.Ties.SevenThreeTieLocus`.  They earn their place by being uniform and by handing
  the velocity work the closed forms it needs — not by being new results.

## The corank-one stratum is the SAME locus, pulled back

An earlier draft dismissed `Gtz.Ties.CorankOneTieExistence` as "a genuinely different
locus — it lives at `m = k + 1`".  That is wrong, and the correction matters because it
names what the first-order package cannot see through.

`tripleSplitTetraDesign_eq_splitSevenDesign` already proves that `splitSevenDesign` IS
the triple split of the `(4,3)` tetrahedron.  Splitting is a replica map, and the tie
stratum through this point pulls back the corank-one Naimark stratum at `m = k + 1`
along it: in aggregate weights `w_d` the stratum is `q_d² = (1 − w_d)/3`, equivalently
`ℓ_d = (2 + w_d)/(3 w_d)`, which is verbatim `Gtz.leverage_of_isTie` at `k = 3`, and
`Gtz.exists_isTie_of_weights` says that stratum meets EVERY weight vector in the open
simplex.  Its tangent directions — three aggregate reweightings, three split
reweightings, three gauge — span exactly the critical cone on which the first-order
certificate is silent.  [DERIVED-BY-HAND for the closed form and the identification with
`leverage_of_isTie`, which is formula matching and not a typechecked bridge; MEASURED at
60 digits for the tangent-span equality.  None of this paragraph is mechanized.]

The old dismissal also gave a non-sequitur reason: that the fifteen direction-repeating
triples sit at gap determinant `−8`.  Those triples are artifacts of the split and have
no counterpart at `m = k + 1`; the determinant says nothing about the strata.

## Layering debt

`projectionBlock_eq_congruence` and `det_projectionBlock_of_design` are `{m k : ℕ}`-generic
facts about `projectionOfDesign` and belong beside `det_projectionBlock_sub_weightDiagonal`
in `Gtz.LinAlg.ProjectionForm`; `gapFormVelocity`, `gapForm_ray_expansion`, `leverageOf_ray`,
`parsevalTraceVelocity`, `traceIdentity_ray_expansion`, `rayAtomSum` and `rayAtomSum_gap_form`
are a generic velocity kit and belong in a module of their own.  They are parked in this
`Ties/` file only because it may not edit `Gtz/LinAlg/ProjectionForm.lean`.

## Honest scope

Everything here is about ONE point of ONE tie stratum at `(7,3)`.  The certificate is
also specific to the SYMMETRIC split: `rainbowSevenMultiplier_marginal` uses the weights
`t_c`, so it does not transfer to `Gtz.splitSevenReweighted`, whose atoms — and therefore
whose twenty gradients — are identical but whose weights are not.  Those reweighting
directions lie inside the critical cone.  Nothing here bears on the other tie classes at
`(7,3)`, on rank `≥ 4`, or on `GtzWeighted 7 3` itself.

`SplitSevenNeighbourhoodCovering` names what is left, together with the trivial
`splitSevenNeighbourhoodCovering_of_gtzWeighted` recording that it is a CONSEQUENCE of
the conjecture and therefore a necessary sub-goal.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Ties.SevenThreeTieLocus
import Gtz.Quantitative.StrictDomination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The tetrahedron closed form -/

/-- The four tetrahedron atoms resolve `4 · I`: the regular tetrahedron is a tight
frame with redundancy `4/3`.  Named away from the short `sum_atomMatrix_tetraAtom`,
which `Gtz.Reduction.MixedCharPolynomial` also declares inside `namespace Gtz`. -/
theorem sum_atomMatrix_tetraAtom_eq_four_smul_one :
    ∑ dir : Fin 4, atomMatrix (tetraAtom dir)
      = (4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowIndex colIndex
  simp only [Matrix.sum_apply, Fin.sum_univ_four, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [tetraAtom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

/-- **Three distinct tetrahedron directions sum to `4·I` minus the fourth.** -/
theorem sum_three_atomMatrix_tetraAtom {dirOne dirTwo dirThree missing : Fin 4}
    (hcover : ({dirOne, dirTwo, dirThree, missing} : Finset (Fin 4)) = Finset.univ)
    (hOneTwo : dirOne ≠ dirTwo) (hOneThree : dirOne ≠ dirThree)
    (hOneMissing : dirOne ≠ missing) (hTwoThree : dirTwo ≠ dirThree)
    (hTwoMissing : dirTwo ≠ missing) (hThreeMissing : dirThree ≠ missing) :
    atomMatrix (tetraAtom dirOne) + atomMatrix (tetraAtom dirTwo)
        + atomMatrix (tetraAtom dirThree)
      = (4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (tetraAtom missing) := by
  have hfull := sum_atomMatrix_tetraAtom_eq_four_smul_one
  rw [← hcover, Finset.sum_insert (by simp [hOneTwo, hOneThree, hOneMissing]),
    Finset.sum_insert (by simp [hTwoThree, hTwoMissing]),
    Finset.sum_insert (by simp [hThreeMissing]), Finset.sum_singleton] at hfull
  rw [eq_sub_iff_add_eq, ← hfull]
  abel

/-! ## The twenty rainbow triples of the split tetrahedron -/

/-- The weights of the split tetrahedron: `1/4` on the unsplit atom `3`, `1/8` on each
of the six split copies. -/
theorem splitSevenDesign_weight_apply (atomIndex : Fin 7) :
    splitSevenDesign.weight atomIndex = if atomIndex = 3 then 1/4 else 1/8 := by
  fin_cases atomIndex <;> norm_num +decide [splitSevenDesign]

/-- First atom of the `i`-th rainbow triple. -/
def rainbowSevenFirst : Fin 20 → Fin 7 :=
  ![0, 0, 0, 0, 4, 4, 4, 4, 1, 1, 5, 5, 0, 0, 4, 4, 0, 0, 4, 4]

/-- Second atom of the `i`-th rainbow triple. -/
def rainbowSevenSecond : Fin 20 → Fin 7 :=
  ![1, 1, 5, 5, 1, 1, 5, 5, 2, 6, 2, 6, 2, 6, 2, 6, 1, 5, 1, 5]

/-- Third atom of the `i`-th rainbow triple. -/
def rainbowSevenThird : Fin 20 → Fin 7 :=
  ![2, 6, 2, 6, 2, 6, 2, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]

/-- The `i`-th rainbow triple: three atoms carrying three distinct tetrahedron
directions.  Eight of them omit the unsplit direction `3`, four omit each of the
split directions `0, 1, 2`. -/
def rainbowSevenTriple (tripleIndex : Fin 20) : Finset (Fin 7) :=
  {rainbowSevenFirst tripleIndex, rainbowSevenSecond tripleIndex,
    rainbowSevenThird tripleIndex}

/-- The tetrahedron direction the `i`-th rainbow triple misses — the tie direction
of its gap. -/
def rainbowSevenMissedDirection : Fin 20 → Fin 4 :=
  ![3, 3, 3, 3, 3, 3, 3, 3, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2]

/-- The Farkas multiplier of the `i`-th rainbow triple: `1/32` on the eight triples
missing the unsplit direction, `1/16` on the twelve containing the unsplit atom.  At
this design these coincide with the principal minors `det(P_T)`
(`rainbowSevenMultiplier_eq_det_projectionBlock`) — a coincidence forced by symmetry plus
total mass one, NOT a mechanism.  See the module header. -/
noncomputable def rainbowSevenMultiplier : Fin 20 → ℝ :=
  ![1/32, 1/32, 1/32, 1/32, 1/32, 1/32, 1/32, 1/32,
    1/16, 1/16, 1/16, 1/16, 1/16, 1/16, 1/16, 1/16, 1/16, 1/16, 1/16, 1/16]

/-- The three atoms of a rainbow triple are pairwise distinct. -/
theorem rainbowSevenIndices_distinct (tripleIndex : Fin 20) :
    rainbowSevenFirst tripleIndex ≠ rainbowSevenSecond tripleIndex
      ∧ rainbowSevenFirst tripleIndex ≠ rainbowSevenThird tripleIndex
      ∧ rainbowSevenSecond tripleIndex ≠ rainbowSevenThird tripleIndex := by
  decide +revert

/-- The three atoms of a rainbow triple carry three distinct tetrahedron
directions, none of them the missed one. -/
theorem rainbowSevenDirections_distinct (tripleIndex : Fin 20) :
    splitSevenDirection (rainbowSevenFirst tripleIndex)
        ≠ splitSevenDirection (rainbowSevenSecond tripleIndex)
      ∧ splitSevenDirection (rainbowSevenFirst tripleIndex)
        ≠ splitSevenDirection (rainbowSevenThird tripleIndex)
      ∧ splitSevenDirection (rainbowSevenSecond tripleIndex)
        ≠ splitSevenDirection (rainbowSevenThird tripleIndex) := by
  decide +revert

/-- No atom of a rainbow triple carries the missed direction. -/
theorem rainbowSevenDirections_ne_missed (tripleIndex : Fin 20) :
    splitSevenDirection (rainbowSevenFirst tripleIndex)
        ≠ rainbowSevenMissedDirection tripleIndex
      ∧ splitSevenDirection (rainbowSevenSecond tripleIndex)
        ≠ rainbowSevenMissedDirection tripleIndex
      ∧ splitSevenDirection (rainbowSevenThird tripleIndex)
        ≠ rainbowSevenMissedDirection tripleIndex := by
  decide +revert

/-- The three carried directions together with the missed one exhaust the
tetrahedron. -/
theorem rainbowSevenDirections_cover (tripleIndex : Fin 20) :
    ({splitSevenDirection (rainbowSevenFirst tripleIndex),
        splitSevenDirection (rainbowSevenSecond tripleIndex),
        splitSevenDirection (rainbowSevenThird tripleIndex),
        rainbowSevenMissedDirection tripleIndex} : Finset (Fin 4)) = Finset.univ := by
  decide +revert

/-- Summation over a rainbow triple is the three-term sum over its atoms. -/
theorem sum_rainbowSevenTriple {Carrier : Type*} [AddCommMonoid Carrier]
    (tripleIndex : Fin 20) (summand : Fin 7 → Carrier) :
    ∑ atomIndex ∈ rainbowSevenTriple tripleIndex, summand atomIndex
      = summand (rainbowSevenFirst tripleIndex) + summand (rainbowSevenSecond tripleIndex)
        + summand (rainbowSevenThird tripleIndex) := by
  obtain ⟨hOneTwo, hOneThree, hTwoThree⟩ := rainbowSevenIndices_distinct tripleIndex
  rw [rainbowSevenTriple, Finset.sum_insert (by simp [hOneTwo, hOneThree]),
    Finset.sum_insert (by simp [hTwoThree]), Finset.sum_singleton, add_assoc]

/-- Every rainbow triple has three elements. -/
theorem rainbowSevenTriple_card (tripleIndex : Fin 20) :
    (rainbowSevenTriple tripleIndex).card = 3 := by
  obtain ⟨hOneTwo, hOneThree, hTwoThree⟩ := rainbowSevenIndices_distinct tripleIndex
  rw [rainbowSevenTriple, Finset.card_insert_of_notMem (by simp [hOneTwo, hOneThree]),
    Finset.card_insert_of_notMem (by simp [hTwoThree]), Finset.card_singleton]

/-- **The twenty entries of the table are pairwise distinct triples.** -/
theorem rainbowSevenTriple_injective : Function.Injective rainbowSevenTriple := by
  decide +kernel

/-- **The table IS the rainbow family — sound and complete.**  A subset of the seven
atoms appears in the table exactly when it has three elements carrying three distinct
tetrahedron directions.  With `rainbowSevenTriple_injective` this decides two thirds of
the `20 + 15 = 35` census; only the determinant reindexing into
`sum_det_projectionMinors_rank` stays unmechanized. -/
theorem rainbowSevenTriple_eq_rainbowFamily (selected : Finset (Fin 7)) :
    (∃ tripleIndex : Fin 20, rainbowSevenTriple tripleIndex = selected)
      ↔ (selected.card = 3 ∧ ∀ atomOne ∈ selected, ∀ atomTwo ∈ selected,
            splitSevenDirection atomOne = splitSevenDirection atomTwo → atomOne = atomTwo) := by
  decide +kernel +revert

/-- Membership in a rainbow triple is membership in its three atoms. -/
theorem mem_rainbowSevenTriple_iff (tripleIndex : Fin 20) (atomIndex : Fin 7) :
    atomIndex ∈ rainbowSevenTriple tripleIndex
      ↔ atomIndex = rainbowSevenFirst tripleIndex
        ∨ atomIndex = rainbowSevenSecond tripleIndex
        ∨ atomIndex = rainbowSevenThird tripleIndex := by
  simp [rainbowSevenTriple]

/-- No atom of a rainbow triple carries the missed direction — the membership
form. -/
theorem rainbowSevenTriple_direction_ne_missed {tripleIndex : Fin 20} {atomIndex : Fin 7}
    (hmem : atomIndex ∈ rainbowSevenTriple tripleIndex) :
    splitSevenDirection atomIndex ≠ rainbowSevenMissedDirection tripleIndex := by
  obtain ⟨hone, htwo, hthree⟩ := rainbowSevenDirections_ne_missed tripleIndex
  rcases (mem_rainbowSevenTriple_iff tripleIndex atomIndex).mp hmem with rfl | rfl | rfl
  · exact hone
  · exact htwo
  · exact hthree

/-- Every multiplier is strictly positive. -/
theorem rainbowSevenMultiplier_pos (tripleIndex : Fin 20) :
    0 < rainbowSevenMultiplier tripleIndex := by
  fin_cases tripleIndex <;> norm_num [rainbowSevenMultiplier]

/-- **The multipliers are a probability measure on the twenty rainbow triples.**
Eight thirty-seconds plus twelve sixteenths is one.  Placed beside
`sum_det_projectionMinors_rank` — total mass one over all thirty-five subsets — this
reads as "the fifteen direction-repeating triples carry no volume", but that comparison
is a READING and not a theorem: the reindexing is not mechanized. -/
theorem rainbowSevenMultiplier_sum_one :
    ∑ tripleIndex : Fin 20, rainbowSevenMultiplier tripleIndex = 1 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, rainbowSevenMultiplier,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

/-! ## The twenty margin facts -/

/-- **The closed form of a rainbow triple's atom sum**: the three carried
directions are the tetrahedron minus the missed one, so
`S_T = 4·I − v_d v_dᵀ` with `d` the missed direction. -/
theorem splitSevenDesign_subsetSum_rainbow (tripleIndex : Fin 20) :
    subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex)
      = (4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - atomMatrix (tetraAtom (rainbowSevenMissedDirection tripleIndex)) := by
  obtain ⟨hOneTwo, hOneThree, hTwoThree⟩ := rainbowSevenDirections_distinct tripleIndex
  obtain ⟨hOneMissed, hTwoMissed, hThreeMissed⟩ :=
    rainbowSevenDirections_ne_missed tripleIndex
  rw [subsetSum, sum_rainbowSevenTriple]
  simp only [splitSevenDesign_atom]
  exact sum_three_atomMatrix_tetraAtom (rainbowSevenDirections_cover tripleIndex)
    hOneTwo hOneThree hOneMissed hTwoThree hTwoMissed hThreeMissed

/-- **The closed form of a rainbow triple's gap**: `S_T − I = 3·I − v_d v_dᵀ`,
positive semidefinite with a one-dimensional kernel spanned by `v_d`, because
`|v_d|² = 3` exactly. -/
theorem splitSevenDesign_rainbowGap (tripleIndex : Fin 20) :
    subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex) - 1
      = (3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - atomMatrix (tetraAtom (rainbowSevenMissedDirection tripleIndex)) := by
  rw [splitSevenDesign_subsetSum_rainbow]
  module

/-- The gap quadratic form of a rainbow triple: `3|x|² − ⟨v_d, x⟩²`. -/
theorem splitSevenDesign_rainbowGap_form (tripleIndex : Fin 20) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ ((subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex) - 1) *ᵥ probe)
      = 3 * (probe ⬝ᵥ probe)
        - (tetraAtom (rainbowSevenMissedDirection tripleIndex) ⬝ᵥ probe) ^ 2 := by
  rw [splitSevenDesign_rainbowGap, Matrix.sub_mulVec, dotProduct_sub, atom_form_eq_sq,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

/-- **Every rainbow triple dominates, with margin exactly zero.**  One Cauchy–Schwarz
against `|v_d|² = 3` covers all twenty at once — no case split on the sign pattern, no
`nlinarith`.  This is a REPROOF of `Gtz.splitSevenDesign_dominates_of_rainbowDirections`;
it is kept for the uniform route and for the closed form the velocity work consumes. -/
theorem rainbowSevenTriple_dominates (tripleIndex : Fin 20) :
    Dominates splitSevenDesign (rainbowSevenTriple tripleIndex) := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe => ?_⟩
  · exact ((Matrix.posSemidef_sum (rainbowSevenTriple tripleIndex) fun atomIndex _ =>
      posSemidef_atomMatrix (splitSevenDesign.atom atomIndex)).1).sub Matrix.isHermitian_one
  · rw [star_trivial, splitSevenDesign_rainbowGap_form]
    have hcauchy := dotProduct_sq_le_mul
      (tetraAtom (rainbowSevenMissedDirection tripleIndex)) probe
    rw [tetraAtom_dot_self] at hcauchy
    linarith

/-- **The margin is attained at the missed direction**: the gap form vanishes at `v_d`.
The eigenvalue reading of this — `λ_min(S_T) = 1` — is itself a theorem below,
`rainbowSevenTriple_lambdaMinMat_eq_one`. -/
theorem rainbowSevenTriple_gapForm_missedDirection (tripleIndex : Fin 20) :
    tetraAtom (rainbowSevenMissedDirection tripleIndex)
        ⬝ᵥ ((subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex) - 1)
          *ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex)) = 0 := by
  rw [splitSevenDesign_rainbowGap_form, tetraAtom_dot_self]
  norm_num

/-- **The bottom eigenvector is the missed direction**: `S_T · v_d = v_d`.  With
`rainbowSevenTriple_gap_mulVec_of_orthogonal` this pins the gap spectrum at `{0, 3, 3}`
— corank one, kernel `v_d` — on both sides, rather than asserting it in prose. -/
theorem rainbowSevenTriple_tightEigenvector (tripleIndex : Fin 20) :
    subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex)
        *ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex)
      = tetraAtom (rainbowSevenMissedDirection tripleIndex) :=
  tightDirection_isEigenvector splitSevenDesign (rainbowSevenTriple_dominates tripleIndex)
    (rainbowSevenTriple_gapForm_missedDirection tripleIndex)

/-- **The gap acts as `3` on the orthogonal complement of the missed direction.**  The
companion of `rainbowSevenTriple_tightEigenvector`: together the two mechanize the whole
gap spectrum `{0, 3, 3}`, kernel exactly the line through `v_d`. -/
theorem rainbowSevenTriple_gap_mulVec_of_orthogonal (tripleIndex : Fin 20)
    (probe : Fin 3 → ℝ)
    (horth : tetraAtom (rainbowSevenMissedDirection tripleIndex) ⬝ᵥ probe = 0) :
    (subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex) - 1) *ᵥ probe
      = (3 : ℝ) • probe := by
  rw [splitSevenDesign_rainbowGap, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    atomMatrix, vecMulVec_mulVec_eq, horth, zero_smul, sub_zero]

/-- **No rainbow triple dominates strictly.**  The gap kills `v_d ≠ 0`.  This is a
REPROOF of `Gtz.splitSevenDesign_no_strictDominator` restricted to the rainbow table. -/
theorem rainbowSevenTriple_not_posDef (tripleIndex : Fin 20) :
    ¬ (subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex) - 1).PosDef := by
  intro hposDef
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2
    (tetraAtom_ne_zero (rainbowSevenMissedDirection tripleIndex))
  rw [star_trivial, rainbowSevenTriple_gapForm_missedDirection] at hpos
  exact lt_irrefl 0 hpos

/-- **The smallest eigenvalue of a rainbow atom sum is exactly `1`.**  Weak domination
gives `1 ≤ λ_min` and the failure of strict domination gives `λ_min ≤ 1`, both through
the repo's own bridges — so "the margin is exactly zero" is an eigenvalue theorem here,
not a docstring reading. -/
theorem rainbowSevenTriple_lambdaMinMat_eq_one (tripleIndex : Fin 20) :
    lambdaMinMat (subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex)) = 1 := by
  have hhermitian : (subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex)).IsHermitian :=
    (Matrix.posSemidef_sum (rainbowSevenTriple tripleIndex) fun atomIndex _ =>
      posSemidef_atomMatrix (splitSevenDesign.atom atomIndex)).1
  refine le_antisymm (not_lt.mp ?_)
    ((dominates_iff_one_le_lambdaMinMat splitSevenDesign _).mp
      (rainbowSevenTriple_dominates tripleIndex))
  intro hlt
  exact rainbowSevenTriple_not_posDef tripleIndex
    ((one_lt_lambdaMinMat_iff_posDef _ hhermitian).mp hlt)

/-! ## The fifteen direction-repeating triples fail, with an explicit witness -/

/-- For two distinct tetrahedron directions, an integer vector orthogonal to both: `±`
their cross product with the factor `2` cleared.  The table is SYMMETRIC in its two
indices, so it is not the cross product itself — that is antisymmetric — and the sign
disagrees with it on half the entries.  Nothing below is sign sensitive.  On the diagonal
the entry is `0`, where the orthogonality lemmas do not apply. -/
def tetraNormalDirection : Fin 4 → Fin 4 → (Fin 3 → ℝ) :=
  ![![![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]],
    ![![0, 1, -1], ![0, 0, 0], ![1, 1, 0], ![1, 0, 1]],
    ![![1, 0, -1], ![1, 1, 0], ![0, 0, 0], ![0, 1, 1]],
    ![![1, -1, 0], ![1, 0, 1], ![0, 1, 1], ![0, 0, 0]]]

/-- The normal of a pair is orthogonal to the first direction. -/
theorem tetraNormalDirection_dot_left {dirLeft dirRight : Fin 4} (hne : dirLeft ≠ dirRight) :
    tetraAtom dirLeft ⬝ᵥ tetraNormalDirection dirLeft dirRight = 0 := by
  fin_cases dirLeft <;> fin_cases dirRight <;>
    simp_all [tetraAtom, tetraNormalDirection, dotProduct, Fin.sum_univ_three]

/-- The normal of a pair is orthogonal to the second direction. -/
theorem tetraNormalDirection_dot_right {dirLeft dirRight : Fin 4} (hne : dirLeft ≠ dirRight) :
    tetraAtom dirRight ⬝ᵥ tetraNormalDirection dirLeft dirRight = 0 := by
  fin_cases dirLeft <;> fin_cases dirRight <;>
    simp_all [tetraAtom, tetraNormalDirection, dotProduct, Fin.sum_univ_three]

/-- The normal of a pair has squared norm `2`. -/
theorem tetraNormalDirection_dot_self {dirLeft dirRight : Fin 4} (hne : dirLeft ≠ dirRight) :
    tetraNormalDirection dirLeft dirRight ⬝ᵥ tetraNormalDirection dirLeft dirRight = 2 := by
  fin_cases dirLeft <;> fin_cases dirRight <;>
    simp_all [tetraNormalDirection, dotProduct, Fin.sum_univ_three] <;> norm_num

/-- Three distinct atoms of the split tetrahedron that repeat a direction carry at
most TWO tetrahedron directions — the split multiplicities are `(2,2,2,1)`, so no
direction can appear three times. -/
theorem exists_twoDirectionCover_of_repeated {atomOne atomTwo atomThree : Fin 7}
    (hOneTwo : atomOne ≠ atomTwo) (hOneThree : atomOne ≠ atomThree)
    (hTwoThree : atomTwo ≠ atomThree)
    (hrepeat : splitSevenDirection atomOne = splitSevenDirection atomTwo
      ∨ splitSevenDirection atomOne = splitSevenDirection atomThree
      ∨ splitSevenDirection atomTwo = splitSevenDirection atomThree) :
    ∃ dirLeft dirRight : Fin 4, dirLeft ≠ dirRight
      ∧ (splitSevenDirection atomOne = dirLeft ∨ splitSevenDirection atomOne = dirRight)
      ∧ (splitSevenDirection atomTwo = dirLeft ∨ splitSevenDirection atomTwo = dirRight)
      ∧ (splitSevenDirection atomThree = dirLeft
          ∨ splitSevenDirection atomThree = dirRight) := by
  revert hOneTwo hOneThree hTwoThree hrepeat
  revert atomOne atomTwo atomThree
  decide

/-- **The explicit failing direction of a direction-repeating triple.**  Its three
atoms span at most two tetrahedron directions, so the normal of that pair is in the
kernel of the atom sum and the gap form there is `−|n|² = −2`: the triple fails
robustly, with Rayleigh quotient exactly `−1`. -/
theorem splitSevenDesign_twoDirection_gapForm_negative {atomOne atomTwo atomThree : Fin 7}
    {dirLeft dirRight : Fin 4} (hne : dirLeft ≠ dirRight)
    (hOne : splitSevenDirection atomOne = dirLeft ∨ splitSevenDirection atomOne = dirRight)
    (hTwo : splitSevenDirection atomTwo = dirLeft ∨ splitSevenDirection atomTwo = dirRight)
    (hThree : splitSevenDirection atomThree = dirLeft
      ∨ splitSevenDirection atomThree = dirRight)
    (hOneTwo : atomOne ≠ atomTwo) (hOneThree : atomOne ≠ atomThree)
    (hTwoThree : atomTwo ≠ atomThree) :
    tetraNormalDirection dirLeft dirRight ⬝ᵥ
        ((subsetSum splitSevenDesign ({atomOne, atomTwo, atomThree} : Finset (Fin 7)) - 1)
          *ᵥ tetraNormalDirection dirLeft dirRight) = -2 := by
  have hzero : ∀ atomIndex : Fin 7,
      (splitSevenDirection atomIndex = dirLeft ∨ splitSevenDirection atomIndex = dirRight) →
      (splitSevenDesign.atom atomIndex ⬝ᵥ tetraNormalDirection dirLeft dirRight) ^ 2 = 0 := by
    intro atomIndex hcase
    rw [splitSevenDesign_atom]
    rcases hcase with hleft | hright
    · rw [hleft, tetraNormalDirection_dot_left hne]; norm_num
    · rw [hright, tetraNormalDirection_dot_right hne]; norm_num
  rw [dominationGap_form, Finset.sum_insert (by simp [hOneTwo, hOneThree]),
    Finset.sum_insert (by simp [hTwoThree]), Finset.sum_singleton,
    hzero atomOne hOne, hzero atomTwo hTwo, hzero atomThree hThree,
    tetraNormalDirection_dot_self hne]
  norm_num

/-- **A direction-repeating triple does not dominate** — proved from the explicit
negative direction, with no discriminant system and no eigenvalue anywhere.  This is a
REPROOF of `Gtz.splitSevenDesign_not_dominates_of_repeatedDirection`; the name is kept
deliberately far from it so citations cannot drift between the two. -/
theorem splitSevenDesign_repeatedDirection_fails_at_pairNormal
    {atomOne atomTwo atomThree : Fin 7}
    (hOneTwo : atomOne ≠ atomTwo) (hOneThree : atomOne ≠ atomThree)
    (hTwoThree : atomTwo ≠ atomThree)
    (hrepeat : splitSevenDirection atomOne = splitSevenDirection atomTwo
      ∨ splitSevenDirection atomOne = splitSevenDirection atomThree
      ∨ splitSevenDirection atomTwo = splitSevenDirection atomThree) :
    ¬ Dominates splitSevenDesign ({atomOne, atomTwo, atomThree} : Finset (Fin 7)) := by
  intro hdominates
  obtain ⟨dirLeft, dirRight, hne, hOne, hTwo, hThree⟩ :=
    exists_twoDirectionCover_of_repeated hOneTwo hOneThree hTwoThree hrepeat
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2
    (tetraNormalDirection dirLeft dirRight)
  rw [star_trivial, splitSevenDesign_twoDirection_gapForm_negative hne hOne hTwo hThree
    hOneTwo hOneThree hTwoThree] at hnonneg
  linarith

/-! ## Velocities: the first-order terms, as exact polynomial coefficients

Nothing below differentiates anything.  A design's atoms enter the gap form
QUADRATICALLY and the trace identity CUBICALLY, so moving along the ray
`atom + step • velocity` produces a polynomial in `step` whose coefficients are
exact.  `gapFormVelocity` and `parsevalTraceVelocity` are those `step`-linear
coefficients, and `gapForm_ray_expansion` / `traceIdentity_ray_expansion` are the
identities that make the word "first-order" a theorem rather than a reading. -/

variable {m k : ℕ}

/-- The `step`-linear coefficient of a subset's gap quadratic form at a fixed probe,
as the atoms move along `atom + step • velocity`. -/
def gapFormVelocity (design : WeightedDesign m k) (atomVelocity : Fin m → Fin k → ℝ)
    (selected : Finset (Fin m)) (probe : Fin k → ℝ) : ℝ :=
  2 * ∑ atomIndex ∈ selected,
    (design.atom atomIndex ⬝ᵥ probe) * (atomVelocity atomIndex ⬝ᵥ probe)

/-- **The gap form along a ray is an exact quadratic in the step**, with linear
coefficient `gapFormVelocity` and a NONNEGATIVE quadratic coefficient. -/
theorem gapForm_ray_expansion (design : WeightedDesign m k)
    (atomVelocity : Fin m → Fin k → ℝ) (selected : Finset (Fin m)) (probe : Fin k → ℝ)
    (step : ℝ) :
    (∑ atomIndex ∈ selected,
        ((design.atom atomIndex + step • atomVelocity atomIndex) ⬝ᵥ probe) ^ 2)
        - probe ⬝ᵥ probe
      = ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)
        + step * gapFormVelocity design atomVelocity selected probe
        + step ^ 2 * ∑ atomIndex ∈ selected, (atomVelocity atomIndex ⬝ᵥ probe) ^ 2 := by
  have hterm : ∀ atomIndex ∈ selected,
      ((design.atom atomIndex + step • atomVelocity atomIndex) ⬝ᵥ probe) ^ 2
        = (design.atom atomIndex ⬝ᵥ probe) ^ 2
          + step * (2 * ((design.atom atomIndex ⬝ᵥ probe)
              * (atomVelocity atomIndex ⬝ᵥ probe)))
          + step ^ 2 * (atomVelocity atomIndex ⬝ᵥ probe) ^ 2 := by
    intro atomIndex _
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm, gapFormVelocity, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The atom sum of a subset as its atoms move along `atom + step • velocity`.  This is
NOT a design: the ray leaves the Parseval manifold at second order, and every statement
about it below is a statement about a matrix. -/
def rayAtomSum (design : WeightedDesign m k) (atomVelocity : Fin m → Fin k → ℝ)
    (selected : Finset (Fin m)) (step : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  ∑ atomIndex ∈ selected, atomMatrix (design.atom atomIndex + step • atomVelocity atomIndex)

/-- The gap quadratic form of a ray atom sum, as a sum of squared projections. -/
theorem rayAtomSum_gap_form (design : WeightedDesign m k)
    (atomVelocity : Fin m → Fin k → ℝ) (selected : Finset (Fin m)) (step : ℝ)
    (probe : Fin k → ℝ) :
    probe ⬝ᵥ ((rayAtomSum design atomVelocity selected step - 1) *ᵥ probe)
      = (∑ atomIndex ∈ selected,
            ((design.atom atomIndex + step • atomVelocity atomIndex) ⬝ᵥ probe) ^ 2)
        - probe ⬝ᵥ probe := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, rayAtomSum,
    Matrix.sum_mulVec, dotProduct_sum]
  exact congrArg (· - probe ⬝ᵥ probe)
    (Finset.sum_congr rfl fun atomIndex _ => atom_form_eq_sq _ _)

/-- The leverage along a ray is an exact quadratic in the step. -/
theorem leverageOf_ray (base direction : Fin k → ℝ) (step : ℝ) :
    leverageOf (base + step • direction)
      = leverageOf base + step * (2 * (base ⬝ᵥ direction)) + step ^ 2 * leverageOf direction := by
  simp only [leverageOf, ← dotProduct_self_eq_sum_sq, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm direction base]
  ring

/-- The `step`-linear coefficient of the trace identity `∑_c t_c |g_c|² = k` as the
design moves along `(weight + step * weightVelocity, atom + step • atomVelocity)`. -/
def parsevalTraceVelocity (design : WeightedDesign m k)
    (atomVelocity : Fin m → Fin k → ℝ) (weightVelocity : Fin m → ℝ) : ℝ :=
  ∑ atomIndex, (weightVelocity atomIndex * leverageOf (design.atom atomIndex)
    + 2 * (design.weight atomIndex * (design.atom atomIndex ⬝ᵥ atomVelocity atomIndex)))

/-- **The trace identity along a ray is an exact cubic in the step**, with constant
term the rank `k` and linear coefficient `parsevalTraceVelocity`.  Any curve of
DESIGNS through `design` has all four coefficients determined; the first-order
tangency condition is that the linear one vanishes. -/
theorem traceIdentity_ray_expansion (design : WeightedDesign m k)
    (atomVelocity : Fin m → Fin k → ℝ) (weightVelocity : Fin m → ℝ) (step : ℝ) :
    (∑ atomIndex, (design.weight atomIndex + step * weightVelocity atomIndex)
        * leverageOf (design.atom atomIndex + step • atomVelocity atomIndex))
      = (k : ℝ) + step * parsevalTraceVelocity design atomVelocity weightVelocity
        + step ^ 2 * ∑ atomIndex,
            (2 * (weightVelocity atomIndex
                * (design.atom atomIndex ⬝ᵥ atomVelocity atomIndex))
              + design.weight atomIndex * leverageOf (atomVelocity atomIndex))
        + step ^ 3 * ∑ atomIndex,
            weightVelocity atomIndex * leverageOf (atomVelocity atomIndex) := by
  have hterm : ∀ atomIndex ∈ (Finset.univ : Finset (Fin m)),
      (design.weight atomIndex + step * weightVelocity atomIndex)
          * leverageOf (design.atom atomIndex + step • atomVelocity atomIndex)
        = design.weight atomIndex * leverageOf (design.atom atomIndex)
          + step * (weightVelocity atomIndex * leverageOf (design.atom atomIndex)
              + 2 * (design.weight atomIndex
                  * (design.atom atomIndex ⬝ᵥ atomVelocity atomIndex)))
          + step ^ 2 * (2 * (weightVelocity atomIndex
                * (design.atom atomIndex ⬝ᵥ atomVelocity atomIndex))
              + design.weight atomIndex * leverageOf (atomVelocity atomIndex))
          + step ^ 3 * (weightVelocity atomIndex * leverageOf (atomVelocity atomIndex)) := by
    intro atomIndex _
    rw [leverageOf_ray]
    ring
  rw [Finset.sum_congr rfl hterm, parsevalTraceVelocity, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_weight_mul_leverage]

/-! ## The Farkas identity -/

/-- Summing an indicator over the whole index set is summing over the subset. -/
private theorem sum_indicator_eq_sum_subset {Carrier : Type*} [AddCommMonoid Carrier]
    (selected : Finset (Fin 7)) (summand : Fin 7 → Carrier) :
    ∑ atomIndex : Fin 7, (if atomIndex ∈ selected then summand atomIndex else 0)
      = ∑ atomIndex ∈ selected, summand atomIndex := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The pairing of the first tetrahedron direction with a probe. -/
theorem tetraAtom_dotProduct_zero (probe : Fin 3 → ℝ) :
    tetraAtom 0 ⬝ᵥ probe = probe 0 + probe 1 + probe 2 := by
  simp only [tetraAtom, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The pairing of the second tetrahedron direction with a probe. -/
theorem tetraAtom_dotProduct_one (probe : Fin 3 → ℝ) :
    tetraAtom 1 ⬝ᵥ probe = probe 0 - probe 1 - probe 2 := by
  simp only [tetraAtom, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The pairing of the third tetrahedron direction with a probe. -/
theorem tetraAtom_dotProduct_two (probe : Fin 3 → ℝ) :
    tetraAtom 2 ⬝ᵥ probe = -probe 0 + probe 1 - probe 2 := by
  simp only [tetraAtom, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The pairing of the fourth tetrahedron direction with a probe. -/
theorem tetraAtom_dotProduct_three (probe : Fin 3 → ℝ) :
    tetraAtom 3 ⬝ᵥ probe = -probe 0 - probe 1 + probe 2 := by
  simp only [tetraAtom, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons]
  ring

/-- **THE MARGINAL IDENTITY — the arithmetic heart of the certificate.**  For every
atom `c`, the multipliers of the rainbow triples CONTAINING `c`, weighted by their
missed directions, reproduce `−t_c g_c`:

  `∑_{T ∋ c} det(P_T) · v_{miss T} = − t_c · g_c`.

Read it in two steps.  The triples containing `c` and missing a fixed direction
`e ≠ d(c)` carry total multiplier exactly `t_c` — the volume-sampling measure splits
its marginal `P_cc = 3 t_c` evenly over the three admissible missed directions.  And
the four tetrahedron directions sum to zero, so `∑_{e ≠ d(c)} v_e = −v_{d(c)}`.  The
weight reappears on the right because the leverage is exactly `3` at every atom. -/
theorem rainbowSevenMultiplier_marginal (atomIndex : Fin 7) (probe : Fin 3 → ℝ) :
    ∑ tripleIndex : Fin 20,
        (if atomIndex ∈ rainbowSevenTriple tripleIndex then
          rainbowSevenMultiplier tripleIndex
            * (tetraAtom (rainbowSevenMissedDirection tripleIndex) ⬝ᵥ probe)
        else 0)
      = -(splitSevenDesign.weight atomIndex * (splitSevenDesign.atom atomIndex ⬝ᵥ probe)) := by
  fin_cases atomIndex <;>
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, rainbowSevenTriple, rainbowSevenFirst,
      rainbowSevenSecond, rainbowSevenThird, rainbowSevenMissedDirection,
      rainbowSevenMultiplier, splitSevenDesign, splitSevenAtom, splitSevenDirection,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.mem_insert,
      Finset.mem_singleton] <;>
    norm_num +decide <;>
    simp only [tetraAtom_dotProduct_zero, tetraAtom_dotProduct_one,
      tetraAtom_dotProduct_two, tetraAtom_dotProduct_three] <;>
    ring

/-- **THE FARKAS IDENTITY.**  Weighted by the volume-sampling multipliers, the twenty
rainbow tie-form velocities add up to the velocity of the trace identity:

  `∑_T det(P_T) · (gap-form velocity of T at its tie direction) = 2 ∑_c t_c ⟨g_c, dg_c⟩`.

Every step is linear algebra.  Each atom of a rainbow triple pairs to `−1` with the
missed direction, so the triple's velocity collapses to `−2 ∑_{c ∈ T} ⟨v_{miss T}, dg_c⟩`;
exchanging the two sums turns the outer weighting into the per-atom marginal, and
`rainbowSevenMultiplier_marginal` evaluates it to `−t_c g_c`.  The right-hand side is
exactly the `dg`-part of the derivative of `∑_c t_c |g_c|² = 3`. -/
theorem splitSevenDesign_farkasIdentity (atomVelocity : Fin 7 → Fin 3 → ℝ) :
    ∑ tripleIndex : Fin 20, rainbowSevenMultiplier tripleIndex *
        gapFormVelocity splitSevenDesign atomVelocity (rainbowSevenTriple tripleIndex)
          (tetraAtom (rainbowSevenMissedDirection tripleIndex))
      = 2 * ∑ atomIndex, splitSevenDesign.weight atomIndex
          * (splitSevenDesign.atom atomIndex ⬝ᵥ atomVelocity atomIndex) := by
  have hpairing : ∀ (tripleIndex : Fin 20) (atomIndex : Fin 7),
      atomIndex ∈ rainbowSevenTriple tripleIndex →
      splitSevenDesign.atom atomIndex
          ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex) = -1 := by
    intro tripleIndex atomIndex hmem
    rw [splitSevenDesign_atom]
    exact tetraAtom_dot_of_ne (rainbowSevenTriple_direction_ne_missed hmem)
  have hperTriple : ∀ tripleIndex : Fin 20,
      rainbowSevenMultiplier tripleIndex *
          gapFormVelocity splitSevenDesign atomVelocity (rainbowSevenTriple tripleIndex)
            (tetraAtom (rainbowSevenMissedDirection tripleIndex))
        = ∑ atomIndex : Fin 7, (if atomIndex ∈ rainbowSevenTriple tripleIndex then
            (-2 : ℝ) * (rainbowSevenMultiplier tripleIndex
              * (tetraAtom (rainbowSevenMissedDirection tripleIndex)
                  ⬝ᵥ atomVelocity atomIndex)) else 0) := by
    intro tripleIndex
    rw [sum_indicator_eq_sum_subset, gapFormVelocity, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun atomIndex hmem => ?_
    rw [hpairing tripleIndex atomIndex hmem, dotProduct_comm (atomVelocity atomIndex)]
    ring
  have hperAtom : ∀ atomIndex : Fin 7,
      ∑ tripleIndex : Fin 20, (if atomIndex ∈ rainbowSevenTriple tripleIndex then
          (-2 : ℝ) * (rainbowSevenMultiplier tripleIndex
            * (tetraAtom (rainbowSevenMissedDirection tripleIndex)
                ⬝ᵥ atomVelocity atomIndex)) else 0)
        = 2 * (splitSevenDesign.weight atomIndex
            * (splitSevenDesign.atom atomIndex ⬝ᵥ atomVelocity atomIndex)) := by
    intro atomIndex
    have hpull : ∑ tripleIndex : Fin 20,
          (if atomIndex ∈ rainbowSevenTriple tripleIndex then
            (-2 : ℝ) * (rainbowSevenMultiplier tripleIndex
              * (tetraAtom (rainbowSevenMissedDirection tripleIndex)
                  ⬝ᵥ atomVelocity atomIndex)) else 0)
        = (-2 : ℝ) * ∑ tripleIndex : Fin 20,
            (if atomIndex ∈ rainbowSevenTriple tripleIndex then
              rainbowSevenMultiplier tripleIndex
                * (tetraAtom (rainbowSevenMissedDirection tripleIndex)
                    ⬝ᵥ atomVelocity atomIndex) else 0) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun tripleIndex _ => by
        by_cases hcase : atomIndex ∈ rainbowSevenTriple tripleIndex <;> simp [hcase]
    rw [hpull, rainbowSevenMultiplier_marginal]
    ring
  simp_rw [hperTriple]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun atomIndex _ => hperAtom atomIndex

/-- **The tangent conditions kill the right-hand side.**  Every leverage of the split
tetrahedron is exactly `3`, so a traceless weight velocity leaves the trace-identity
velocity equal to `2 ∑_c t_c ⟨g_c, dg_c⟩`; requiring it to vanish forces that pairing
to vanish. -/
theorem splitSevenDesign_velocityPairing_zero (atomVelocity : Fin 7 → Fin 3 → ℝ)
    (weightVelocity : Fin 7 → ℝ) (hmass : ∑ atomIndex, weightVelocity atomIndex = 0)
    (htrace : parsevalTraceVelocity splitSevenDesign atomVelocity weightVelocity = 0) :
    ∑ atomIndex, splitSevenDesign.weight atomIndex
        * (splitSevenDesign.atom atomIndex ⬝ᵥ atomVelocity atomIndex) = 0 := by
  have hterm : ∀ atomIndex : Fin 7,
      weightVelocity atomIndex * leverageOf (splitSevenDesign.atom atomIndex)
          + 2 * (splitSevenDesign.weight atomIndex
              * (splitSevenDesign.atom atomIndex ⬝ᵥ atomVelocity atomIndex))
        = 3 * weightVelocity atomIndex
          + 2 * (splitSevenDesign.weight atomIndex
              * (splitSevenDesign.atom atomIndex ⬝ᵥ atomVelocity atomIndex)) := by
    intro atomIndex
    rw [splitSevenDesign_leverage]
    ring
  rw [parsevalTraceVelocity, Finset.sum_congr rfl (fun atomIndex _ => hterm atomIndex),
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hmass] at htrace
  linarith

/-- **The certificate fires: the weighted sum of the twenty tie-form velocities is
ZERO along every admissible tangent direction.** -/
theorem splitSevenDesign_farkasIdentity_zero (atomVelocity : Fin 7 → Fin 3 → ℝ)
    (weightVelocity : Fin 7 → ℝ) (hmass : ∑ atomIndex, weightVelocity atomIndex = 0)
    (htrace : parsevalTraceVelocity splitSevenDesign atomVelocity weightVelocity = 0) :
    ∑ tripleIndex : Fin 20, rainbowSevenMultiplier tripleIndex *
        gapFormVelocity splitSevenDesign atomVelocity (rainbowSevenTriple tripleIndex)
          (tetraAtom (rainbowSevenMissedDirection tripleIndex)) = 0 := by
  rw [splitSevenDesign_farkasIdentity,
    splitSevenDesign_velocityPairing_zero atomVelocity weightVelocity hmass htrace]
  ring

/-! ## No first-order descent -/

/-- **NO ADMISSIBLE DIRECTION LOWERS ALL TWENTY TIE FORMS.**  Twenty strictly positive
multipliers summing a quantity to zero cannot have every summand negative — the Gordan
alternative, instantiated by the explicit certificate rather than invoked abstractly. -/
theorem rainbowSeven_exists_nonnegative_velocity (atomVelocity : Fin 7 → Fin 3 → ℝ)
    (weightVelocity : Fin 7 → ℝ) (hmass : ∑ atomIndex, weightVelocity atomIndex = 0)
    (htrace : parsevalTraceVelocity splitSevenDesign atomVelocity weightVelocity = 0) :
    ∃ tripleIndex : Fin 20, 0 ≤ gapFormVelocity splitSevenDesign atomVelocity
      (rainbowSevenTriple tripleIndex)
      (tetraAtom (rainbowSevenMissedDirection tripleIndex)) := by
  by_contra hnone
  push Not at hnone
  have hstrict : ∑ tripleIndex : Fin 20, rainbowSevenMultiplier tripleIndex *
      gapFormVelocity splitSevenDesign atomVelocity (rainbowSevenTriple tripleIndex)
        (tetraAtom (rainbowSevenMissedDirection tripleIndex))
      < ∑ _tripleIndex : Fin 20, (0 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ fun tripleIndex _ =>
      mul_neg_of_pos_of_neg (rainbowSevenMultiplier_pos tripleIndex) (hnone tripleIndex)
  rw [Finset.sum_const_zero,
    splitSevenDesign_farkasIdentity_zero atomVelocity weightVelocity hmass htrace] at hstrict
  exact lt_irrefl 0 hstrict

/-- **THE STRICT READING.**  Because every multiplier is strictly positive, the
certificate says more than "not all negative": along any admissible direction that moves
ANY tie form at all, some rainbow triple's tie FORM moves strictly UP.

That is a statement about the form at the frozen probe `v_{miss T}` and nothing more.  It
does NOT say that triple survives the perturbation, still less that it becomes a strict
dominator — the bottom eigenvector moves too, and `stratumCriticalRay_not_posSemidef`
below exhibits a critical velocity whose frozen form rises while its triple dies. -/
theorem rainbowSeven_exists_positive_velocity (atomVelocity : Fin 7 → Fin 3 → ℝ)
    (weightVelocity : Fin 7 → ℝ) (hmass : ∑ atomIndex, weightVelocity atomIndex = 0)
    (htrace : parsevalTraceVelocity splitSevenDesign atomVelocity weightVelocity = 0)
    (hmoves : ∃ movedIndex : Fin 20, gapFormVelocity splitSevenDesign atomVelocity
      (rainbowSevenTriple movedIndex)
      (tetraAtom (rainbowSevenMissedDirection movedIndex)) ≠ 0) :
    ∃ tripleIndex : Fin 20, 0 < gapFormVelocity splitSevenDesign atomVelocity
      (rainbowSevenTriple tripleIndex)
      (tetraAtom (rainbowSevenMissedDirection tripleIndex)) := by
  obtain ⟨movedIndex, hmoved⟩ := hmoves
  by_contra hnone
  push Not at hnone
  have hstrict : ∑ tripleIndex : Fin 20, rainbowSevenMultiplier tripleIndex *
      gapFormVelocity splitSevenDesign atomVelocity (rainbowSevenTriple tripleIndex)
        (tetraAtom (rainbowSevenMissedDirection tripleIndex))
      < ∑ _tripleIndex : Fin 20, (0 : ℝ) := by
    refine Finset.sum_lt_sum (fun tripleIndex _ => ?_) ⟨movedIndex, Finset.mem_univ movedIndex, ?_⟩
    · exact mul_nonpos_of_nonneg_of_nonpos (rainbowSevenMultiplier_pos tripleIndex).le
        (hnone tripleIndex)
    · exact mul_neg_of_pos_of_neg (rainbowSevenMultiplier_pos movedIndex)
        (lt_of_le_of_ne (hnone movedIndex) hmoved)
  rw [Finset.sum_const_zero,
    splitSevenDesign_farkasIdentity_zero atomVelocity weightVelocity hmass htrace] at hstrict
  exact lt_irrefl 0 hstrict

/-! ## From velocities to domination: the one safe direction

`gapFormVelocity` moves a FORM at a frozen probe, and the bridge to `Dominates` runs in
exactly one direction.  A negative form at any fixed probe already breaks positive
semidefiniteness, so a strictly negative tie-form velocity really destroys its triple for
all small positive steps — no eigenvector control needed.  Combined with
`rainbowSeven_exists_nonnegative_velocity` this is what the certificate buys: the
elementary route to a nearby counterexample, pushing all twenty tie forms down at once,
is closed.  The converse direction is false; the next section exhibits the failure. -/

/-- **The exact ray expansion of a tie form at its own tie direction.**  The constant term
is `0` because the triple is tied, so the whole form is `step · velocity + step² · (sum of
squares)` — an exact polynomial identity, no remainder. -/
theorem rainbowSevenTriple_rayGapForm_missedDirection (tripleIndex : Fin 20)
    (atomVelocity : Fin 7 → Fin 3 → ℝ) (step : ℝ) :
    tetraAtom (rainbowSevenMissedDirection tripleIndex)
        ⬝ᵥ ((rayAtomSum splitSevenDesign atomVelocity (rainbowSevenTriple tripleIndex) step
              - 1) *ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex))
      = step * gapFormVelocity splitSevenDesign atomVelocity (rainbowSevenTriple tripleIndex)
            (tetraAtom (rainbowSevenMissedDirection tripleIndex))
        + step ^ 2 * ∑ atomIndex ∈ rainbowSevenTriple tripleIndex,
            (atomVelocity atomIndex
              ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex)) ^ 2 := by
  have hbase : (∑ atomIndex ∈ rainbowSevenTriple tripleIndex,
        (splitSevenDesign.atom atomIndex
          ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex)) ^ 2)
      - tetraAtom (rainbowSevenMissedDirection tripleIndex)
        ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex) = 0 := by
    rw [← dominationGap_form]
    exact rainbowSevenTriple_gapForm_missedDirection tripleIndex
  rw [rayAtomSum_gap_form, gapForm_ray_expansion, hbase, zero_add]

/-- **A strictly negative tie-form velocity really destroys its triple.**  For every step
below an explicit positive bound the perturbed gap is not positive semidefinite, witnessed
at the frozen tie direction itself.  This is the honest content of "no first-order
descent": the certificate forbids all twenty velocities from being negative, and each
negative velocity would genuinely kill its triple. -/
theorem rainbowSevenTriple_ray_not_posSemidef_of_velocity_neg (tripleIndex : Fin 20)
    (atomVelocity : Fin 7 → Fin 3 → ℝ)
    (hvelocityNeg : gapFormVelocity splitSevenDesign atomVelocity
      (rainbowSevenTriple tripleIndex)
      (tetraAtom (rainbowSevenMissedDirection tripleIndex)) < 0) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ step : ℝ, 0 < step → step < bound →
      ¬ (rayAtomSum splitSevenDesign atomVelocity (rainbowSevenTriple tripleIndex) step
          - 1).PosSemidef := by
  set velocity := gapFormVelocity splitSevenDesign atomVelocity
    (rainbowSevenTriple tripleIndex)
    (tetraAtom (rainbowSevenMissedDirection tripleIndex)) with hvelocity
  set quadratic := ∑ atomIndex ∈ rainbowSevenTriple tripleIndex,
    (atomVelocity atomIndex ⬝ᵥ tetraAtom (rainbowSevenMissedDirection tripleIndex)) ^ 2
    with hquadratic
  have hquadNonneg : 0 ≤ quadratic := Finset.sum_nonneg fun atomIndex _ => sq_nonneg _
  refine ⟨-velocity / (quadratic + 1), div_pos (by linarith) (by linarith),
    fun step hstepPos hstepSmall => ?_⟩
  intro hposSemidef
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hposSemidef).2
    (tetraAtom (rainbowSevenMissedDirection tripleIndex))
  rw [star_trivial, rainbowSevenTriple_rayGapForm_missedDirection, ← hvelocity,
    ← hquadratic] at hform
  have hboundQuad : (-velocity / (quadratic + 1)) * quadratic < -velocity := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  have hstepQuad : step * quadratic ≤ (-velocity / (quadratic + 1)) * quadratic :=
    mul_le_mul_of_nonneg_right hstepSmall.le hquadNonneg
  nlinarith

/-! ## The frozen-form second order is NOT rigidity — an exact counterexample

A previous draft of this file shipped a theorem saying that on the critical cone the gap
form AT THE FROZEN TIE DIRECTION moves strictly up at order two, its quadratic coefficient
being a sum of squares.  True, and worthless: that coefficient is the leading term of a
difference whose second term it never bounds, so it says nothing about the smallest
eigenvalue.  The theorem is gone and this is what stands in its place.

The velocity below has zero mass velocity and zero Parseval-trace velocity, is CRITICAL
for triple `0`, and has frozen-form second-order coefficient exactly `2 > 0` — the deleted
theorem's own conclusion.  Its perturbed gap nevertheless has determinant `−2 · step²`,
so the triple stops dominating at every nonzero step.  The frozen form rises; the margin
goes negative.

The velocity is a genuine tangent direction and not an artifact of weak hypotheses: with
that weight velocity it annihilates the FULL matrix Parseval velocity
`∑_c (dt_c g_c g_cᵀ + t_c (dg_c g_cᵀ + g_c dg_cᵀ))`, not merely its trace.  That last check
is exact rational arithmetic done BY HAND and is not mechanized; the theorems here need
only the trace, which is proved. -/

/-- The critical atom velocity of the counterexample: `dg_0 = e_0`, `dg_1 = −e_0`, and the
other five atoms frozen. -/
def stratumCriticalAtomVelocity : Fin 7 → Fin 3 → ℝ :=
  ![![1, 0, 0], ![-1, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]

/-- The weight velocity that makes `stratumCriticalAtomVelocity` tangent: `dt_0 = −1/8`,
`dt_1 = 1/8`, the rest frozen. -/
noncomputable def stratumCriticalWeightVelocity : Fin 7 → ℝ := ![-(1/8), 1/8, 0, 0, 0, 0, 0]

/-- The counterexample velocity keeps total mass fixed. -/
theorem stratumCriticalVelocity_mass_zero :
    ∑ atomIndex, stratumCriticalWeightVelocity atomIndex = 0 := by
  simp only [Fin.sum_univ_seven, stratumCriticalWeightVelocity, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
  norm_num

/-- The counterexample velocity is tangent to the trace identity. -/
theorem stratumCriticalVelocity_parsevalTrace_zero :
    parsevalTraceVelocity splitSevenDesign stratumCriticalAtomVelocity
      stratumCriticalWeightVelocity = 0 := by
  simp only [parsevalTraceVelocity, Fin.sum_univ_seven, splitSevenDesign_atom,
    splitSevenDesign_weight_apply, stratumCriticalAtomVelocity, stratumCriticalWeightVelocity,
    splitSevenDirection, tetraAtom, leverageOf, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
  norm_num +decide

/-- **The counterexample velocity is on the critical cone of triple `0`** — its
first-order tie-form term vanishes, so the whole first-order package is silent about it. -/
theorem stratumCriticalVelocity_gapFormVelocity_zero :
    gapFormVelocity splitSevenDesign stratumCriticalAtomVelocity (rainbowSevenTriple 0)
      (tetraAtom (rainbowSevenMissedDirection 0)) = 0 := by
  rw [gapFormVelocity, sum_rainbowSevenTriple]
  simp only [rainbowSevenFirst, rainbowSevenSecond, rainbowSevenThird,
    rainbowSevenMissedDirection, splitSevenDesign_atom, splitSevenDirection,
    stratumCriticalAtomVelocity, tetraAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons]
  norm_num

/-- **The deleted theorem's conclusion holds at this velocity**: the frozen-form
second-order coefficient of triple `0` is the strictly positive sum of squares `2`. -/
theorem stratumCriticalVelocity_frozenQuadratic_eq_two :
    (∑ atomIndex ∈ rainbowSevenTriple 0,
      (stratumCriticalAtomVelocity atomIndex
        ⬝ᵥ tetraAtom (rainbowSevenMissedDirection 0)) ^ 2) = 2 := by
  rw [sum_rainbowSevenTriple]
  simp only [rainbowSevenFirst, rainbowSevenSecond, rainbowSevenThird,
    rainbowSevenMissedDirection, stratumCriticalAtomVelocity, tetraAtom, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  norm_num

/-- The perturbed gap of triple `0` in closed form, exactly rational in the step. -/
theorem stratumCriticalRay_gap_eq (step : ℝ) :
    rayAtomSum splitSevenDesign stratumCriticalAtomVelocity (rainbowSevenTriple 0) step - 1
      = !![2 + 2 * step ^ 2, 2 * step - 1, 2 * step + 1;
           2 * step - 1, 2, 1;
           2 * step + 1, 1, 2] := by
  rw [rayAtomSum, sum_rainbowSevenTriple]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, atomMatrix,
      Matrix.vecMulVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      rainbowSevenFirst, rainbowSevenSecond, rainbowSevenThird, splitSevenDesign_atom,
      splitSevenDirection, stratumCriticalAtomVelocity, tetraAtom, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    norm_num <;> ring

/-- **The determinant of the perturbed gap is `−2 · step²`.**  Negative at every nonzero
step, however small. -/
theorem stratumCriticalRay_gap_det (step : ℝ) :
    (rayAtomSum splitSevenDesign stratumCriticalAtomVelocity (rainbowSevenTriple 0) step
        - 1).det = -2 * step ^ 2 := by
  rw [stratumCriticalRay_gap_eq, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- **THE COUNTEREXAMPLE.**  A critical velocity whose frozen tie form rises at order two
— coefficient exactly `2`, by `stratumCriticalVelocity_frozenQuadratic_eq_two` — and whose
triple stops dominating at every nonzero step.  A positive semidefinite matrix has
nonnegative determinant; this one has determinant `−2 · step²`.

So the frozen-form second-order sign is NOT evidence of second-order rigidity, and no
statement of that shape belongs in this file. -/
theorem stratumCriticalRay_not_posSemidef {step : ℝ} (hstep : step ≠ 0) :
    ¬ (rayAtomSum splitSevenDesign stratumCriticalAtomVelocity (rainbowSevenTriple 0) step
        - 1).PosSemidef := by
  intro hposSemidef
  have hdetNonneg := hposSemidef.det_nonneg
  rw [stratumCriticalRay_gap_det] at hdetNonneg
  have hstepSquare : 0 < step ^ 2 :=
    lt_of_le_of_ne (sq_nonneg step) (Ne.symm (pow_ne_zero 2 hstep))
  linarith

/-! ## The multipliers coincide with the volume-sampling measure HERE

Nothing above needed to know where the numbers `1/32` and `1/16` come from.  At THIS
design they are the principal minors `det(P_T)` of the projection form — the
volume-sampling probability of `T` — and this section proves that identity, through the
unshifted sibling of `Gtz.projectionBlock_sub_weightDiagonal`.

The identity does not travel.  Symmetry plus total mass one already pins the symmetric
certificate here, so `det(P_T)` is coinciding with the only numbers available rather than
predicting them; and at neighbouring rational designs on the same tie stratum the
determinantal measure is not a certificate at all.  [MEASURED; module header.] -/

/-- The unshifted positive-diagonal congruence: a principal block of the projection
form is the selected Gram conjugated by `diag √t`. -/
theorem projectionBlock_eq_congruence (design : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) :
    (projectionOfDesign design).submatrix pick pick
      = (sqrtWeightDiagonal design pick)ᵀ
          * (selectedAtomRows design pick * (selectedAtomRows design pick)ᵀ)
          * sqrtWeightDiagonal design pick := by
  rw [sqrtWeightDiagonal, Matrix.diagonal_transpose]
  ext leftIndex rightIndex
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply,
    selectedAtomRows, Matrix.of_apply]
  rw [projectionOfDesign_apply, dotProduct]
  ring

/-- **The principal minors of the projection form rescale the selected Gram
determinants** — the unshifted companion of `det_projectionBlock_sub_weightDiagonal`. -/
theorem det_projectionBlock_of_design (design : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) :
    ((projectionOfDesign design).submatrix pick pick).det
      = (∏ selectedIndex, design.weight (pick selectedIndex))
        * (selectedAtomRows design pick * (selectedAtomRows design pick)ᵀ).det := by
  rw [projectionBlock_eq_congruence, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    sqrtWeightDiagonal, Matrix.det_diagonal]
  have hsquare : (∏ selectedIndex, Real.sqrt (design.weight (pick selectedIndex)))
        * (∏ selectedIndex, Real.sqrt (design.weight (pick selectedIndex)))
      = ∏ selectedIndex, design.weight (pick selectedIndex) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun selectedIndex _ =>
      Real.mul_self_sqrt (design.weight_pos (pick selectedIndex)).le
  rw [← hsquare]
  ring

/-- The determinant of a rainbow triple's gap-free atom sum: `det(4·I − v_d v_dᵀ) = 16`,
the product of the spectrum `{1, 4, 4}`. -/
theorem det_four_smul_one_sub_atomMatrix_tetraAtom (dir : Fin 4) :
    ((4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (tetraAtom dir)).det = 16 := by
  fin_cases dir <;>
    norm_num +decide [Matrix.det_fin_three, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, atomMatrix, Matrix.vecMulVec_apply, tetraAtom, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- The selection map of the `i`-th rainbow triple, as a function out of `Fin 3`. -/
def rainbowSevenPick (tripleIndex : Fin 20) : Fin 3 → Fin 7 :=
  ![rainbowSevenFirst tripleIndex, rainbowSevenSecond tripleIndex,
    rainbowSevenThird tripleIndex]

/-- The selected-row matrix of a rainbow triple squares to its atom sum. -/
theorem transpose_mul_selectedAtomRows_rainbow (tripleIndex : Fin 20) :
    (selectedAtomRows splitSevenDesign (rainbowSevenPick tripleIndex))ᵀ
        * selectedAtomRows splitSevenDesign (rainbowSevenPick tripleIndex)
      = subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex) := by
  rw [transpose_mul_self_eq_sum_rows, subsetSum, sum_rainbowSevenTriple,
    Fin.sum_univ_three]
  rfl

/-- Every rainbow triple's atom sum has determinant `16`. -/
theorem splitSevenDesign_rainbowGram_det (tripleIndex : Fin 20) :
    (subsetSum splitSevenDesign (rainbowSevenTriple tripleIndex)).det = 16 := by
  rw [splitSevenDesign_subsetSum_rainbow, det_four_smul_one_sub_atomMatrix_tetraAtom]

/-- **AT THIS DESIGN THE MULTIPLIERS ARE THE VOLUME-SAMPLING PROBABILITIES.**  `λ_T`
equals the principal minor `det(P_T)` of the projection form, whose total mass is `1`
(`sum_det_projectionMinors_rank`) and whose marginals (`projectionOfDesign_diagonal`) are
the leverage scores.

Do not read this as the mechanism behind the certificate.  Once the mass is fixed, the
symmetric certificate here is unique, so ANY symmetric candidate would have to be this
vector; and off this point the identification fails outright — at other rational designs
on the same tie stratum, and at this design with an uneven split, `∑_T det(P_T) · grad_T`
is a nonzero rational vector.  [Both MEASURED outside Lean; module header.] -/
theorem rainbowSevenMultiplier_eq_det_projectionBlock (tripleIndex : Fin 20) :
    rainbowSevenMultiplier tripleIndex
      = ((projectionOfDesign splitSevenDesign).submatrix (rainbowSevenPick tripleIndex)
          (rainbowSevenPick tripleIndex)).det := by
  rw [det_projectionBlock_of_design, Matrix.det_mul_comm,
    transpose_mul_selectedAtomRows_rainbow, splitSevenDesign_rainbowGram_det,
    Fin.prod_univ_three]
  fin_cases tripleIndex <;>
    norm_num +decide [rainbowSevenMultiplier, rainbowSevenPick, rainbowSevenFirst,
      rainbowSevenSecond, rainbowSevenThird, splitSevenDesign_weight_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
      Matrix.cons_val_two, Matrix.tail_cons]

/-! ## What the certificate leaves open -/

/-- **THE NAMED RESIDUAL: local minimality at the split tetrahedron.**  Every design in
a sup-norm neighbourhood of the split tetrahedron has a dominating triple.

This is what the first-order package does NOT establish and is not claimed to.  What is
proved above is exactly three things: no admissible velocity lowers all twenty tie FORMS;
a strictly negative form velocity really destroys its triple
(`rainbowSevenTriple_ray_not_posSemidef_of_velocity_neg`); and a critical velocity whose
frozen form RISES can destroy its triple anyway (`stratumCriticalRay_not_posSemidef`).

Two things stand between that and the residual, and neither is what an earlier draft
named.  Eigenvalue control is NOT the obstacle: the repo already has it — `lambdaMinMat`,
`dominates_iff_one_le_lambdaMinMat`, `lipschitzWith_lambdaMinCLM` — and
`rainbowSevenTriple_lambdaMinMat_eq_one` uses it here.  What is missing is (i) EIGENVECTOR
perturbation, since every gap has a simple bottom eigenvalue whose eigenvector moves, and
(ii) a radius uniform over the critical cone — which is the tie stratum described in the
module header, the corank-one Naimark stratum pulled back along the split, hence a whole
positive-dimensional plateau and not one direction at a time. -/
def SplitSevenNeighbourhoodCovering : Prop :=
  ∃ radius : ℝ, 0 < radius ∧
    ∀ design : WeightedDesign 7 3,
      (∀ atomIndex coord, |design.atom atomIndex coord
          - splitSevenDesign.atom atomIndex coord| < radius) →
      (∀ atomIndex, |design.weight atomIndex - splitSevenDesign.weight atomIndex| < radius) →
      ∃ selected : Finset (Fin 7), selected.card = 3 ∧ Dominates design selected

/-- The residual is a CONSEQUENCE of the conjecture, hence a necessary sub-goal and not
an independent gamble: `GtzWeighted 7 3` gives it with any radius at all. -/
theorem splitSevenNeighbourhoodCovering_of_gtzWeighted (hcovering : GtzWeighted 7 3) :
    SplitSevenNeighbourhoodCovering :=
  ⟨1, one_pos, fun design _ _ => hcovering design⟩

end Gtz

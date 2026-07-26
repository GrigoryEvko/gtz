/-
# Primitive tight rank-three designs: the bracket stratum vocabulary, the Fano
# emptiness, and the hinge from a per-matroid ledger

The campaign's one nature-facing gap is the HINGE: every exact tie at `(6,3)` and
`(7,3)` carries two parallel atoms.  A tie with NO parallel pair is *primitive*,
its `m` directions are pairwise non-parallel, and Parseval makes them span `ℝ³`
(`Gtz.eq_zero_of_forall_atom_dot_eq_zero`), so its direction matroid is a SIMPLE
rank-three matroid on `m` elements.  The hinge is therefore equivalent to a
finite ledger of per-matroid emptiness statements — nine isomorphism classes at
`m = 6`, twenty-three at `m = 7`.

This file supplies the mechanized vocabulary that ledger is written in, the
pruning rules it consumes, the one stratum that dies outright, and the logical
assembly from the ledger to the hinge.  It proves NO instance of `GtzWeighted`
and assumes none: every statement here is an emptiness or structure statement
about a stratum.

## Labelled strata versus isomorphism classes — read before quoting a count

`HasLinePattern` pins the pattern ON THE NOSE, with its `Fin`-labels, so two
labellings of the same matroid are two different patterns.  `PatternListIsComplete`
therefore ranges over LABELLED patterns, of which there are 352 at `m = 6` and
8389 at `m = 7` — 8741, not 32.  The Fano class alone has `7! / |Aut(F₇)| =
5040 / 168 = 30` labellings.

`stratumIsTieFree_comp_relabel` closes `StratumIsTieFree` under relabelling, and
`PatternListIsCompleteUpToRelabel` / `hingeHoldsAtSize_of_relabelLedger` are the
ledger and the assembly stated up to relabelling.  Against THOSE the ledger has
exactly 32 entries, one representative per isomorphism class, and
`stratumIsTieFree_fano` retires one of the 23 classes at `m = 7` — equivalently
all 30 of its labellings.  Both forms are shipped; quote the count that matches
the form being used.

## PROVED here, kernel-checked, unconditional

* `tripleBracket` / `atomBracket` and the expansion `tripleBracket_eq` — the
  direction matroid's dependence test as a determinant, in the ordered-triple
  form the ledger indexes by.  `tripleBracket_swapLeft`, `tripleBracket_swapRight`
  record its antisymmetry, so a pattern's vanishing set is slot-symmetric.
  `IsPrimitiveDesign` names the hinge's complement.
* `bracketNormal` and `tripleBracket_eq_bracketNormal_dotProduct` — the bracket
  is a PAIRING against one vector, so a family of vanishing brackets sharing two
  slots exhibits one common normal.  `eq_smul_of_bracketNormal_eq_zero` is the
  converse half (vanishing normal forces parallelism);
  `bracketNormal_atom_ne_zero_of_isPrimitiveDesign` turns primitivity into the
  nonvanishing that the normal must have.
* `hasCommonOrthogonal_of_atomBracket_eq_zero`, `not_dominates_of_atomBracket_eq_zero`,
  `atomBracket_ne_zero_of_dominates` — **the pruning rule in triple form**: a
  dependent triple never dominates, hence a tie is attained on a BASIS.  This is
  the triple-indexed face of the landed `Gtz.not_dominates_of_commonOrthogonal`
  (`Gtz.Ties.TotalTieCorankOne`); what is new is that the hypothesis is now a
  single polynomial in the atom coordinates, which is what a stratum system needs.
* `exists_basisTriple_of_isTie` — every tie has at least one basis triple, so a
  pattern declaring every triple dependent is tie-free for free.
* `trace_probe_mul_atomMatrix` and `not_parseval_of_traceNegativeProbe` — a
  Parseval obstruction for ONE FIXED atom family.  See the scope warning below;
  this tool retires no entry of the current ledger.
* **`fanoCoordinates_impossible` / `fanoBrackets_impossible` /
  `not_hasLinePattern_fano` / `stratumIsTieFree_fano`** — the free win.  Seven
  vectors in `ℝ³` cannot realize the Fano plane: after gauging the frame
  `{0,1,3}` to the standard basis the frame-incident lines force the remaining
  three points, and the last relation evaluates to `2 = 0`.  So the `F₇` stratum
  contains no design whatever, tie or not.  With `stratumIsTieFree_comp_relabel`
  this retires one of the twenty-three isomorphism classes at seven points
  outright, with no dependence on any open question.
* `soleOffPlane_normal_eq_smul_pole`, `soleOffPlane_share_eq_one`,
  `soleOffPlane_leverage_one_lt` — **the near-pencil collapse**.  If every atom
  but one is orthogonal to a nonzero direction, Parseval collapses to a single
  rank-one term: the exceptional atom (the POLE) is PARALLEL to that direction
  and its share `t·|g|²` is exactly `1`, so (at `m ≥ 2`) its leverage is
  `1/t > 1`.  `not_dominates_of_missing_pole` adds that no `k`-subset avoiding
  the pole ever dominates, so at a near-pencil every basis contains the pole.
  `exists_sharedNormal_of_isPrimitiveDesign` MANUFACTURES the normal those
  three consume from the line pattern alone.
* `atomBracket_relabelDesign`, `isTie_relabelDesign_iff`,
  `hasLinePattern_relabelDesign_symm`, **`stratumIsTieFree_comp_relabel`** — the
  relabelling closure, riding the landed `Gtz.relabelDesign` /
  `Gtz.dominates_relabelDesign_iff` (`Gtz.Ties.SelectionObstruction`).  This is
  what lets one representative stand for a whole isomorphism class.
* `LinePattern`, `HasLinePattern`, `StratumIsTieFree`, `PatternListIsComplete`,
  `PatternListIsCompleteUpToRelabel`, **`hingeHoldsAtSize_of_stratumLedger`**,
  **`hingeHoldsAtSize_of_relabelLedger`** — the assembly, in both the labelled
  and the up-to-relabelling form.  A complete enumeration of the primitive
  strata plus tie-freeness of each one yields the hinge's conclusion verbatim.
  Both inputs are named `Prop`s and appear in the statement; neither is assumed
  anywhere else in this file.
* `tetraDesign_atomBracket_ne_zero`, `tieAtFourThree_atomBracket_ne_zero`,
  `stratumIsTieFree_fourThree_of_line` — the `(4,3)` rung restated in ledger
  vocabulary: a `(4,3)` tie has NO dependent triple, so every pattern with a
  line is tie-free and only the uniform matroid `U(3,4)` survives.
* `tetraDesign_hasUniformLinePattern`, `not_stratumIsTieFree_fourThree_uniform`,
  `parallelPairDesign`, `parallelPairDesign_hasLinePattern`,
  **`parallelPairStratum_isNonempty_and_tieFree`** — the two vocabulary
  controls.  The tetrahedron realizes the line-FREE pattern (its four brackets
  are computed here, independently of the tie machinery, so the witness does not
  rest on what it certifies), and `StratumIsTieFree` genuinely fails there.
  `parallelPairDesign` realizes a pattern WITH lines, so an indexing or
  slot-symmetry bug in `HasLinePattern` could not hide behind vacuity: that
  stratum is inhabited by designs and empty of ties, and both halves are proved.

## Scope warning on the trace probe — it retires nothing on this ledger

`not_parseval_of_traceNegativeProbe` says: no nonnegative weights resolve the
identity over THE GIVEN atom family.  Its hypothesis is about one fixed family,
not about a stratum, which is a positive-dimensional set (twelve free parameters
at rank three after gauge), and no single constant probe is nonnegative across
one.  Worse for its advertised role: exact rational realizations exist for all
thirty-one non-Fano hinge strata, and whitening any positive masses turns a
realization into a genuine `WeightedDesign`, so every remaining stratum PROVABLY
carries designs and no negative-trace probe for one can exist.  The twenty-nine
open entries need TIE-freeness, a strictly finer semialgebraic condition the
trace probe never sees (it does not mention `Dominates`).  The theorem is correct
and is kept as general scalable-frame infrastructure; it is not a route to any
open entry, and the earlier description of it as "the socket the next
per-matroid certificate plugs into" is withdrawn.

CITED for the probe: the easy implication of Kutyniok–Okoudjou–Philipp–Tuley,
*Scalable frames*, LAA 438 (2013), Theorem 3.2 (i)⇒(ii).  The hard converse is
never invoked, so nothing here depends on it.

## CITED, not reproved here

* `Gtz.tieAtFourThree_isTotal` / `_isUniformMatroid` / `_isPrimitive`
  (`Gtz.Ties.TotalTieCorankOne`) — the `(4,3)` classification, and the fact that
  the hinge's conclusion is FALSE at `m = 4` (`Gtz.tetraDesign_isTie` is a tie
  with four pairwise non-parallel atoms), which is why the hinge is asserted
  from `m = 6` on.
* `Gtz.diamondDesign_isTie` (`Gtz.Design.DiamondPrimitive`) — the diamond
  `M(K₄ − e)`, a primitive `(5,3)` tie.  So the hinge is also FALSE at `m = 5`,
  and any ledger argument must be run at `m = 6, 7` only.
* `Gtz.relabelDesign`, `Gtz.subsetSum_relabelDesign`,
  `Gtz.dominates_relabelDesign_iff` (`Gtz.Ties.SelectionObstruction`) — the
  relabelling action this file extends from `Dominates` to `IsTie` and to
  `HasLinePattern`.
* `Gtz.HasParallelPair` and the hinge predicate `Gtz.HingeHoldsAtSize` are
  already defined in `Gtz.Reduction.SplitTransfer`; this file does NOT redefine
  either, and imports neither, so nothing here depends on that module's state.
  The conclusion of both assembly theorems is the body of `HingeHoldsAtSize` at
  `rank = 3` written out, and `IsPrimitiveDesign` is `¬ Gtz.HasParallelPair`
  with the negation pushed in; both correspondences are definitional, so a
  wiring module importing both modules obtains the hinge from these theorems by
  `:=` with no bridge lemma.  (Read the live declaration before wiring: the
  predicate has carried more than one name across the campaign's working copies,
  and the correspondence is name-independent because it is the body that matches.)
* Non-representability of `F₇` over any field of characteristic `≠ 2` is
  classical (Oxley, *Matroid Theory*, Prop. 6.4.8); `fanoBrackets_impossible` is
  a self-contained real-linear-algebra proof of the real case, not a citation.

## MEASURED, outside Lean — the ledger's current state, and it is NOT closed

An exhaustive exact-rational sweep of all thirty-two primitive isomorphism
classes (nine at `m = 6`, twenty-three at `m = 7`; counts `2, 4, 9, 23` for
`q = 4, 5, 6, 7` cross-checked against the classical simple-rank-3 numbers by
two independent enumerations) produced three verdicts.

* EMPTY, mechanized: `F₇` at `q = 7`, proved here — one isomorphism class,
  equivalently thirty labelled strata via `stratumIsTieFree_comp_relabel`.
* EMPTY on paper, NOT mechanized: the near-pencils `q6m3` (one five-point line)
  and `q7m4` (one six-point line).  Two ingredients were needed and one has now
  landed.  (i) `exists_sharedNormal_of_isPrimitiveDesign` produces the single
  normal shared by all planar atoms out of the line pattern — PROVED here.
  (ii) The rank-two transport is the remaining residue: with
  `poleShare = 1 − t_pole`, the planar family rescaled to `h_c =
  √(m_c · poleShare / t_c) · u_c` at weights `τ_c = t_c / poleShare` is a genuine
  `WeightedDesign _ 2`, so `Gtz.gtz_rank_two` yields a planar pair with
  `G ⪰ (1/poleShare) · I_plane`, and `1/poleShare > 1` is where the STRICTNESS
  comes from — the factor is `1/(1 − t_pole)`, not `1 − t_pole`; getting it
  backwards makes the argument fail.  Together with the pole-axis gap
  `(1 − t_pole)/t_pole > 0` from `soleOffPlane_share_eq_one` and
  block-diagonality, `S_{{pole} ∪ C} − I` is positive definite.  That transport
  is the named residue.
* ATTAINED: `U(3,4)` at `q = 4` and the diamond `M(K₄ − e)` at `q = 5`, both
  already in the repository.  These are the only two maximal simple SP-graphic
  rank-three matroids, which is the shape of the conjecture below.
* OPEN, no tie found: the remaining twenty-nine classes.  At each, the best
  point located inside the searched collar has value exactly `≥ 1 + ε` with `ε`
  rational and a witness basis dominating strictly; the smallest excesses at
  collar radius `1.5` are `1.45e-5` (`q6m5`) and `2.36e-5` (`q7m10`), the
  largest is `1.84e-2` at `F₇⁻`.  Every minimizer sits on the collar BOUNDARY:
  opening the collar drops the excess by one to three orders of magnitude.  That
  is the signature of an infimum attained only on the stratum boundary,
  consistent with emptiness of the OPEN stratum, and it is not a proof.
* `M(K₄)` is the sharpest of the twenty-nine, and its degeneration was
  misdescribed in an earlier draft.  Exactly, in rational arithmetic over the
  six grounded `K₄` edge vectors (graphic matroids are uniquely representable,
  so those parameterize the whole stratum), switching the sixth edge on with
  `mass = eps²` and `weight = eps` on top of `Gtz.diamondDesign` gives NO tie for
  every `eps > 0`, with strict-domination witness `(0,1,2)` and `det(S − I)` =
  6345, 498.88, 161.67, 11.23, 1.0842, 1.0800e-3 at `eps` = 1/2, 1/5, 1/10,
  1/100, 1/1000, 1e-6.  The excess is `Θ(eps)` and the boundary point is the
  `(5,3)` DIAMOND TIE.  So `M(K₄)`'s infimum is inherited from the `m = 5`
  counterexample sitting on its boundary — one atom's mass and length going to
  zero, not three weights being dusted.  Consequence: no argument that is
  continuous up to the closure can work there, which is exactly why the
  inequation (OPEN) half of `HasLinePattern` is load-bearing.
* Total tie holds exactly on every tie in the repository — `tetraDesign` and
  `sharpDesign` at `(4,3)` (4/4 bases at `λ_min = 1`), `diamondDesign` at
  `(5,3)` (8/8 bases, both non-bases singular, corank 2), and
  `splitTetraDesign` at `(6,3)` (12/12 bases, corank 3) — all verified in exact
  arithmetic by principal minors, no eigenvalue solver.  Whether total tie is
  FORCED at corank `≥ 2` remains OPEN; per `Gtz.Ties.TotalTieCorankOne` a proof
  through criticality of the max would prove `GtzWeighted` at the same size.  No
  statement in this file assumes it, and no namespace here carries a criticality
  hypothesis.
* Three apparent GTZ violations found during that sweep were float artifacts,
  each refuted in exact rational arithmetic (`q4m0` float `0.999999999995` →
  exact `≥ 1 + 2.70e-12`; `q5m0` → `≥ 1 + 1.16e-8`; `q5m3` → `≥ 1 + 2.22e-7`).
  A fourth trap was recorded independently: whitening atoms before evaluating
  drives weights to `~1e-23` and atom norms to `~1e11`, and double precision then
  reports `λ_min` values that are impossible for a sum of rank-one PSD matrices.
  Search must compare `Σ (mass/weight) u uᵀ ⪰ Σ mass u uᵀ` without whitening.
  The campaign's earlier note that `F₇⁻` has interior minimum `1.1225` is a
  uniform-design-weight SLICE fact and is contradicted as a family fact by
  points of value `1.00037`; it must not be quoted as a floor.
* CONJECTURED, and the sharpest next attack: every tie in the repository has an
  SP-graphic direction matroid, and the `m = 6` sweep found the genuinely tight
  designs to be exactly the SP-graphic ones.  A simple rank-three SP-graphic
  matroid has at most FIVE elements (rank three graphic forces four vertices;
  simple forces a simple graph; no `K₄` minor then leaves at most five edges,
  i.e. `K₄ − e`).  So "every tie's direction matroid is SP-graphic" implies the
  hinge at EVERY size `≥ 6` in one step, and simultaneously explains why the
  hinge is false at exactly `m = 4, 5`.  That single structural statement would
  replace all thirty-two per-class emptiness proofs, and it does not go through
  criticality.

So the ledger stands at ONE isomorphism class mechanized (`F₇`, equivalently
thirty labelled strata), TWO closed on paper modulo the one named rank-two
transport residue, TWO attained and outside the hinge, and TWENTY-NINE open.
`hingeHoldsAtSize_of_relabelLedger` is stated so that every class still open is
one named hypothesis, and nothing in this file pretends otherwise.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Ties.TotalTieCorankOne
import Gtz.Ties.SelectionObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The bracket: the direction matroid's dependence test

Domination and `IsTie` read only the atom vectors (`Gtz.subsetSum` is
weight-free), so the combinatorial datum a stratum is cut out by is which
triples of directions are dependent.  In `ℝ³` that is the vanishing of one
determinant per triple. -/

/-- The scalar triple product of three vectors of `ℝ³`, as the determinant of
the matrix carrying them as rows.  The triple is dependent exactly when this
vanishes. -/
def tripleBracket (leftVec midVec rightVec : Fin 3 → ℝ) : ℝ :=
  (Matrix.of ![leftVec, midVec, rightVec]).det

/-- The bracket expanded along the first row — the polynomial form every stratum
system is written in. -/
theorem tripleBracket_eq (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec midVec rightVec =
      leftVec 0 * (midVec 1 * rightVec 2 - midVec 2 * rightVec 1)
        - leftVec 1 * (midVec 0 * rightVec 2 - midVec 2 * rightVec 0)
        + leftVec 2 * (midVec 0 * rightVec 1 - midVec 1 * rightVec 0) := by
  simp [tripleBracket, Matrix.det_fin_three]
  ring

/-- Swapping the first two slots negates the bracket. -/
theorem tripleBracket_swapLeft (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec midVec rightVec = -tripleBracket midVec leftVec rightVec := by
  simp only [tripleBracket_eq]; ring

/-- Swapping the last two slots negates the bracket.  With
`tripleBracket_swapLeft` this makes the vanishing set of a bracket invariant
under every permutation of the three slots, so a line pattern may be read as a
statement about unordered triples. -/
theorem tripleBracket_swapRight (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec midVec rightVec = -tripleBracket leftVec rightVec midVec := by
  simp only [tripleBracket_eq]; ring

/-- Two parallel slots kill the bracket. -/
theorem tripleBracket_eq_zero_of_parallel (leftVec rightVec : Fin 3 → ℝ) (ratio : ℝ)
    {midVec : Fin 3 → ℝ} (hparallel : midVec = ratio • leftVec) :
    tripleBracket leftVec midVec rightVec = 0 := by
  subst hparallel
  simp only [tripleBracket_eq, Pi.smul_apply, smul_eq_mul]; ring

/-- The bracket of three atoms of a rank-three design, indexed by their labels. -/
def atomBracket {m : ℕ} (D : WeightedDesign m 3)
    (leftLabel midLabel rightLabel : Fin m) : ℝ :=
  tripleBracket (D.atom leftLabel) (D.atom midLabel) (D.atom rightLabel)

/-- No two atoms are parallel.  This is `¬ Gtz.HasParallelPair` with the negation
pushed in; it is the exact complement of the hinge's conclusion, and the standing
hypothesis of every statement about a SIMPLE direction matroid. -/
def IsPrimitiveDesign {size rank : ℕ} (D : WeightedDesign size rank) : Prop :=
  ∀ (keptLabel dropLabel : Fin size) (ratio : ℝ),
    keptLabel ≠ dropLabel → D.atom dropLabel ≠ ratio • D.atom keptLabel

/-! ## The bracket as a pairing: one normal for a whole coplanar family

The bracket of a fixed pair against a varying third slot is a linear functional,
namely pairing against one vector.  That vector is the normal a near-pencil
argument needs: a family of vanishing brackets all sharing the same two slots
exhibits ONE common orthogonal direction, not one per triple.  The converse half
— a vanishing normal forces the two slots parallel — is what turns primitivity
into the nonvanishing that makes the normal usable. -/

/-- The vector the bracket pairs its third slot against. -/
def bracketNormal (leftVec rightVec : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![leftVec 1 * rightVec 2 - leftVec 2 * rightVec 1,
    leftVec 2 * rightVec 0 - leftVec 0 * rightVec 2,
    leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0]

/-- **The bracket is a pairing.**  Fixing the first two slots, the bracket is the
inner product against `bracketNormal`. -/
theorem tripleBracket_eq_bracketNormal_dotProduct (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec midVec rightVec = bracketNormal leftVec midVec ⬝ᵥ rightVec := by
  simp only [tripleBracket_eq, bracketNormal, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- A vanishing normal makes the two vectors proportional up to the left one's
squared norm — the scale-free half of the parallelism statement. -/
theorem smul_dotProduct_self_eq_of_bracketNormal_eq_zero (leftVec rightVec : Fin 3 → ℝ)
    (hnormalZero : bracketNormal leftVec rightVec = 0) :
    (leftVec ⬝ᵥ leftVec) • rightVec = (leftVec ⬝ᵥ rightVec) • leftVec := by
  have hcomponentZero : ∀ index : Fin 3, bracketNormal leftVec rightVec index = 0 :=
    fun index => congrFun hnormalZero index
  have hfirst := hcomponentZero 0
  have hsecond := hcomponentZero 1
  have hthird := hcomponentZero 2
  simp only [bracketNormal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hfirst hsecond hthird
  funext index
  fin_cases index
  · show (leftVec ⬝ᵥ leftVec) * rightVec 0 = (leftVec ⬝ᵥ rightVec) * leftVec 0
    simp only [dotProduct, Fin.sum_univ_three]
    linear_combination (-leftVec 1) * hthird + leftVec 2 * hsecond
  · show (leftVec ⬝ᵥ leftVec) * rightVec 1 = (leftVec ⬝ᵥ rightVec) * leftVec 1
    simp only [dotProduct, Fin.sum_univ_three]
    linear_combination leftVec 0 * hthird + (-leftVec 2) * hfirst
  · show (leftVec ⬝ᵥ leftVec) * rightVec 2 = (leftVec ⬝ᵥ rightVec) * leftVec 2
    simp only [dotProduct, Fin.sum_univ_three]
    linear_combination (-leftVec 0) * hsecond + leftVec 1 * hfirst

/-- **A vanishing normal means parallel**, with the ratio exhibited. -/
theorem eq_smul_of_bracketNormal_eq_zero (leftVec rightVec : Fin 3 → ℝ)
    (hleftNe : leftVec ≠ 0) (hnormalZero : bracketNormal leftVec rightVec = 0) :
    rightVec = ((leftVec ⬝ᵥ rightVec) / (leftVec ⬝ᵥ leftVec)) • leftVec := by
  have hnormNe : leftVec ⬝ᵥ leftVec ≠ 0 := fun hzero => hleftNe (dotProduct_self_eq_zero.mp hzero)
  have hscaled := smul_dotProduct_self_eq_of_bracketNormal_eq_zero leftVec rightVec hnormalZero
  funext index
  have hcomponent := congrFun hscaled index
  simp only [Pi.smul_apply, smul_eq_mul] at hcomponent ⊢
  field_simp
  linarith [hcomponent]

/-- Contrapositive: non-parallel vectors have a nonzero normal. -/
theorem bracketNormal_ne_zero_of_not_parallel (leftVec rightVec : Fin 3 → ℝ)
    (hleftNe : leftVec ≠ 0) (hnotParallel : ∀ ratio : ℝ, rightVec ≠ ratio • leftVec) :
    bracketNormal leftVec rightVec ≠ 0 := fun hnormalZero =>
  hnotParallel _ (eq_smul_of_bracketNormal_eq_zero leftVec rightVec hleftNe hnormalZero)

/-- **A primitive design has no zero atom.**  Taking `ratio = 0` in primitivity
against any other label rules the zero vector out. -/
theorem atom_ne_zero_of_isPrimitiveDesign {m rank : ℕ} (hsize : 2 ≤ m)
    (D : WeightedDesign m rank) (hprimitive : IsPrimitiveDesign D) (label : Fin m) :
    D.atom label ≠ 0 := by
  obtain ⟨otherLabel, hother⟩ := Fintype.exists_ne_of_one_lt_card
    (by simp only [Fintype.card_fin]; omega) label
  have hne := hprimitive otherLabel label 0 hother
  rw [zero_smul] at hne
  exact hne

/-- **Primitivity makes every pair's normal nonzero.** -/
theorem bracketNormal_atom_ne_zero_of_isPrimitiveDesign {m : ℕ} (hsize : 2 ≤ m)
    (D : WeightedDesign m 3) (hprimitive : IsPrimitiveDesign D)
    (firstLabel secondLabel : Fin m) (hdistinct : firstLabel ≠ secondLabel) :
    bracketNormal (D.atom firstLabel) (D.atom secondLabel) ≠ 0 :=
  bracketNormal_ne_zero_of_not_parallel _ _
    (atom_ne_zero_of_isPrimitiveDesign hsize D hprimitive firstLabel)
    (fun ratio => hprimitive firstLabel secondLabel ratio hdistinct)

/-! ## The pruning rule, in triple form

A vanishing bracket produces a direction annihilated by all three atoms, so the
gap form is `−|w|²` there and the triple never dominates.  Contrapositive: every
dominating triple is a BASIS of the direction matroid.  This is the landed
`Gtz.not_dominates_of_commonOrthogonal` re-indexed by an explicit triple, which
is the shape a stratum system consumes. -/

/-- A vanishing bracket exhibits a common orthogonal direction of the triple. -/
theorem hasCommonOrthogonal_of_atomBracket_eq_zero {m : ℕ} (D : WeightedDesign m 3)
    (leftLabel midLabel rightLabel : Fin m)
    (hvanish : atomBracket D leftLabel midLabel rightLabel = 0) :
    HasCommonOrthogonal D {leftLabel, midLabel, rightLabel} := by
  rw [atomBracket, tripleBracket] at hvanish
  obtain ⟨direction, hne, hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hvanish
  refine ⟨direction, hne, fun label hlabel => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel
  rcases hlabel with rfl | rfl | rfl
  · simpa [Matrix.mulVec] using congrFun hkernel 0
  · simpa [Matrix.mulVec] using congrFun hkernel 1
  · simpa [Matrix.mulVec] using congrFun hkernel 2

/-- **A dependent triple never dominates.** -/
theorem not_dominates_of_atomBracket_eq_zero {m : ℕ} (D : WeightedDesign m 3)
    (leftLabel midLabel rightLabel : Fin m)
    (hvanish : atomBracket D leftLabel midLabel rightLabel = 0) :
    ¬ Dominates D {leftLabel, midLabel, rightLabel} :=
  not_dominates_of_commonOrthogonal D _
    (hasCommonOrthogonal_of_atomBracket_eq_zero D leftLabel midLabel rightLabel hvanish)

/-- **A dominating triple is a basis.** -/
theorem atomBracket_ne_zero_of_dominates {m : ℕ} (D : WeightedDesign m 3)
    (leftLabel midLabel rightLabel : Fin m)
    (hdominates : Dominates D {leftLabel, midLabel, rightLabel}) :
    atomBracket D leftLabel midLabel rightLabel ≠ 0 := fun hvanish =>
  not_dominates_of_atomBracket_eq_zero D leftLabel midLabel rightLabel hvanish hdominates

/-- **Every tie has a basis triple.**  A pattern that declares every triple
dependent is therefore tie-free with no algebra at all. -/
theorem exists_basisTriple_of_isTie {m : ℕ} (D : WeightedDesign m 3) (htie : IsTie D) :
    ∃ leftLabel midLabel rightLabel : Fin m,
      leftLabel ≠ midLabel ∧ leftLabel ≠ rightLabel ∧ midLabel ≠ rightLabel ∧
        atomBracket D leftLabel midLabel rightLabel ≠ 0 := by
  obtain ⟨⟨dominatingSubset, hcard, hdominates⟩, _⟩ := htie
  obtain ⟨leftLabel, midLabel, rightLabel, hleftMid, hleftRight, hmidRight, hsubset⟩ :=
    Finset.card_eq_three.mp hcard
  subst hsubset
  exact ⟨leftLabel, midLabel, rightLabel, hleftMid, hleftRight, hmidRight,
    atomBracket_ne_zero_of_dominates D leftLabel midLabel rightLabel hdominates⟩

/-! ## The trace probe: a Parseval obstruction for one fixed atom family

Domination is weight-free, but a design also needs POSITIVE weights resolving
the identity.  That is a linear feasibility question about the directions alone,
and its cheapest refutation is a single matrix.  If `probe` has negative trace
and nonnegative quadratic form at every direction, then pairing Parseval with
`probe` gives `0 > tr probe = Σ t_c · (g_cᵀ probe g_c) ≥ 0`.

Scope: the hypothesis quantifies over the labels of ONE atom family, so the
conclusion is about that family, not about a stratum.  See the scope warning in
the file header — every non-Fano hinge stratum provably carries designs, so this
tool retires no open ledger entry.  It is kept as correct general infrastructure. -/

/-- Pairing an atom against a probe is the probe's quadratic form at the atom. -/
theorem trace_probe_mul_atomMatrix {k : ℕ} (probe : Matrix (Fin k) (Fin k) ℝ)
    (vec : Fin k → ℝ) :
    Matrix.trace (probe * atomMatrix vec) = vec ⬝ᵥ (probe *ᵥ vec) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, atomMatrix,
    Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The trace-probe Parseval obstruction.**  No nonnegative weights resolve the
identity over a family that a negative-trace probe evaluates nonnegatively. -/
theorem not_parseval_of_traceNegativeProbe {m k : ℕ} (atomVec : Fin m → (Fin k → ℝ))
    (probe : Matrix (Fin k) (Fin k) ℝ)
    (hprobeNonneg : ∀ label, 0 ≤ atomVec label ⬝ᵥ (probe *ᵥ atomVec label))
    (htraceNegative : Matrix.trace probe < 0)
    (weight : Fin m → ℝ) (hweightNonneg : ∀ label, 0 ≤ weight label)
    (hparseval : ∑ label, weight label • atomMatrix (atomVec label)
      = (1 : Matrix (Fin k) (Fin k) ℝ)) : False := by
  have hpaired : Matrix.trace (probe * ∑ label, weight label • atomMatrix (atomVec label))
      = ∑ label, weight label * (atomVec label ⬝ᵥ (probe *ᵥ atomVec label)) := by
    rw [Finset.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun label _ => by
      rw [Matrix.mul_smul, Matrix.trace_smul, trace_probe_mul_atomMatrix, smul_eq_mul]
  rw [hparseval, Matrix.mul_one] at hpaired
  have hnonneg : 0 ≤ ∑ label, weight label * (atomVec label ⬝ᵥ (probe *ᵥ atomVec label)) :=
    Finset.sum_nonneg fun label _ => mul_nonneg (hweightNonneg label) (hprobeNonneg label)
  rw [← hpaired] at hnonneg
  linarith

/-- **No design with these atoms.**  A negative-trace probe nonnegative on a
direction family rules out every `WeightedDesign` carrying exactly those atoms —
in particular every tie among them.  It says nothing about neighbouring atom
families, hence nothing about a stratum. -/
theorem no_design_of_traceNegativeProbe {m k : ℕ} (D : WeightedDesign m k)
    (probe : Matrix (Fin k) (Fin k) ℝ)
    (hprobeNonneg : ∀ label, 0 ≤ D.atom label ⬝ᵥ (probe *ᵥ D.atom label))
    (htraceNegative : Matrix.trace probe < 0) : False :=
  not_parseval_of_traceNegativeProbe D.atom probe hprobeNonneg htraceNegative D.weight
    (fun label => (D.weight_pos label).le) D.isParseval

/-! ## The near-pencil collapse

If every atom but one is orthogonal to a nonzero direction, Parseval evaluated at
that direction has a single surviving term.  The exceptional atom (the POLE) is
therefore parallel to the direction, and its share is exactly one.  This pins the
pole's leverage at `1/t > 1` and needs no rank-two input.  The last statement of
the section manufactures the shared normal that the earlier ones consume, so a
near-pencil LINE PATTERN — not a hand-supplied vector — is enough to enter. -/

/-- A weighted rank-one atom applied to a vector is a rescaled copy of that atom.
Stated with the scale attached because that is the shape Parseval hands over. -/
theorem smul_atomMatrix_mulVec {k : ℕ} (scale : ℝ) (vec direction : Fin k → ℝ) :
    (scale • atomMatrix vec) *ᵥ direction = (scale * (vec ⬝ᵥ direction)) • vec := by
  funext coordIndex
  have hleft : ((scale • atomMatrix vec) *ᵥ direction) coordIndex
      = ∑ innerIndex, scale * vec coordIndex * vec innerIndex * direction innerIndex := by
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hright : ((scale * (vec ⬝ᵥ direction)) • vec) coordIndex
      = ∑ innerIndex, scale * vec coordIndex * vec innerIndex * direction innerIndex := by
    simp only [Pi.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hleft, hright]

/-- **The collapse.**  With every non-pole atom orthogonal to `normalVec`,
Parseval says `normalVec` is a multiple of the pole's atom. -/
theorem soleOffPlane_normal_eq_smul_pole {m : ℕ} (D : WeightedDesign m 3)
    (poleLabel : Fin m) {normalVec : Fin 3 → ℝ}
    (hplanar : ∀ label, label ≠ poleLabel → D.atom label ⬝ᵥ normalVec = 0) :
    normalVec
      = (D.weight poleLabel * (D.atom poleLabel ⬝ᵥ normalVec)) • D.atom poleLabel := by
  have hparseval := congrArg (fun gram => gram *ᵥ normalVec) D.isParseval
  simp only [Matrix.one_mulVec, Matrix.sum_mulVec, smul_atomMatrix_mulVec] at hparseval
  rw [Finset.sum_eq_single poleLabel
      (fun label _ hne => by rw [hplanar label hne, mul_zero, zero_smul])
      (fun hnotMem => absurd (Finset.mem_univ poleLabel) hnotMem)] at hparseval
  exact hparseval.symm

/-- **The pole's share is exactly one**: `t · |g|² = 1`.  Equality here is what
makes deflation at the pole degenerate, and it is the quantitative content of the
collapse.  Its complement `(1 − t)/t > 0` is the pole-axis half of the gap the
near-pencil argument needs. -/
theorem soleOffPlane_share_eq_one {m : ℕ} (D : WeightedDesign m 3)
    (poleLabel : Fin m) {normalVec : Fin 3 → ℝ} (hnormalNe : normalVec ≠ 0)
    (hplanar : ∀ label, label ≠ poleLabel → D.atom label ⬝ᵥ normalVec = 0) :
    D.weight poleLabel * leverageOf (D.atom poleLabel) = 1 := by
  have hcollapse := soleOffPlane_normal_eq_smul_pole D poleLabel hplanar
  have hleverage : D.atom poleLabel ⬝ᵥ D.atom poleLabel = leverageOf (D.atom poleLabel) := by
    simp only [dotProduct, leverageOf, pow_two]
  have hproject := congrArg (fun vec => D.atom poleLabel ⬝ᵥ vec) hcollapse
  simp only [dotProduct_smul, smul_eq_mul, hleverage] at hproject
  have hprojectNe : D.atom poleLabel ⬝ᵥ normalVec ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero, zero_smul] at hcollapse
    exact hnormalNe hcollapse
  have hfactored : (D.atom poleLabel ⬝ᵥ normalVec)
      * (D.weight poleLabel * leverageOf (D.atom poleLabel) - 1) = 0 := by
    nlinarith [hproject]
  rcases mul_eq_zero.mp hfactored with hzero | hgap
  · exact absurd hzero hprojectNe
  · linarith

/-- **The pole is heavy**: at two or more atoms its leverage strictly exceeds one.
This is the near-pencil's first block estimate — on the pole's own axis the gap
matrix of any triple through the pole is already strictly positive. -/
theorem soleOffPlane_leverage_one_lt {m : ℕ} (hsize : 2 ≤ m) (D : WeightedDesign m 3)
    (poleLabel : Fin m) {normalVec : Fin 3 → ℝ} (hnormalNe : normalVec ≠ 0)
    (hplanar : ∀ label, label ≠ poleLabel → D.atom label ⬝ᵥ normalVec = 0) :
    1 < leverageOf (D.atom poleLabel) := by
  have hshare := soleOffPlane_share_eq_one D poleLabel hnormalNe hplanar
  have hweightPos := D.weight_pos poleLabel
  have hweightLtOne := weight_lt_one D hsize poleLabel
  nlinarith [hshare, hweightPos, hweightLtOne]

/-- **Every dominating subset of a near-pencil contains the pole.**  A subset
avoiding the pole lies entirely in the plane, so it inherits the normal as a
common orthogonal direction. -/
theorem not_dominates_of_missing_pole {m : ℕ} (D : WeightedDesign m 3)
    (poleLabel : Fin m) (planarSubset : Finset (Fin m)) (hmissing : poleLabel ∉ planarSubset)
    {normalVec : Fin 3 → ℝ} (hnormalNe : normalVec ≠ 0)
    (hplanar : ∀ label, label ≠ poleLabel → D.atom label ⬝ᵥ normalVec = 0) :
    ¬ Dominates D planarSubset :=
  not_dominates_of_commonOrthogonal D planarSubset
    ⟨normalVec, hnormalNe, fun label hlabel =>
      hplanar label (fun hequal => hmissing (hequal ▸ hlabel))⟩

/-- **The near-pencil's normal, manufactured from the line pattern.**  If two
distinct labels' brackets against every non-pole label vanish, then at a
primitive design their `bracketNormal` is a single NONZERO direction orthogonal
to every non-pole atom — exactly the hypothesis
`soleOffPlane_share_eq_one`, `soleOffPlane_leverage_one_lt` and
`not_dominates_of_missing_pole` take.  Primitivity enters only to make the normal
nonzero.  This closes the "one normal per triple versus one normal for the whole
plane" gap: the entry point is now a bracket pattern, not a supplied vector. -/
theorem exists_sharedNormal_of_isPrimitiveDesign {m : ℕ} (hsize : 2 ≤ m)
    (D : WeightedDesign m 3) (hprimitive : IsPrimitiveDesign D)
    (poleLabel firstLabel secondLabel : Fin m) (hdistinct : firstLabel ≠ secondLabel)
    (hplanarTriples : ∀ label, label ≠ poleLabel →
      atomBracket D firstLabel secondLabel label = 0) :
    ∃ normalVec : Fin 3 → ℝ, normalVec ≠ 0 ∧
      ∀ label, label ≠ poleLabel → D.atom label ⬝ᵥ normalVec = 0 := by
  refine ⟨bracketNormal (D.atom firstLabel) (D.atom secondLabel),
    bracketNormal_atom_ne_zero_of_isPrimitiveDesign hsize D hprimitive firstLabel secondLabel
      hdistinct, fun label hlabel => ?_⟩
  rw [dotProduct_comm, ← tripleBracket_eq_bracketNormal_dotProduct]
  exact hplanarTriples label hlabel

/-! ## The Fano stratum is empty

Gauge the frame `{0, 1, 3}` to the standard basis of `ℝ³`.  The three lines
`{0,1,2}`, `{0,3,4}`, `{1,3,5}` each kill one coordinate of the points `2, 4, 5`;
the lines `{0,5,6}`, `{1,4,6}`, `{2,3,6}` become three bilinear relations; and
the seventh line `{2,4,5}` becomes a fourth.  Eliminating gives
`2 · (five nonzero frame brackets) = 0`, so the configuration exists only in
characteristic two.  The elimination is a single `linear_combination` with the
cofactors written out. -/

/-- **The Fano contradiction in gauge-fixed coordinates.**  The four relations
carried by the lines `{0,5,6}`, `{1,4,6}`, `{2,3,6}`, `{2,4,5}` force
`2 · twoSecond · fourFirst · fiveThird · sixFirst · sixThird = 0`, and those five
factors are exactly the frame brackets of the non-lines `{0,2,3}`, `{1,3,4}`,
`{0,1,5}`, `{1,3,6}`, `{0,1,6}`. -/
theorem fanoCoordinates_impossible
    (twoFirst twoSecond fourFirst fourThird fiveSecond fiveThird
      sixFirst sixSecond sixThird : ℝ)
    (hline056 : fiveSecond * sixThird - fiveThird * sixSecond = 0)
    (hline146 : fourThird * sixFirst - fourFirst * sixThird = 0)
    (hline236 : twoSecond * sixFirst - twoFirst * sixSecond = 0)
    (hline245 : twoFirst * fourThird * fiveSecond + twoSecond * fourFirst * fiveThird = 0)
    (htwoSecond : twoSecond ≠ 0) (hfourFirst : fourFirst ≠ 0) (hfiveThird : fiveThird ≠ 0)
    (hsixFirst : sixFirst ≠ 0) (hsixThird : sixThird ≠ 0) : False := by
  have hdoubled : (2 : ℝ) * (twoSecond * fourFirst * fiveThird * sixFirst * sixThird) = 0 := by
    linear_combination (sixFirst * sixThird) * hline245
      - (twoFirst * fiveSecond * sixThird) * hline146
      - (twoFirst * fourFirst * sixThird) * hline056
      + (fourFirst * fiveThird * sixThird) * hline236
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero htwoSecond hfourFirst) hfiveThird)
    hsixFirst) hsixThird (by linarith)

/-- **No seven vectors of `ℝ³` realize the Fano plane.**  Seven brackets vanish
on the Fano lines and six do not vanish on the listed non-lines; that is
contradictory over `ℝ`.  The six non-vanishing hypotheses are exactly what a
Fano REALIZATION supplies — `{0,1,3}`, `{0,1,5}`, `{0,1,6}`, `{0,2,3}`,
`{1,3,4}`, `{1,3,6}` are non-lines of `F₇`. -/
theorem fanoBrackets_impossible (vecFamily : Fin 7 → (Fin 3 → ℝ))
    (hline012 : tripleBracket (vecFamily 0) (vecFamily 1) (vecFamily 2) = 0)
    (hline034 : tripleBracket (vecFamily 0) (vecFamily 3) (vecFamily 4) = 0)
    (hline056 : tripleBracket (vecFamily 0) (vecFamily 5) (vecFamily 6) = 0)
    (hline135 : tripleBracket (vecFamily 1) (vecFamily 3) (vecFamily 5) = 0)
    (hline146 : tripleBracket (vecFamily 1) (vecFamily 4) (vecFamily 6) = 0)
    (hline236 : tripleBracket (vecFamily 2) (vecFamily 3) (vecFamily 6) = 0)
    (hline245 : tripleBracket (vecFamily 2) (vecFamily 4) (vecFamily 5) = 0)
    (hbasis013 : tripleBracket (vecFamily 0) (vecFamily 1) (vecFamily 3) ≠ 0)
    (hbasis015 : tripleBracket (vecFamily 0) (vecFamily 1) (vecFamily 5) ≠ 0)
    (hbasis016 : tripleBracket (vecFamily 0) (vecFamily 1) (vecFamily 6) ≠ 0)
    (hbasis023 : tripleBracket (vecFamily 0) (vecFamily 2) (vecFamily 3) ≠ 0)
    (hbasis134 : tripleBracket (vecFamily 1) (vecFamily 3) (vecFamily 4) ≠ 0)
    (hbasis136 : tripleBracket (vecFamily 1) (vecFamily 3) (vecFamily 6) ≠ 0) : False := by
  classical
  set frame : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of ![vecFamily 0, vecFamily 1, vecFamily 3] with hframe
  have hdet : frame.det ≠ 0 := hbasis013
  have hunit : IsUnit frameᵀ.det := by
    rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hdet
  set coord : Fin 7 → (Fin 3 → ℝ) := fun label => (frameᵀ)⁻¹ *ᵥ vecFamily label with hcoord
  have hrecover : ∀ label : Fin 7, frameᵀ *ᵥ coord label = vecFamily label := by
    intro label
    rw [hcoord]; simp only
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hrow : ∀ (label : Fin 7) (coordIndex : Fin 3),
      ∑ innerIndex, coord label innerIndex * frame innerIndex coordIndex
        = vecFamily label coordIndex := by
    intro label coordIndex
    have hstep := congrFun (hrecover label) coordIndex
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply] at hstep
    rw [← hstep]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hbracket : ∀ leftLabel midLabel rightLabel : Fin 7,
      tripleBracket (vecFamily leftLabel) (vecFamily midLabel) (vecFamily rightLabel)
        = tripleBracket (coord leftLabel) (coord midLabel) (coord rightLabel) * frame.det := by
    intro leftLabel midLabel rightLabel
    have hmatEq : Matrix.of ![coord leftLabel, coord midLabel, coord rightLabel] * frame
        = Matrix.of ![vecFamily leftLabel, vecFamily midLabel, vecFamily rightLabel] := by
      ext rowIndex coordIndex
      fin_cases rowIndex <;> simpa [Matrix.mul_apply] using hrow _ coordIndex
    rw [tripleBracket, tripleBracket, ← Matrix.det_mul, hmatEq]
  have htransfer : ∀ leftLabel midLabel rightLabel : Fin 7,
      tripleBracket (vecFamily leftLabel) (vecFamily midLabel) (vecFamily rightLabel) = 0 →
        tripleBracket (coord leftLabel) (coord midLabel) (coord rightLabel) = 0 := by
    intro leftLabel midLabel rightLabel hvanish
    rw [hbracket] at hvanish
    exact (mul_eq_zero.mp hvanish).resolve_right hdet
  have htransferNe : ∀ leftLabel midLabel rightLabel : Fin 7,
      tripleBracket (vecFamily leftLabel) (vecFamily midLabel) (vecFamily rightLabel) ≠ 0 →
        tripleBracket (coord leftLabel) (coord midLabel) (coord rightLabel) ≠ 0 := by
    intro leftLabel midLabel rightLabel hne hvanish
    exact hne (by rw [hbracket, hvanish, zero_mul])
  have hframeRow : ∀ standardIndex : Fin 3,
      frameᵀ *ᵥ (fun innerIndex => if innerIndex = standardIndex then (1:ℝ) else 0)
        = frame standardIndex := by
    intro standardIndex
    funext coordIndex
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have hcoordStd : ∀ (label : Fin 7) (standardIndex innerIndex : Fin 3),
      vecFamily label = frame standardIndex →
        coord label innerIndex = if innerIndex = standardIndex then (1:ℝ) else 0 := by
    intro label standardIndex innerIndex hlabel
    have hfun : coord label = fun inner => if inner = standardIndex then (1:ℝ) else 0 := by
      rw [hcoord]; simp only
      rw [hlabel, ← hframeRow standardIndex, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
    exact congrFun hfun innerIndex
  have hframeZero : vecFamily 0 = frame 0 := by rw [hframe]; rfl
  have hframeOne : vecFamily 1 = frame 1 := by rw [hframe]; rfl
  have hframeThree : vecFamily 3 = frame 2 := by rw [hframe]; rfl
  have hzeroFirst : coord 0 0 = 1 := by rw [hcoordStd 0 0 0 hframeZero, if_pos rfl]
  have hzeroSecond : coord 0 1 = 0 := by rw [hcoordStd 0 0 1 hframeZero, if_neg (by decide)]
  have hzeroThird : coord 0 2 = 0 := by rw [hcoordStd 0 0 2 hframeZero, if_neg (by decide)]
  have honeFirst : coord 1 0 = 0 := by rw [hcoordStd 1 1 0 hframeOne, if_neg (by decide)]
  have honeSecond : coord 1 1 = 1 := by rw [hcoordStd 1 1 1 hframeOne, if_pos rfl]
  have honeThird : coord 1 2 = 0 := by rw [hcoordStd 1 1 2 hframeOne, if_neg (by decide)]
  have hthreeFirst : coord 3 0 = 0 := by rw [hcoordStd 3 2 0 hframeThree, if_neg (by decide)]
  have hthreeSecond : coord 3 1 = 0 := by rw [hcoordStd 3 2 1 hframeThree, if_neg (by decide)]
  have hthreeThird : coord 3 2 = 1 := by rw [hcoordStd 3 2 2 hframeThree, if_pos rfl]
  -- the three coordinates killed by the frame-incident lines
  have hvalue012 : tripleBracket (coord 0) (coord 1) (coord 2) = coord 2 2 := by
    simp only [tripleBracket_eq, hzeroFirst, hzeroSecond, hzeroThird,
      honeFirst, honeSecond, honeThird]; ring
  have hvalue034 : tripleBracket (coord 0) (coord 3) (coord 4) = -(coord 4 1) := by
    simp only [tripleBracket_eq, hzeroFirst, hzeroSecond, hzeroThird,
      hthreeFirst, hthreeSecond, hthreeThird]; ring
  have hvalue135 : tripleBracket (coord 1) (coord 3) (coord 5) = coord 5 0 := by
    simp only [tripleBracket_eq, honeFirst, honeSecond, honeThird,
      hthreeFirst, hthreeSecond, hthreeThird]; ring
  have hvanishTwoThird : coord 2 2 = 0 := by
    rw [← hvalue012]; exact htransfer 0 1 2 hline012
  have hvanishFourSecond : coord 4 1 = 0 := by
    have hraw := htransfer 0 3 4 hline034
    rw [hvalue034] at hraw; linarith
  have hvanishFiveFirst : coord 5 0 = 0 := by
    rw [← hvalue135]; exact htransfer 1 3 5 hline135
  -- the four surviving relations
  have hvalue056 : tripleBracket (coord 0) (coord 5) (coord 6)
      = coord 5 1 * coord 6 2 - coord 5 2 * coord 6 1 := by
    simp only [tripleBracket_eq, hzeroFirst, hzeroSecond, hzeroThird]; ring
  have hvalue146 : tripleBracket (coord 1) (coord 4) (coord 6)
      = coord 4 2 * coord 6 0 - coord 4 0 * coord 6 2 := by
    simp only [tripleBracket_eq, honeFirst, honeSecond, honeThird]; ring
  have hvalue236 : tripleBracket (coord 2) (coord 3) (coord 6)
      = coord 2 1 * coord 6 0 - coord 2 0 * coord 6 1 := by
    simp only [tripleBracket_eq, hthreeFirst, hthreeSecond, hthreeThird]; ring
  have hvalue245 : tripleBracket (coord 2) (coord 4) (coord 5)
      = -(coord 2 0 * coord 4 2 * coord 5 1) - coord 2 1 * coord 4 0 * coord 5 2 := by
    simp only [tripleBracket_eq, hvanishTwoThird, hvanishFourSecond, hvanishFiveFirst]; ring
  have hrel056 : coord 5 1 * coord 6 2 - coord 5 2 * coord 6 1 = 0 := by
    rw [← hvalue056]; exact htransfer 0 5 6 hline056
  have hrel146 : coord 4 2 * coord 6 0 - coord 4 0 * coord 6 2 = 0 := by
    rw [← hvalue146]; exact htransfer 1 4 6 hline146
  have hrel236 : coord 2 1 * coord 6 0 - coord 2 0 * coord 6 1 = 0 := by
    rw [← hvalue236]; exact htransfer 2 3 6 hline236
  have hrel245 : coord 2 0 * coord 4 2 * coord 5 1 + coord 2 1 * coord 4 0 * coord 5 2 = 0 := by
    have hraw := htransfer 2 4 5 hline245
    rw [hvalue245] at hraw; linarith
  -- the five nonvanishing frame brackets
  have hvalue023 : tripleBracket (coord 0) (coord 2) (coord 3) = coord 2 1 := by
    simp only [tripleBracket_eq, hzeroFirst, hzeroSecond, hzeroThird,
      hthreeFirst, hthreeSecond, hthreeThird]; ring
  have hvalue134 : tripleBracket (coord 1) (coord 3) (coord 4) = coord 4 0 := by
    simp only [tripleBracket_eq, honeFirst, honeSecond, honeThird,
      hthreeFirst, hthreeSecond, hthreeThird]; ring
  have hvalue015 : tripleBracket (coord 0) (coord 1) (coord 5) = coord 5 2 := by
    simp only [tripleBracket_eq, hzeroFirst, hzeroSecond, hzeroThird,
      honeFirst, honeSecond, honeThird]; ring
  have hvalue016 : tripleBracket (coord 0) (coord 1) (coord 6) = coord 6 2 := by
    simp only [tripleBracket_eq, hzeroFirst, hzeroSecond, hzeroThird,
      honeFirst, honeSecond, honeThird]; ring
  have hvalue136 : tripleBracket (coord 1) (coord 3) (coord 6) = coord 6 0 := by
    simp only [tripleBracket_eq, honeFirst, honeSecond, honeThird,
      hthreeFirst, hthreeSecond, hthreeThird]; ring
  exact fanoCoordinates_impossible (coord 2 0) (coord 2 1) (coord 4 0) (coord 4 2)
    (coord 5 1) (coord 5 2) (coord 6 0) (coord 6 1) (coord 6 2)
    hrel056 hrel146 hrel236 hrel245
    (by rw [← hvalue023]; exact htransferNe 0 2 3 hbasis023)
    (by rw [← hvalue134]; exact htransferNe 1 3 4 hbasis134)
    (by rw [← hvalue015]; exact htransferNe 0 1 5 hbasis015)
    (by rw [← hvalue136]; exact htransferNe 1 3 6 hbasis136)
    (by rw [← hvalue016]; exact htransferNe 0 1 6 hbasis016)

/-! ## The stratum ledger and the hinge

A stratum is indexed by its LINE PATTERN — which ordered triples of labels are
dependent.  A design realizes the pattern when the brackets of distinct triples
vanish exactly on it.  Emptiness of the tie set on a stratum is
`StratumIsTieFree`, and the hinge follows from a COMPLETE list of patterns all
of whose strata are tie-free.

Both inputs are honest hypotheses.  `PatternListIsComplete` is the combinatorial
enumeration — it is not proved here, and proving it needs the classification of
simple rank-three matroids, not analysis.  `StratumIsTieFree` is the per-matroid
work; only the Fano instance and the `(4,3)` line instances are discharged
below. -/

/-- Which ordered triples of labels are DEPENDENT.  Bracket antisymmetry
(`tripleBracket_swapLeft`, `tripleBracket_swapRight`) means only slot-symmetric
patterns are realizable, and every pattern used below is slot-symmetric. -/
abbrev LinePattern (size : ℕ) : Type := Fin size → Fin size → Fin size → Prop

/-- The design's direction matroid is exactly the given pattern: among distinct
labels, a bracket vanishes precisely on the pattern's triples.  The equations are
the stratum's closed conditions; the inequations are its OPEN ones, so a stratum
is a locally closed set and emptiness here is compatible with an infimum living
on its boundary.  Note the pattern is pinned WITH its labels — see the header on
labelled strata versus isomorphism classes. -/
def HasLinePattern {size : ℕ} (D : WeightedDesign size 3) (pattern : LinePattern size) : Prop :=
  ∀ leftLabel midLabel rightLabel : Fin size,
    leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
      (atomBracket D leftLabel midLabel rightLabel = 0
        ↔ pattern leftLabel midLabel rightLabel)

/-- No design on this stratum is a tie. -/
def StratumIsTieFree {size : ℕ} (pattern : LinePattern size) : Prop :=
  ∀ D : WeightedDesign size 3, HasLinePattern D pattern → ¬ IsTie D

/-- The enumerated patterns exhaust the primitive designs: every design with no
parallel pair realizes one of them ON THE NOSE.  This is the matroid-classification
input in its LABELLED form, so a list satisfying it carries one entry per
labelling — 352 at `size = 6`, 8389 at `size = 7`.  Use
`PatternListIsCompleteUpToRelabel` for the one-per-isomorphism-class form.  Stated
and never assumed elsewhere. -/
def PatternListIsComplete (size : ℕ) (patterns : List (LinePattern size)) : Prop :=
  ∀ D : WeightedDesign size 3, IsPrimitiveDesign D →
    ∃ pattern ∈ patterns, HasLinePattern D pattern

/-- **The hinge from the labelled ledger.**  A complete list of primitive strata,
each tie-free, forces every tie to carry a parallel pair.  The conclusion is the
body of `Gtz.HingeHoldsAtSize size 3` (`Gtz.Reduction.SplitTransfer`) written
out, so a wiring module importing both obtains `HingeHoldsAtSize 6 3` and
`HingeHoldsAtSize 7 3` from this by `:=`.

Nothing is claimed about whether either hypothesis holds: at `size = 4` and
`size = 5` the conclusion is FALSE (`Gtz.tetraDesign_isTie`,
`Gtz.diamondDesign_isTie` are primitive ties), so any use of this theorem must
supply strata data that genuinely fails there. -/
theorem hingeHoldsAtSize_of_stratumLedger {size : ℕ} (patterns : List (LinePattern size))
    (hcomplete : PatternListIsComplete size patterns)
    (hstrataEmpty : ∀ pattern ∈ patterns, StratumIsTieFree pattern) :
    ∀ D : WeightedDesign size 3, IsTie D →
      ∃ (keptLabel dropLabel : Fin size) (ratio : ℝ),
        keptLabel ≠ dropLabel ∧ D.atom dropLabel = ratio • D.atom keptLabel := by
  intro D htie
  by_contra hnoParallelPair
  push Not at hnoParallelPair
  have hprimitive : IsPrimitiveDesign D := hnoParallelPair
  obtain ⟨pattern, hmem, hpattern⟩ := hcomplete D hprimitive
  exact hstrataEmpty pattern hmem D hpattern htie

/-! ## Relabelling: one representative per isomorphism class

`HasLinePattern` pins labels, so without this section a ledger would owe one
entry per LABELLING — 8741 across the hinge, not 32.  Relabelling a design
transports both `IsTie` and `HasLinePattern`, so `StratumIsTieFree` is closed
under composing a pattern with a permutation, and one representative per
isomorphism class suffices.  The design action `Gtz.relabelDesign` and the
domination transport are landed in `Gtz.Ties.SelectionObstruction`; what is added
here is the `IsTie` and `HasLinePattern` halves. -/

/-- Relabelling transports the bracket along the permutation. -/
theorem atomBracket_relabelDesign {m : ℕ} (D : WeightedDesign m 3)
    (relabel : Equiv.Perm (Fin m)) (leftLabel midLabel rightLabel : Fin m) :
    atomBracket (relabelDesign D relabel) leftLabel midLabel rightLabel
      = atomBracket D (relabel leftLabel) (relabel midLabel) (relabel rightLabel) := rfl

/-- Relabelling preserves subset cardinality. -/
theorem card_map_relabelEmbedding {m : ℕ} (relabel : Equiv.Perm (Fin m))
    (subset : Finset (Fin m)) :
    (subset.map relabel.toEmbedding).card = subset.card := Finset.card_map _

/-- Mapping by the inverse and then by the permutation is the identity on subsets. -/
theorem map_relabelSymm_then_relabel {m : ℕ} (relabel : Equiv.Perm (Fin m))
    (subset : Finset (Fin m)) :
    (subset.map relabel.symm.toEmbedding).map relabel.toEmbedding = subset := by
  ext label
  simp [Finset.mem_map_equiv]

/-- **`IsTie` is relabelling-invariant.**  Both halves — the existence of a
dominating `k`-subset and the absence of a strictly dominating one — transport
along the induced bijection of `k`-subsets. -/
theorem isTie_relabelDesign_iff {m k : ℕ} (D : WeightedDesign m k)
    (relabel : Equiv.Perm (Fin m)) :
    IsTie (relabelDesign D relabel) ↔ IsTie D := by
  constructor
  · rintro ⟨⟨dominatingSubset, hcard, hdominates⟩, hnoStrict⟩
    refine ⟨⟨dominatingSubset.map relabel.toEmbedding,
      by rw [card_map_relabelEmbedding]; exact hcard,
      (dominates_relabelDesign_iff D relabel dominatingSubset).mp hdominates⟩, ?_⟩
    intro candidate hcandidate hposdef
    refine hnoStrict (candidate.map relabel.symm.toEmbedding)
      (by rw [card_map_relabelEmbedding]; exact hcandidate) ?_
    rw [subsetSum_relabelDesign, map_relabelSymm_then_relabel]
    exact hposdef
  · rintro ⟨⟨dominatingSubset, hcard, hdominates⟩, hnoStrict⟩
    refine ⟨⟨dominatingSubset.map relabel.symm.toEmbedding,
      by rw [card_map_relabelEmbedding]; exact hcard, ?_⟩, ?_⟩
    · rw [dominates_relabelDesign_iff, map_relabelSymm_then_relabel]; exact hdominates
    · intro candidate hcandidate hposdef
      rw [subsetSum_relabelDesign] at hposdef
      exact hnoStrict (candidate.map relabel.toEmbedding)
        (by rw [card_map_relabelEmbedding]; exact hcandidate) hposdef

/-- A design realizing a RELABELLED pattern becomes, after the inverse
relabelling, a design realizing the pattern itself. -/
theorem hasLinePattern_relabelDesign_symm {size : ℕ} (D : WeightedDesign size 3)
    (pattern : LinePattern size) (relabel : Equiv.Perm (Fin size))
    (hpattern : HasLinePattern D
      (fun leftLabel midLabel rightLabel =>
        pattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel))) :
    HasLinePattern (relabelDesign D relabel.symm) pattern := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  rw [atomBracket_relabelDesign]
  have hshifted := hpattern (relabel.symm leftLabel) (relabel.symm midLabel)
    (relabel.symm rightLabel)
    (fun hequal => hleftMid (relabel.symm.injective hequal))
    (fun hequal => hleftRight (relabel.symm.injective hequal))
    (fun hequal => hmidRight (relabel.symm.injective hequal))
  simpa only [Equiv.apply_symm_apply] using hshifted

/-- **Tie-freeness is a property of the isomorphism class.**  If a stratum is
tie-free then so is every relabelling of it, so a ledger may carry one
representative per class instead of one entry per labelling. -/
theorem stratumIsTieFree_comp_relabel {size : ℕ} (pattern : LinePattern size)
    (relabel : Equiv.Perm (Fin size)) (hfree : StratumIsTieFree pattern) :
    StratumIsTieFree (fun leftLabel midLabel rightLabel =>
      pattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) :=
  fun D hpattern htie =>
    hfree (relabelDesign D relabel.symm)
      (hasLinePattern_relabelDesign_symm D pattern relabel hpattern)
      ((isTie_relabelDesign_iff D relabel.symm).mpr htie)

/-- The enumeration UP TO RELABELLING: every primitive design realizes some
listed pattern after some permutation of its labels.  A list satisfying this
carries one entry per isomorphism class — nine at `size = 6`, twenty-three at
`size = 7`.  Stated and never assumed elsewhere. -/
def PatternListIsCompleteUpToRelabel (size : ℕ) (patterns : List (LinePattern size)) : Prop :=
  ∀ D : WeightedDesign size 3, IsPrimitiveDesign D →
    ∃ pattern ∈ patterns, ∃ relabel : Equiv.Perm (Fin size),
      HasLinePattern D (fun leftLabel midLabel rightLabel =>
        pattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel))

/-- **The hinge from the isomorphism-class ledger.**  Same conclusion as
`hingeHoldsAtSize_of_stratumLedger`, but the completeness hypothesis now ranges
over classes rather than labellings, so the ledger it consumes has thirty-two
entries at the hinge rather than eight thousand seven hundred and forty-one.
`stratumIsTieFree_comp_relabel` is what closes the gap. -/
theorem hingeHoldsAtSize_of_relabelLedger {size : ℕ} (patterns : List (LinePattern size))
    (hcomplete : PatternListIsCompleteUpToRelabel size patterns)
    (hstrataEmpty : ∀ pattern ∈ patterns, StratumIsTieFree pattern) :
    ∀ D : WeightedDesign size 3, IsTie D →
      ∃ (keptLabel dropLabel : Fin size) (ratio : ℝ),
        keptLabel ≠ dropLabel ∧ D.atom dropLabel = ratio • D.atom keptLabel := by
  intro D htie
  by_contra hnoParallelPair
  push Not at hnoParallelPair
  have hprimitive : IsPrimitiveDesign D := hnoParallelPair
  obtain ⟨pattern, hmem, relabel, hpattern⟩ := hcomplete D hprimitive
  exact stratumIsTieFree_comp_relabel pattern relabel (hstrataEmpty pattern hmem) D hpattern htie

/-- The Fano plane `PG(2,2)` as a line pattern on seven labels: shifting to
`1..7` and reading the labels as nonzero bit vectors of `𝔽₂³`, a triple is a line
exactly when the three bit vectors sum to zero.  The encoding is manifestly
symmetric in the three slots. -/
abbrev fanoLinePattern : LinePattern 7 := fun leftLabel midLabel rightLabel =>
  (leftLabel.val + 1) ^^^ (midLabel.val + 1) ^^^ (rightLabel.val + 1) = 0

/-- **No `(7,3)` design realizes the Fano plane.**  The stratum is empty of
designs, so a fortiori empty of ties. -/
theorem not_hasLinePattern_fano (D : WeightedDesign 7 3) :
    ¬ HasLinePattern D fanoLinePattern := by
  intro hpattern
  exact fanoBrackets_impossible D.atom
    ((hpattern 0 1 2 (by decide) (by decide) (by decide)).mpr (by decide))
    ((hpattern 0 3 4 (by decide) (by decide) (by decide)).mpr (by decide))
    ((hpattern 0 5 6 (by decide) (by decide) (by decide)).mpr (by decide))
    ((hpattern 1 3 5 (by decide) (by decide) (by decide)).mpr (by decide))
    ((hpattern 1 4 6 (by decide) (by decide) (by decide)).mpr (by decide))
    ((hpattern 2 3 6 (by decide) (by decide) (by decide)).mpr (by decide))
    ((hpattern 2 4 5 (by decide) (by decide) (by decide)).mpr (by decide))
    (fun hvanish => (by decide : ¬ fanoLinePattern 0 1 3)
      ((hpattern 0 1 3 (by decide) (by decide) (by decide)).mp hvanish))
    (fun hvanish => (by decide : ¬ fanoLinePattern 0 1 5)
      ((hpattern 0 1 5 (by decide) (by decide) (by decide)).mp hvanish))
    (fun hvanish => (by decide : ¬ fanoLinePattern 0 1 6)
      ((hpattern 0 1 6 (by decide) (by decide) (by decide)).mp hvanish))
    (fun hvanish => (by decide : ¬ fanoLinePattern 0 2 3)
      ((hpattern 0 2 3 (by decide) (by decide) (by decide)).mp hvanish))
    (fun hvanish => (by decide : ¬ fanoLinePattern 1 3 4)
      ((hpattern 1 3 4 (by decide) (by decide) (by decide)).mp hvanish))
    (fun hvanish => (by decide : ¬ fanoLinePattern 1 3 6)
      ((hpattern 1 3 6 (by decide) (by decide) (by decide)).mp hvanish))

/-- **The Fano stratum is tie-free** — the first entry of the `m = 7` ledger,
kernel-checked.  Via `stratumIsTieFree_comp_relabel` this covers all thirty
labellings of `F₇`, i.e. the whole isomorphism class. -/
theorem stratumIsTieFree_fano : StratumIsTieFree fanoLinePattern :=
  fun D hpattern _ => not_hasLinePattern_fano D hpattern

/-! ## The `(4,3)` rung in ledger vocabulary

At corank one every `k`-subset of a tie dominates
(`Gtz.corankOne_isTie_dominates`), so no triple can be dependent: a `(4,3)` tie
has all four triples as bases, i.e. direction matroid `U(3,4)`.  In pattern
language, every pattern carrying a line is tie-free, and only the empty pattern
survives. -/

/-- **A `(4,3)` tie has no dependent triple.** -/
theorem tieAtFourThree_atomBracket_ne_zero (D : WeightedDesign 4 3) (htie : IsTie D)
    {leftLabel midLabel rightLabel : Fin 4} (hleftMid : leftLabel ≠ midLabel)
    (hleftRight : leftLabel ≠ rightLabel) (hmidRight : midLabel ≠ rightLabel) :
    atomBracket D leftLabel midLabel rightLabel ≠ 0 := by
  have hcard : ({leftLabel, midLabel, rightLabel} : Finset (Fin 4)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hleftMid, hleftRight]),
      Finset.card_insert_of_notMem (by simp [hmidRight]), Finset.card_singleton]
  exact atomBracket_ne_zero_of_dominates D leftLabel midLabel rightLabel
    (corankOne_isTie_dominates (k := 3) (by omega) D htie hcard)

/-- **Every `(4,3)` stratum with a line is tie-free.**  Of the two simple
rank-three matroids on four points only the uniform one `U(3,4)` carries a tie,
now in the vocabulary the ledger is written in. -/
theorem stratumIsTieFree_fourThree_of_line (pattern : LinePattern 4)
    {leftLabel midLabel rightLabel : Fin 4} (hleftMid : leftLabel ≠ midLabel)
    (hleftRight : leftLabel ≠ rightLabel) (hmidRight : midLabel ≠ rightLabel)
    (hline : pattern leftLabel midLabel rightLabel) : StratumIsTieFree pattern := by
  intro D hpattern htie
  exact tieAtFourThree_atomBracket_ne_zero D htie hleftMid hleftRight hmidRight
    ((hpattern leftLabel midLabel rightLabel hleftMid hleftRight hmidRight).mpr hline)

/-! ## Two controls on the vocabulary

`HasLinePattern` is an iff over every distinct triple, so it is exactly the kind
of predicate that can be accidentally unsatisfiable — a slot-indexing or
symmetry bug would make every line-carrying `StratumIsTieFree` vacuously true
and nothing downstream would notice.  Both directions are therefore witnessed by
explicit designs whose brackets are COMPUTED here.

The first control is the line-FREE pattern at four labels, realized by the
tetrahedron; the second is a pattern WITH lines, realized by a design carrying a
parallel pair.  The second one is also the sharp reading of
`stratumIsTieFree_fourThree_of_line`: that stratum is inhabited by designs and
empty of ties, so the emptiness statement is about a nonempty set. -/

/-- **The tetrahedron's four brackets are nonzero**, computed directly from the
vertex coordinates.  Independent of `Gtz.corankOne_isTie_dominates` and of
everything else about ties, so the non-vacuity witness below does not rest on the
machinery it is meant to certify. -/
theorem tetraDesign_atomBracket_ne_zero
    {leftLabel midLabel rightLabel : Fin 4} (hleftMid : leftLabel ≠ midLabel)
    (hleftRight : leftLabel ≠ rightLabel) (hmidRight : midLabel ≠ rightLabel) :
    atomBracket tetraDesign leftLabel midLabel rightLabel ≠ 0 := by
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    simp_all [atomBracket, tripleBracket_eq, tetraDesign, tetraAtom] <;>
    norm_num

/-- **The vocabulary is inhabited.**  The tetrahedron realizes the line-free
pattern on four labels — the uniform matroid `U(3,4)` — so `HasLinePattern` is
not an empty predicate and the emptiness statements above have content. -/
theorem tetraDesign_hasUniformLinePattern :
    HasLinePattern tetraDesign (fun _ _ _ => False) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  exact ⟨fun hvanish =>
      tetraDesign_atomBracket_ne_zero hleftMid hleftRight hmidRight hvanish,
    fun hfalse => hfalse.elim⟩

/-- **The `(4,3)` rung is sharp in both directions.**  The line-free stratum is
NOT tie-free: `Gtz.tetraDesign` sits on it.  So exactly one of the two simple
rank-three strata on four labels carries a tie, and the hinge's conclusion fails
at `m = 4`. -/
theorem not_stratumIsTieFree_fourThree_uniform :
    ¬ StratumIsTieFree (size := 4) (fun _ _ _ => False) := fun hstratumEmpty =>
  hstratumEmpty tetraDesign tetraDesign_hasUniformLinePattern tetraDesign_isTie

/-- Two proportional atoms on the first axis, then the two remaining axes.  Every
atom is nonzero and the direction matroid has exactly the lines through the
parallel pair. -/
def parallelPairAtom : Fin 4 → Fin 3 → ℝ :=
  ![![1, 0, 0], ![2, 0, 0], ![0, 2, 0], ![0, 0, 2]]

/-- A rational `(4,3)` design with a parallel pair: masses `1/3, 2/3, 1, 1`
resolve the identity and the weights sum to one. -/
noncomputable def parallelPairDesign : WeightedDesign 4 3 where
  atom := parallelPairAtom
  weight := ![1/3, 1/6, 1/4, 1/4]
  weight_pos := by intro label; fin_cases label <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_four, smul_eq_mul, parallelPairAtom, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- The dependent triples of `parallelPairDesign`: exactly those meeting both
labels of the parallel pair. -/
abbrev parallelPairLinePattern : LinePattern 4 := fun leftLabel midLabel rightLabel =>
  (leftLabel = 0 ∨ midLabel = 0 ∨ rightLabel = 0) ∧
    (leftLabel = 1 ∨ midLabel = 1 ∨ rightLabel = 1)

/-- **A pattern WITH lines is realized.**  All twenty-four distinct ordered
triples are checked: the twelve meeting both `0` and `1` have vanishing bracket,
the twelve others have bracket `±4` or `±8`. -/
theorem parallelPairDesign_hasLinePattern :
    HasLinePattern parallelPairDesign parallelPairLinePattern := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    simp_all [atomBracket, tripleBracket_eq, parallelPairDesign, parallelPairAtom] <;>
    decide

/-- **The over-constrained-builder control.**  A line-carrying stratum is
inhabited by designs AND empty of ties.  The first half rules out the failure
mode where an indexing bug makes `HasLinePattern` unsatisfiable and every
line-carrying emptiness claim vacuous; the second is
`stratumIsTieFree_fourThree_of_line` at that pattern.  Together they say the
`(4,3)` line strata are genuine nonempty sets carrying no tie — which is what
the ledger's entries are supposed to assert. -/
theorem parallelPairStratum_isNonempty_and_tieFree :
    HasLinePattern parallelPairDesign parallelPairLinePattern ∧
      StratumIsTieFree parallelPairLinePattern :=
  ⟨parallelPairDesign_hasLinePattern,
    stratumIsTieFree_fourThree_of_line parallelPairLinePattern
      (leftLabel := 0) (midLabel := 1) (rightLabel := 2)
      (by decide) (by decide) (by decide) (by decide)⟩

end Gtz

/-
# Attacking the twenty-nine open tie-freeness classes: what the deflation route
# reaches, and the exact wall it stops at

`Gtz.Design.StratumEmptinessLedger` leaves TWENTY-NINE of the thirty-two
primitive rank-three isomorphism classes open for tie-freeness — eight of nine
at six points, twenty-one of twenty-three at seven.  This file attacks them and
DISCHARGES NONE.  What it lands instead is a strict sharpening of the ledger's
own share bracket, a new combinatorial necessary condition on the direction
matroid of a tie, a new quantitative ceiling on coplanar families, and a
theorem-ization of the structural obstruction that the near-pencil transport's
header states informally.  Read the honesty section before quoting anything.

## PROVED here, kernel-checked, unconditional unless the statement says otherwise

* `sum_weighted_atomPairing` — Parseval as a BILINEAR form,
  `Sum_c t_c (g_c . y)(g_c . z) = y . z`.  The polarized companion of the landed
  `Gtz.parseval_weighted_sum_sq`.
* `eq_of_forall_dotProduct_eq`, `eq_smul_normal_of_orthogonal_annihilates` —
  two elementary separation facts used to turn "annihilates a hyperplane" into
  "is a multiple of the normal", with no plane frame and no spectral input.
* **`dotProduct_atom_pole_eq_zero_of_share_eq_one`** — the CONVERSE of the
  shipped `Gtz.soleOffPlane_share_eq_one`.  If one atom's share `t_d |g_d|^2`
  equals one, then EVERY other atom is orthogonal to it.  So share one is not a
  numerical coincidence: it is exactly the near-pencil configuration, with the
  pole's own atom serving as the normal.  `share_eq_one_iff_forall_dotProduct_eq_zero`
  packages both directions.
* **`share_lt_one_of_isTie`** — the headline.  At a tie of a rank-three design
  with at least two atoms, EVERY share is STRICTLY below one.  Unconditional:
  it consumes no instance of `GtzWeighted` at rank three, only the landed
  `Gtz.gtz_rank_two` inside `Gtz.not_isTie_of_soleOffPlane`.  This strictly
  sharpens `Gtz.share_bracket_of_isTie`, whose upper end is the vacuous
  per-atom ceiling `Gtz.weighted_leverage_le_one`, into the half-open bracket
  `[t_c, 1)` — see `share_bracket_strict_of_isTie_sixThree`.
* **`exists_deflatedGapBound_of_isTie`** — the operational payoff: at a tie the
  share hypothesis of `Gtz.exists_deflatedGapBound` is automatic, so deflation
  is available at EVERY label with no side condition to discharge.
* **`atomBracket_ne_zero_of_deflatedGapBound`** — the deflated triple is a
  BASIS.  A dependent triple's common orthogonal direction makes the
  transported gap at least `1/t_d` times the squared length, and Cauchy-Schwarz
  turns that into `t_d |g_d|^2 >= 1`, which the headline forbids.
* **`exists_basisTriple_avoiding_of_isTie`** and
  **`exists_basisTriple_avoiding_of_isTie_sixThree`** — at a `(6,3)` tie, for
  EVERY label there is a basis triple avoiding it.  Unconditionally: the input
  is `Gtz.gtzWeighted_of_le_five`.  Combinatorially: the direction matroid of a
  tie has rank three after deleting any single point.
* `stratumIsTieFree_of_blindLabel` — the general discharge rule that condition
  yields, and `stratumIsTieFree_nearPencil_viaBlindLabel_sixThree`, its
  six-point near-pencil instance.  That instance is NOT a third independent
  certificate: it routes through `share_lt_one_of_isTie` and hence through
  `Gtz.not_isTie_of_soleOffPlane`, and at a near pencil the pole's share is
  exactly one so the deflation step is never reached.  It is a re-derivation
  through a general interface; the rule, not the instance, is the deliverable.
* `exists_distinctTriple_avoiding`, `not_blindLabel_lineFree` — the CONTROL that
  measures how far that rule reaches, and the answer is: nowhere new.  See the
  wall section.
* **`coplanarWeightedLeverage_le_two`** — a new quantitative ceiling: for any
  family of atoms sharing a nonzero orthogonal direction,
  `Sum t_c |g_c|^2 <= 2`.  Proof is two lines of Parseval plus Cauchy-Schwarz,
  with no plane frame, no trace basis change and no eigenvalue.
  `one_le_offPlaneWeightedLeverage` is the equivalent complementary form.
* **`two_le_card_offPlane_of_isTie`** — at a tie no plane holds all but at most
  one atom.  A second derivation of the near-pencil exclusion whose own final
  step is purely quantitative, but NOT logically independent of the rank-two
  transport: it consumes the headline, which routes through
  `Gtz.not_isTie_of_soleOffPlane` into `Gtz.exists_posDef_of_soleOffPlane` — the
  transport itself — and through that into `Gtz.gtz_rank_two`.
* `exists_lineNormal_of_hasLinePattern`, **`two_le_card_offLine_of_isTie`** — the
  same ceiling at PATTERN level.  A line of the pattern supplies its own nonzero
  normal (the off-line witness triple's non-dependence is what certifies it, as
  in `Gtz.sharedNormal_of_hasNearPencilLinePattern`), so every line of a tie's
  pattern misses at least two labels.  This is the wall stated as a theorem: a
  class falls to it only if some line misses at most one point, and a
  `(size - 1)`-point line IS a near pencil.
* **`offPlanePair_combination_eq_normal`** — the two-pole analogue of
  `Gtz.soleOffPlane_normal_eq_smul_pole`: with exactly two atoms off a plane,
  `t_p (g_p . w) g_p + t_q (g_q . w) g_q = w` ON THE NOSE.
  `offPlanePair_normalSquare_eq` is its diagonal
  (`t_p (g_p . w)^2 + t_q (g_q . w)^2 = w . w`) and
  `offPlanePair_projection_antiparallel` its off-diagonal: the two poles'
  IN-PLANE components are exactly antiparallel.
* **`exists_planarProbe_of_offPlanePair_of_isPrimitive`** — the punchline of
  that section, and the theorem-ization of a claim the near-pencil transport's
  header makes in prose.  At a primitive design neither pole is parallel to the
  normal, so the compression `Gtz.compressedDesign` kills NEITHER of them, so
  the planar weight is the full one and the deflation margin
  `Gtz.poleDeflation` that makes `Gtz.exists_posDef_of_soleOffPlane` strict does
  not exist.  The transport's specialness to ONE off-plane atom is now a
  theorem, not a remark.

## WHERE THE ARGUMENT BROKE — the named wall

The deflation route produces exactly one combinatorial condition on the
direction matroid of a tie: **every single-point deletion still has rank
three** (`exists_basisTriple_avoiding_of_isTie_sixThree`).  Against the
thirty-two-class ledger that condition fails on exactly the class where all
but one point are collinear — the NEAR PENCIL, already discharged three ways.
It discharges NOTHING new, and `not_blindLabel_lineFree` shows it is inert on
the line-free classes.  The reason is structural and worth recording so the
next campaign does not re-walk it: deleting one point from a simple rank-three
matroid on six or seven points drops the rank only when the survivors are
collinear, and a class with a `(size - 1)`-point line is a near pencil by
definition.  So single-deletion rank is a DEAD LEVER.

The same wall appears from the quantitative side.  `coplanarWeightedLeverage_le_two`
and the trace identity `Gtz.sum_weighted_leverage` are, together, exactly the
statement `Sum_{c not in L} t_c |g_c|^2 >= 1`; combined with the headline
`s_c < 1` this yields "at least two atoms off every line" and nothing more.
Worked out by hand on the covering configurations of the ledger, the bookkeeping
is inert: two lines meeting in one point give `s_z <= 1`, which is the vacuous
ceiling again; `M(K4)`'s four lines give the exact identity `Sum_L delta_L = 2`
with `delta_L = Sum_{c not in L} t_c |P_L g_c|^2`, which is satisfiable; the
Fano's seven lines give `Sum_L delta_L = 5`, likewise satisfiable.  No
inclusion-exclusion over lines closes any class, because every such count is a
consequence of the single trace identity.

The two-pole section says why the near-pencil mechanism cannot be rescaled to
the four classes that have exactly two atoms off a maximal line — six-point
`[0123]` and `[0123,045]`, seven-point `[01234]` and `[01234,056]`.  With one
pole the compression sends its atom to zero and the surviving planar weight is
`1 - t_pole < 1`, which is the entire margin.  With two poles
`exists_planarProbe_of_offPlanePair_of_isPrimitive` proves both in-plane
components are NONZERO, so the compressed design keeps total weight one and
`Gtz.gtz_rank_two` returns `>= I` with no margin at all.

That this is not a proof-technique artifact was checked by hand, OUTSIDE Lean,
and is recorded as such.  Take the orthonormal frame `(u, v, w)` with `w` the
line's normal and `u` the poles' shared in-plane direction, so
`g_p = (alpha, 0, a)`, `g_q = (beta, 0, b)` and `g_c = (x_c, y_c, 0)` for `c` on
the line.  Parseval reads
`t_p alpha a + t_q beta b = 0`, `t_p a^2 + t_q b^2 = 1`,
`Sum_L t_c y_c^2 = 1`, `Sum_L t_c x_c y_c = 0` and
`t_p alpha^2 + t_q beta^2 + Sum_L t_c x_c^2 = 1`.  In the symmetric slice
`t_p = t_q = t`, `beta = -alpha`, `b = a` the mixed entry `alpha a + beta b`
vanishes, the `w` block decouples at `2 a^2 - 1 = 1/t - 1 > 0`, and the triple
`{p, q, c}` has positive-definite gap exactly when the remaining in-plane
`2 x 2` block is positive definite, i.e. when BOTH `y_c^2 > 1` and
`(2 alpha^2 + x_c^2 - 1)(y_c^2 - 1) > x_c^2 y_c^2`.  The diagonal condition is
not redundant: the determinant alone is also positive on the negative-definite
sign.  Writing `e = 2 alpha^2 - 1`, the determinant condition rearranges to
`x_c^2 < e (y_c^2 - 1)` exactly, so it FAILS at every line label as soon as
`x_c^2 >= e (y_c^2 - 1)` for all `c`.  Summing that pointwise family against the
weights yields `e <= (1 - t)/(3 t)` — but note the direction: summation gives
only a NECESSARY condition on `e`, not the realizability of a configuration, so
the threshold alone does not exhibit one.  What does exhibit one is the slice
`e = 0` (`alpha^2 = 1/2`), where the determinant condition reads `x_c^2 < 0` and
therefore fails at EVERY line label whatever the line carries.  That slice is
realized exactly: on six points with `t_c = 1/6` throughout, poles
`(1/sqrt 2, 0, sqrt 3)` and `(-1/sqrt 2, 0, sqrt 3)` and the four line atoms
`r_c (cos theta_c, sin theta_c, 0)` at `theta = 30, 60, 120, 150` degrees with
`r^2 = 9/4, 13/4, 13/4, 9/4`, Parseval holds on the nose and every `x_c` is
nonzero, so no triple through both poles is a strict dominator and the matroid is
the `[0123]` class.  A companion rational witness for the hypothesis bundle of
`exists_planarProbe_of_offPlanePair_of_isPrimitive` alone — atoms
`(1,0,2), (-1,0,2), (2,0,0), (0,4/3,0)` with weights `1/8, 1/8, 3/16, 9/16` — is
Parseval-exact and primitive, confirming that section is not vacuous.
So the two-pole triple is NOT always a strict dominator; a proof for those four
classes must range over triples carrying TWO atoms on the line, where the
rank-two transport gives a pair inside the plane but the third atom's `w`
component is unconstrained.  That is the exact remaining gap.

## Honest ledger arithmetic

Discharged by this file: ZERO of the twenty-nine.  The ledger fraction is
unchanged at THREE of thirty-two mechanized — `F7` at seven points, and the two
near pencils `q6m3` and `q7m4` — i.e. ONE of nine at six points and TWO of
twenty-three at seven.  What this file adds is not an entry but a narrowing:
every open entry may now additionally assume `t_c |g_c|^2 < 1` at every atom
(strictly, not just `<= 1`), `Sum_{c in L} t_c |g_c|^2 <= 2` on every line `L`,
and a basis triple avoiding any nominated label.  The six-point near-pencil
entry gains a re-derivation through a general rule, which is NOT an independent
third certificate — see `stratumIsTieFree_nearPencil_viaBlindLabel_sixThree`.

## The canonical-index dictionary, which must be fixed before any transcription

The campaign's `q`-names and the published canonical enumeration
(OEIS A058731; Blackburn-Crapo-Higgs, *A catalogue of combinatorial
geometries*, Math. Comp. 27 (1973) 155-166; machine-readable as Matsumoto's
matroid database, exposed by `matroids.AllMatroids(n, 3, 'simple')`) index the
classes DIFFERENTLY, and the mismatch is a trap because it is nearly a
transposition:

  five points   `M(K4 - e)`, the diamond           = `simple_n05_r03_#2`
  six points    near pencil `q6m3`                 = `simple_n06_r03_#8`  (NOT #3)
  six points    `M(K4)` = `q6m8`                   = `simple_n06_r03_#5`  (NOT #8)
  seven points  near pencil `q7m4`                 = `simple_n07_r03_#22` (NOT #4)
  seven points  non-Fano `F7-minus` = `q7m21`      = `simple_n07_r03_#12` (NOT #21)
  seven points  Fano `F7` = `q7m22`                = `simple_n07_r03_#13` (NOT #22)

Note the near-collision: `q7m22` is the FANO while canonical `#22` is the NEAR
PENCIL.  A ledger transcribed from the canonical list under the `q`-names would
silently swap a discharged class for an open one.  No `List (LinePattern 6)` or
`List (LinePattern 7)` is introduced here, so nothing in this file depends on
the dictionary; it is recorded because the next lane will need it.

TRUST WARNING on the six index numbers above, which the honesty ledger of this
file originally failed to flag: they are an EXTERNAL TRANSCRIPTION and were not
re-derived against the database in this lane, nor is anything in the repository
able to check them.  Do not treat them as verified.  The next lane must
regenerate the mapping from the database itself before transcribing any pattern
list, and the argument FOR fixing the dictionary — that `q7m22` and canonical
`#22` denote different classes — is exactly the reason a wrong entry here would
be invisible.

## REFUTED — two suggestions this lane was handed, and why they are dead

1. "Try the uniform matroids `U(3,6)` and `U(3,7)` first, they should be the
   most rigid."  BACKWARDS.  On a line-free stratum every distinct triple is a
   basis, so the pruning rule `Gtz.not_dominates_of_atomBracket_eq_zero`
   excludes NO triple and the deflation condition above is satisfied by every
   label — `not_blindLabel_lineFree` proves the latter.  The uniform classes
   carry the LEAST structural input of the thirty-two, and they are exactly
   where the ties live one and two sizes down:
   `Gtz.not_stratumIsTieFree_fourThree_uniform` is `U(3,4)`, realized by
   `Gtz.tetraDesign`.  `U(3,6)` and `U(3,7)` are the hardest entries, not the
   easiest.
2. "Duality-transport a proof from one class to its dual to close several at
   once."  Already refuted by the ledger's own measurement, which this file does
   not repeat and does not contradict: at six points the Naimark involution
   FIXES six of the nine classes and sends the other three to NON-SIMPLE
   matroids, so there is no dual pair to exploit; at seven points it exports to
   rank four and off this rung.  A `StratumIsTieFreeAmongHeavy` duality
   transport would therefore be a theorem with no instances.

## CITED, not reproved here

* `Gtz.not_isTie_of_soleOffPlane`, `Gtz.exists_posDef_of_soleOffPlane`,
  `Gtz.nearPencilLinePattern`, `Gtz.poleDeflation`
  (`Gtz.Design.NearPencilStrictDomination`) — the near-pencil transport whose
  entry hypothesis the headline supplies for free, and whose margin the two-pole
  section proves cannot exist with two poles.
* `Gtz.soleOffPlane_share_eq_one`, `Gtz.atomBracket`, `Gtz.LinePattern`,
  `Gtz.HasLinePattern`, `Gtz.StratumIsTieFree`, `Gtz.IsPrimitiveDesign`,
  `Gtz.hasCommonOrthogonal_of_atomBracket_eq_zero`
  (`Gtz.Design.PrimitiveTightClassification`).
* `Gtz.exists_deflatedGapBound`, `Gtz.share_bracket_of_isTie`,
  `Gtz.leverage_one_le_of_isTie_sixThree` (`Gtz.Design.StratumEmptinessLedger`)
  — the deflation transport this file feeds, and the floor it sits against.
* `Gtz.parseval_weighted_sum_sq` (`Gtz.Reduction.RayleighCertificate`),
  `Gtz.sum_weighted_leverage`, `Gtz.weight_lt_one` (`Gtz.Core.Sanity`),
  `Gtz.weighted_leverage_le_one`, `Gtz.leverageOf_eq_dotProduct`
  (`Gtz.Design.LeverageBound`), `Gtz.dotProduct_sq_le_mul`,
  `Gtz.dotProduct_self_pos` (`Gtz.LinAlg.PsdKit`),
  `Gtz.vecMulVec_mulVec_eq` (`Gtz.LinAlg.SchurRankOne`),
  `Gtz.dotProduct_subsetSum_mulVec_of_finset`, `Gtz.HasCommonOrthogonal`
  (`Gtz.Ties.TotalTieCorankOne`), `Gtz.gtzWeighted_of_le_five`
  (`Gtz.Reduction.Reductions`).
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.Design.LeverageBound
import Gtz.Design.PrimitiveTightClassification
import Gtz.Design.NearPencilStrictDomination
import Gtz.Design.StratumEmptinessLedger
import Gtz.Reduction.RayleighCertificate
import Gtz.Reduction.Reductions
import Gtz.Ties.TotalTieCorankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## Two elementary separation facts

Both are used to promote "this vector pairs correctly against every probe" to
"this vector IS that vector", with no plane frame, no basis change and no
spectral input.  They are the only linear algebra the rest of the file needs
beyond Parseval and Cauchy-Schwarz. -/

/-- **Pairing determines the vector.**  Two vectors agreeing against every probe
are equal; the probe that settles it is their difference.

Kept `private`: the PUBLIC owner of this name is
`Gtz.eq_of_forall_dotProduct_eq` in `Gtz.Quantitative.CriticalQuadric`, which
proves the same statement by evaluating at `Pi.single`.  That module is not in
this file's import graph and importing it would pull the whole seven-three
critical-quadric layer in for a four-line lemma, so the duplicate stays local
rather than becoming a second live global. -/
private theorem eq_of_forall_dotProduct_eq {dimension : ℕ}
    {leftVec rightVec : Fin dimension → ℝ}
    (hpair : ∀ probeVec : Fin dimension → ℝ, leftVec ⬝ᵥ probeVec = rightVec ⬝ᵥ probeVec) :
    leftVec = rightVec := by
  have hzero : (leftVec - rightVec) ⬝ᵥ (leftVec - rightVec) = 0 := by
    rw [sub_dotProduct, hpair (leftVec - rightVec)]
    ring
  exact eq_of_sub_eq_zero (dotProduct_self_eq_zero.mp hzero)

/-- **Annihilating a hyperplane means being normal to it.**  A vector killing
every probe orthogonal to `normalVec` is a multiple of `normalVec`, with the
multiplier exhibited. -/
theorem eq_smul_normal_of_orthogonal_annihilates {dimension : ℕ}
    {vec normalVec : Fin dimension → ℝ} (hnormalNe : normalVec ≠ 0)
    (hannihilates : ∀ probeVec : Fin dimension → ℝ,
      probeVec ⬝ᵥ normalVec = 0 → vec ⬝ᵥ probeVec = 0) :
    vec = ((normalVec ⬝ᵥ vec) / (normalVec ⬝ᵥ normalVec)) • normalVec := by
  have hnormPos : 0 < normalVec ⬝ᵥ normalVec := dotProduct_self_pos hnormalNe
  refine eq_of_forall_dotProduct_eq fun probeVec => ?_
  have hprojOrtho :
      (probeVec - ((normalVec ⬝ᵥ probeVec) / (normalVec ⬝ᵥ normalVec)) • normalVec)
        ⬝ᵥ normalVec = 0 := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul,
      dotProduct_comm probeVec normalVec]
    field_simp
    ring
  have hkill := hannihilates _ hprojOrtho
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul] at hkill
  rw [smul_dotProduct, smul_eq_mul, dotProduct_comm normalVec vec]
  have hvecProbe : vec ⬝ᵥ probeVec
      = ((normalVec ⬝ᵥ probeVec) / (normalVec ⬝ᵥ normalVec)) * (vec ⬝ᵥ normalVec) := by
    linarith [hkill]
  rw [hvecProbe]
  field_simp

/-! ## Parseval as a bilinear form

`Gtz.parseval_weighted_sum_sq` is the diagonal.  The full bilinear identity is
what the two-pole section needs, and it is the same one-line argument with the
probe split into two slots. -/

/-- **Parseval, bilinear.**  The weighted atoms reproduce every inner product:
`Sum_c t_c (g_c . y)(g_c . z) = y . z`. -/
theorem sum_weighted_atomPairing (D : WeightedDesign m k) (leftVec rightVec : Fin k → ℝ) :
    (∑ label, D.weight label * ((D.atom label ⬝ᵥ leftVec) * (D.atom label ⬝ᵥ rightVec)))
      = leftVec ⬝ᵥ rightVec := by
  have hkey : leftVec ⬝ᵥ ((∑ label, D.weight label • atomMatrix (D.atom label)) *ᵥ rightVec)
      = ∑ label, D.weight label * ((D.atom label ⬝ᵥ leftVec) * (D.atom label ⬝ᵥ rightVec)) := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix, vecMulVec_mulVec_eq,
      dotProduct_smul, smul_eq_mul, dotProduct_comm leftVec (D.atom label)]
    ring
  rw [D.isParseval, Matrix.one_mulVec] at hkey
  exact hkey.symm

/-! ## Share exactly one IS the near pencil

`Gtz.soleOffPlane_share_eq_one` says a near-pencil pole has share exactly one.
The converse holds and is elementary: pairing Parseval against the atom itself
makes the residual sum vanish term by term, so every OTHER atom is orthogonal
to it.  The pole's own atom is then the normal the near-pencil machinery wants,
supplied with no pattern hypothesis and no primitivity. -/

/-- **The converse of the pole share identity.**  Share exactly one at a label
forces every other atom orthogonal to that label's atom. -/
theorem dotProduct_atom_pole_eq_zero_of_share_eq_one (D : WeightedDesign m k)
    (poleLabel : Fin m)
    (hshare : D.weight poleLabel * leverageOf (D.atom poleLabel) = 1)
    (label : Fin m) (hne : label ≠ poleLabel) :
    D.atom label ⬝ᵥ D.atom poleLabel = 0 := by
  classical
  have hleverage : leverageOf (D.atom poleLabel) = D.atom poleLabel ⬝ᵥ D.atom poleLabel :=
    leverageOf_eq_dotProduct _
  have hshareDot : D.weight poleLabel * (D.atom poleLabel ⬝ᵥ D.atom poleLabel) = 1 := by
    rw [← hleverage]; exact hshare
  have htotal := parseval_weighted_sum_sq D (D.atom poleLabel)
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun label' => D.weight label' * (D.atom label' ⬝ᵥ D.atom poleLabel) ^ 2)
    (Finset.mem_univ poleLabel)
  have hpoleTerm : D.weight poleLabel * (D.atom poleLabel ⬝ᵥ D.atom poleLabel) ^ 2
      = D.atom poleLabel ⬝ᵥ D.atom poleLabel := by
    linear_combination (D.atom poleLabel ⬝ᵥ D.atom poleLabel) * hshareDot
  have hrestZero : ∑ label' ∈ Finset.univ.erase poleLabel,
      D.weight label' * (D.atom label' ⬝ᵥ D.atom poleLabel) ^ 2 = 0 := by
    rw [htotal] at hsplit
    rw [hpoleTerm] at hsplit
    linarith
  have hterm : D.weight label * (D.atom label ⬝ᵥ D.atom poleLabel) ^ 2 = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hrestZero label ?_
    · exact fun label' _ => mul_nonneg (D.weight_pos label').le (sq_nonneg _)
    · exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ label⟩
  rcases mul_eq_zero.mp hterm with hweightZero | hsquareZero
  · exact absurd hweightZero (D.weight_pos label).ne'
  · exact sq_eq_zero_iff.mp hsquareZero

/-- Share exactly one forces the atom nonzero, since its leverage is `1/t`. -/
theorem atom_ne_zero_of_share_eq_one (D : WeightedDesign m k) (poleLabel : Fin m)
    (hshare : D.weight poleLabel * leverageOf (D.atom poleLabel) = 1) :
    D.atom poleLabel ≠ 0 := by
  intro hzero
  rw [hzero] at hshare
  simp only [leverageOf, Pi.zero_apply] at hshare
  norm_num at hshare

/-- **Share one is exactly the near-pencil configuration.**  The forward
direction is this file's; the backward direction is the shipped
`Gtz.soleOffPlane_share_eq_one` at the normal `g_d` itself. -/
theorem share_eq_one_iff_forall_dotProduct_eq_zero (D : WeightedDesign m 3)
    (poleLabel : Fin m) (hpoleNe : D.atom poleLabel ≠ 0) :
    D.weight poleLabel * leverageOf (D.atom poleLabel) = 1
      ↔ ∀ label : Fin m, label ≠ poleLabel → D.atom label ⬝ᵥ D.atom poleLabel = 0 := by
  refine ⟨fun hshare label hne =>
    dotProduct_atom_pole_eq_zero_of_share_eq_one D poleLabel hshare label hne, fun hplanar => ?_⟩
  exact soleOffPlane_share_eq_one D poleLabel hpoleNe hplanar

/-- **A design with a share-one atom is not a tie.**  The share-one atom is a
near-pencil pole, and `Gtz.not_isTie_of_soleOffPlane` supplies a STRICTLY
dominating triple through it. -/
theorem not_isTie_of_share_eq_one (hsize : 2 ≤ m) (D : WeightedDesign m 3)
    (poleLabel : Fin m)
    (hshare : D.weight poleLabel * leverageOf (D.atom poleLabel) = 1) : ¬ IsTie D :=
  not_isTie_of_soleOffPlane hsize D poleLabel
    (atom_ne_zero_of_share_eq_one D poleLabel hshare)
    fun label hne => dotProduct_atom_pole_eq_zero_of_share_eq_one D poleLabel hshare label hne

/-- **Every share of a tie is strictly below one.**  The upper end of the
ledger's `Gtz.share_bracket_of_isTie` is the vacuous per-atom ceiling
`Gtz.weighted_leverage_le_one`; at a tie it is never attained, because
attainment IS a near pencil and a near pencil strictly dominates.  No instance
of `GtzWeighted` at rank three is consumed. -/
theorem share_lt_one_of_isTie (hsize : 2 ≤ m) (D : WeightedDesign m 3) (htie : IsTie D)
    (label : Fin m) : D.weight label * leverageOf (D.atom label) < 1 := by
  rcases lt_or_ge (D.weight label * leverageOf (D.atom label)) 1 with hlt | hge
  · exact hlt
  · exact absurd htie (not_isTie_of_share_eq_one hsize D label
      (le_antisymm (weighted_leverage_le_one D label) hge))

/-- **The half-open share bracket at a `(6,3)` tie.**  The floor is the ledger's
`Gtz.leverage_one_le_of_isTie_sixThree`, the strict ceiling is this file's. -/
theorem share_bracket_strict_of_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    (label : Fin 6) :
    D.weight label ≤ D.weight label * leverageOf (D.atom label) ∧
      D.weight label * leverageOf (D.atom label) < 1 := by
  refine ⟨?_, share_lt_one_of_isTie (by norm_num) D htie label⟩
  have hfloor := leverage_one_le_of_isTie_sixThree D htie label
  nlinarith [D.weight_pos label]

/-! ## Deflation at every label of a tie, and the deflated triple is a basis

`Gtz.exists_deflatedGapBound` carries a share hypothesis, which the headline now
discharges outright.  The gap bound it returns then forces the triple to be a
BASIS: a dependent triple's common orthogonal direction sends the transported
gap to `-|z|^2`, and the bound converts that into `t_d |g_d|^2 >= 1`. -/

/-- **Deflation is unconditional at a tie.**  Every label of a tie may be
deflated; the share side condition of `Gtz.exists_deflatedGapBound` is
automatic. -/
theorem exists_deflatedGapBound_of_isTie (D : WeightedDesign (m + 1) 3) (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m 3) (htie : IsTie D) (dropLabel : Fin (m + 1)) :
    ∃ selected : Finset (Fin (m + 1)), selected.card = 3 ∧ dropLabel ∉ selected ∧
      (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
        - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))).PosSemidef :=
  exists_deflatedGapBound D hsize hsmaller dropLabel
    (share_lt_one_of_isTie (by omega) D htie dropLabel)

/-- **The deflated triple is a basis.**  If the returned triple were dependent,
its common orthogonal direction `z` would make the primal gap `-|z|^2`, and the
Loewner bound then forces `t_d (g_d . z)^2 >= |z|^2`; Cauchy-Schwarz upgrades
that to `t_d |g_d|^2 >= 1`, which a share strictly below one forbids. -/
theorem atomBracket_ne_zero_of_deflatedGapBound (D : WeightedDesign (m + 1) 3)
    (dropLabel : Fin (m + 1))
    (hshare : D.weight dropLabel * leverageOf (D.atom dropLabel) < 1)
    (leftLabel midLabel rightLabel : Fin (m + 1))
    (hbound : (((1 : ℝ) - D.weight dropLabel)
        • (subsetSum D {leftLabel, midLabel, rightLabel} - 1)
        - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))).PosSemidef) :
    atomBracket D leftLabel midLabel rightLabel ≠ 0 := by
  classical
  intro hvanish
  obtain ⟨direction, hdirectionNe, horthogonal⟩ :=
    hasCommonOrthogonal_of_atomBracket_eq_zero D leftLabel midLabel rightLabel hvanish
  have hdirectionPos : 0 < direction ⬝ᵥ direction := dotProduct_self_pos hdirectionNe
  have hprojectionsVanish : ∑ label ∈ ({leftLabel, midLabel, rightLabel} : Finset (Fin (m + 1))),
      (D.atom label ⬝ᵥ direction) ^ 2 = 0 :=
    Finset.sum_eq_zero fun label hlabel => by rw [horthogonal label hlabel]; ring
  have hprimalGap : direction
      ⬝ᵥ ((subsetSum D {leftLabel, midLabel, rightLabel} - 1) *ᵥ direction)
      = -(direction ⬝ᵥ direction) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
      dotProduct_subsetSum_mulVec_of_finset, hprojectionsVanish]
    ring
  have hcomplementGap : direction
      ⬝ᵥ (((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (D.atom dropLabel)) *ᵥ direction)
      = direction ⬝ᵥ direction - (D.atom dropLabel ⬝ᵥ direction) ^ 2 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, dotProduct_atomMatrix_mulVec]
  have hboundForm := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hbound).2 direction
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hprimalGap,
    hcomplementGap] at hboundForm
  have hpull : direction ⬝ᵥ direction
      ≤ D.weight dropLabel * (D.atom dropLabel ⬝ᵥ direction) ^ 2 := by nlinarith [hboundForm]
  have hcauchy : (D.atom dropLabel ⬝ᵥ direction) ^ 2
      ≤ (D.atom dropLabel ⬝ᵥ D.atom dropLabel) * (direction ⬝ᵥ direction) :=
    dotProduct_sq_le_mul _ _
  have hleverage : leverageOf (D.atom dropLabel) = D.atom dropLabel ⬝ᵥ D.atom dropLabel :=
    leverageOf_eq_dotProduct _
  have hshareDot : D.weight dropLabel * (D.atom dropLabel ⬝ᵥ D.atom dropLabel) < 1 := by
    rw [← hleverage]; exact hshare
  nlinarith [hpull, hcauchy, hshareDot, hdirectionPos, D.weight_pos dropLabel]

/-- **A tie has a basis triple avoiding any nominated label.**  The direction
matroid of a tie therefore still has rank three after deleting any single point.
Granted weighted GTZ one size down. -/
theorem exists_basisTriple_avoiding_of_isTie (D : WeightedDesign (m + 1) 3) (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m 3) (htie : IsTie D) (dropLabel : Fin (m + 1)) :
    ∃ leftLabel midLabel rightLabel : Fin (m + 1),
      leftLabel ≠ midLabel ∧ leftLabel ≠ rightLabel ∧ midLabel ≠ rightLabel ∧
        leftLabel ≠ dropLabel ∧ midLabel ≠ dropLabel ∧ rightLabel ≠ dropLabel ∧
        atomBracket D leftLabel midLabel rightLabel ≠ 0 := by
  classical
  obtain ⟨selected, hcard, hAvoidsDrop, hbound⟩ :=
    exists_deflatedGapBound_of_isTie D hsize hsmaller htie dropLabel
  obtain ⟨leftLabel, midLabel, rightLabel, hleftMid, hleftRight, hmidRight, hshape⟩ :=
    Finset.card_eq_three.mp hcard
  have hdropNotMem :
      dropLabel ∉ ({leftLabel, midLabel, rightLabel} : Finset (Fin (m + 1))) := by
    rw [← hshape]; exact hAvoidsDrop
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hdropNotMem
  refine ⟨leftLabel, midLabel, rightLabel, hleftMid, hleftRight, hmidRight,
    Ne.symm hdropNotMem.1, Ne.symm hdropNotMem.2.1, Ne.symm hdropNotMem.2.2, ?_⟩
  refine atomBracket_ne_zero_of_deflatedGapBound D dropLabel
    (share_lt_one_of_isTie (by omega) D htie dropLabel) leftLabel midLabel rightLabel ?_
  rw [← hshape]
  exact hbound

/-- **The `(6,3)` form, unconditional.**  The input is
`Gtz.gtzWeighted_of_le_five` at five points, so no open instance is assumed. -/
theorem exists_basisTriple_avoiding_of_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    (dropLabel : Fin 6) :
    ∃ leftLabel midLabel rightLabel : Fin 6,
      leftLabel ≠ midLabel ∧ leftLabel ≠ rightLabel ∧ midLabel ≠ rightLabel ∧
        leftLabel ≠ dropLabel ∧ midLabel ≠ dropLabel ∧ rightLabel ≠ dropLabel ∧
        atomBracket D leftLabel midLabel rightLabel ≠ 0 :=
  exists_basisTriple_avoiding_of_isTie (m := 5) D (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) htie dropLabel

/-! ## The discharge rule the condition yields, and how far it reaches

A pattern with a BLIND LABEL — one whose complement carries only dependent
triples — is tie-free.  That is the whole strength of single-deletion rank, and
against the thirty-two-class ledger it recognizes exactly the near pencil. -/

/-- **The blind-label rule.**  If every distinct triple avoiding one nominated
label is declared dependent, no design on the stratum is a tie. -/
theorem stratumIsTieFree_of_blindLabel {size : ℕ} (hsize : 1 ≤ size)
    (hsmaller : GtzWeighted size 3) (pattern : LinePattern (size + 1))
    (blindLabel : Fin (size + 1))
    (hdependent : ∀ leftLabel midLabel rightLabel : Fin (size + 1),
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
      leftLabel ≠ blindLabel → midLabel ≠ blindLabel → rightLabel ≠ blindLabel →
      pattern leftLabel midLabel rightLabel) :
    StratumIsTieFree pattern := by
  intro D hpattern htie
  obtain ⟨leftLabel, midLabel, rightLabel, hleftMid, hleftRight, hmidRight,
    hleftBlind, hmidBlind, hrightBlind, hbracket⟩ :=
    exists_basisTriple_avoiding_of_isTie D hsize hsmaller htie blindLabel
  exact hbracket ((hpattern leftLabel midLabel rightLabel hleftMid hleftRight hmidRight).mpr
    (hdependent leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
      hleftBlind hmidBlind hrightBlind))

/-- **The six-point near-pencil entry through the blind-label interface.**  The
pole is the blind label: every distinct triple avoiding it is dependent by the
pattern's own definition.

NOT logically independent, and the docstring says so rather than implying
otherwise.  The rule reaches the near pencil through `share_lt_one_of_isTie`,
which consumes `Gtz.not_isTie_of_soleOffPlane` — the rank-two transport that
already proves `Gtz.stratumIsTieFree_nearPencil`.  Worse for any independence
claim: at a near pencil the pole's share is EXACTLY one
(`Gtz.soleOffPlane_share_eq_one`), so `share_lt_one_of_isTie` contradicts the
tie before the deflation step is ever reached.  This is therefore a
re-derivation through a different interface, useful because the interface is a
general rule, and not a third certificate.  At seven points the same rule would
additionally need the open `GtzWeighted 6 3`, so there it is strictly weaker
than the shipped proof. -/
theorem stratumIsTieFree_nearPencil_viaBlindLabel_sixThree (poleLabel : Fin 6) :
    StratumIsTieFree (nearPencilLinePattern poleLabel) :=
  stratumIsTieFree_of_blindLabel (size := 5) (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) _ poleLabel
    fun _ _ _ _ _ _ hleftBlind hmidBlind hrightBlind => ⟨hleftBlind, hmidBlind, hrightBlind⟩

/-- Three pairwise distinct labels avoiding a nominated one exist as soon as
there are four labels. -/
theorem exists_distinctTriple_avoiding {size : ℕ} (hsize : 4 ≤ size) (blindLabel : Fin size) :
    ∃ leftLabel midLabel rightLabel : Fin size,
      leftLabel ≠ midLabel ∧ leftLabel ≠ rightLabel ∧ midLabel ≠ rightLabel ∧
        leftLabel ≠ blindLabel ∧ midLabel ≠ blindLabel ∧ rightLabel ≠ blindLabel := by
  classical
  have hcomplement : 3 ≤ ({blindLabel}ᶜ : Finset (Fin size)).card := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    omega
  obtain ⟨witnessTriple, hsubset, hcard⟩ := Finset.exists_subset_card_eq hcomplement
  obtain ⟨leftLabel, midLabel, rightLabel, hleftMid, hleftRight, hmidRight, hshape⟩ :=
    Finset.card_eq_three.mp hcard
  have hoff : ∀ label : Fin size, label ∈ witnessTriple → label ≠ blindLabel := by
    intro label hmem
    simpa only [Finset.mem_compl, Finset.mem_singleton] using hsubset hmem
  exact ⟨leftLabel, midLabel, rightLabel, hleftMid, hleftRight, hmidRight,
    hoff leftLabel (by rw [hshape]; simp), hoff midLabel (by rw [hshape]; simp),
    hoff rightLabel (by rw [hshape]; simp)⟩

/-- **The blind-label rule is inert on the line-free classes.**  At four or more
labels NO label is blind for the uniform matroid's pattern, so `U(3,6)` and
`U(3,7)` are untouched — and, since every distinct triple there is a basis, the
pruning rule `Gtz.not_dominates_of_atomBracket_eq_zero` excludes no triple
either.  The line-free classes carry the least structural input of the
thirty-two, not the most. -/
theorem not_blindLabel_lineFree {size : ℕ} (hsize : 4 ≤ size) (blindLabel : Fin size) :
    ¬ (∀ leftLabel midLabel rightLabel : Fin size,
        leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        leftLabel ≠ blindLabel → midLabel ≠ blindLabel → rightLabel ≠ blindLabel →
        (fun _ _ _ => False : LinePattern size) leftLabel midLabel rightLabel) := by
  intro hdependent
  obtain ⟨leftLabel, midLabel, rightLabel, hleftMid, hleftRight, hmidRight,
    hleftBlind, hmidBlind, hrightBlind⟩ := exists_distinctTriple_avoiding hsize blindLabel
  exact hdependent leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
    hleftBlind hmidBlind hrightBlind

/-! ## A coplanar family carries weighted leverage at most two

Parseval evaluated at the shared normal is carried entirely by the atoms OFF the
plane, and Cauchy-Schwarz bounds each such term by that atom's own share.  So
the off-plane shares total at least one, and the trace identity
`Gtz.sum_weighted_leverage` turns that into a ceiling of two on the plane.  No
plane frame, no basis change, no eigenvalue. -/

/-- **The off-plane share floor.**  The atoms NOT sharing the normal carry
weighted leverage at least one, because they alone must resolve the normal's own
direction. -/
theorem one_le_offPlaneWeightedLeverage (D : WeightedDesign m 3)
    (coplanarSet : Finset (Fin m)) {normalVec : Fin 3 → ℝ} (hnormalNe : normalVec ≠ 0)
    (hcoplanar : ∀ label ∈ coplanarSet, D.atom label ⬝ᵥ normalVec = 0) :
    1 ≤ ∑ label ∈ coplanarSetᶜ, D.weight label * leverageOf (D.atom label) := by
  classical
  have hnormPos : 0 < normalVec ⬝ᵥ normalVec := dotProduct_self_pos hnormalNe
  have htotal := parseval_weighted_sum_sq D normalVec
  have hsplit := Finset.sum_add_sum_compl coplanarSet
    (fun label => D.weight label * (D.atom label ⬝ᵥ normalVec) ^ 2)
  have hplaneZero : ∑ label ∈ coplanarSet,
      D.weight label * (D.atom label ⬝ᵥ normalVec) ^ 2 = 0 :=
    Finset.sum_eq_zero fun label hlabel => by rw [hcoplanar label hlabel]; ring
  have hoffPlane : ∑ label ∈ coplanarSetᶜ,
      D.weight label * (D.atom label ⬝ᵥ normalVec) ^ 2 = normalVec ⬝ᵥ normalVec := by
    rw [hplaneZero, zero_add] at hsplit
    rw [hsplit, htotal]
  have hdominated : ∀ label : Fin m,
      D.weight label * (D.atom label ⬝ᵥ normalVec) ^ 2
        ≤ D.weight label * leverageOf (D.atom label) * (normalVec ⬝ᵥ normalVec) := by
    intro label
    have hcauchy : (D.atom label ⬝ᵥ normalVec) ^ 2
        ≤ (D.atom label ⬝ᵥ D.atom label) * (normalVec ⬝ᵥ normalVec) :=
      dotProduct_sq_le_mul _ _
    have hleverage : leverageOf (D.atom label) = D.atom label ⬝ᵥ D.atom label :=
      leverageOf_eq_dotProduct _
    rw [hleverage, mul_assoc]
    exact mul_le_mul_of_nonneg_left hcauchy (D.weight_pos label).le
  have hsumBound : (∑ label ∈ coplanarSetᶜ, D.weight label * (D.atom label ⬝ᵥ normalVec) ^ 2)
      ≤ ∑ label ∈ coplanarSetᶜ,
          D.weight label * leverageOf (D.atom label) * (normalVec ⬝ᵥ normalVec) :=
    Finset.sum_le_sum fun label _ => hdominated label
  rw [← Finset.sum_mul, hoffPlane] at hsumBound
  nlinarith [hsumBound, hnormPos]

/-- **The coplanar weighted-leverage ceiling.**  A family of atoms sharing a
nonzero orthogonal direction carries weighted leverage at most two — the rank of
the plane it lies in.  Complementary to `one_le_offPlaneWeightedLeverage`
through the trace identity `Gtz.sum_weighted_leverage`. -/
theorem coplanarWeightedLeverage_le_two (D : WeightedDesign m 3)
    (coplanarSet : Finset (Fin m)) {normalVec : Fin 3 → ℝ} (hnormalNe : normalVec ≠ 0)
    (hcoplanar : ∀ label ∈ coplanarSet, D.atom label ⬝ᵥ normalVec = 0) :
    (∑ label ∈ coplanarSet, D.weight label * leverageOf (D.atom label)) ≤ 2 := by
  classical
  have htrace := sum_weighted_leverage D
  have hsplit := Finset.sum_add_sum_compl coplanarSet
    (fun label => D.weight label * leverageOf (D.atom label))
  have hfloor := one_le_offPlaneWeightedLeverage D coplanarSet hnormalNe hcoplanar
  rw [htrace] at hsplit
  norm_num at hsplit
  linarith

/-- **At a tie no plane holds all but at most one atom.**  A re-derivation of the
near-pencil exclusion whose own final step is purely quantitative: the off-plane
shares total at least one while each single share is strictly below one, so at
least two atoms sit off every plane.

NOT logically independent of the rank-two transport, and earlier drafts of this
docstring said otherwise.  Only the last step is transport-free; the theorem
consumes `share_lt_one_of_isTie`, which routes through
`Gtz.not_isTie_of_soleOffPlane` into `Gtz.exists_posDef_of_soleOffPlane` (the
transport) and through that into `Gtz.gtz_rank_two`. -/
theorem two_le_card_offPlane_of_isTie (hsize : 2 ≤ m) (D : WeightedDesign m 3)
    (htie : IsTie D) (coplanarSet : Finset (Fin m)) {normalVec : Fin 3 → ℝ}
    (hnormalNe : normalVec ≠ 0)
    (hcoplanar : ∀ label ∈ coplanarSet, D.atom label ⬝ᵥ normalVec = 0) :
    2 ≤ coplanarSetᶜ.card := by
  classical
  have hfloor := one_le_offPlaneWeightedLeverage D coplanarSet hnormalNe hcoplanar
  rcases Finset.eq_empty_or_nonempty coplanarSetᶜ with hempty | hnonempty
  · rw [hempty, Finset.sum_empty] at hfloor
    linarith
  · have hstrict : (∑ label ∈ coplanarSetᶜ, D.weight label * leverageOf (D.atom label))
        < ∑ _label ∈ coplanarSetᶜ, (1 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty hnonempty
        fun label _ => share_lt_one_of_isTie hsize D htie label
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hstrict
    have hcardReal : (1 : ℝ) < (coplanarSetᶜ.card : ℝ) := lt_of_le_of_lt hfloor hstrict
    have hcardNat : 1 < coplanarSetᶜ.card := by exact_mod_cast hcardReal
    omega

/-! ## The ceiling at pattern level, and the wall as a theorem

A line of a pattern carries a normal that the pattern itself certifies nonzero,
exactly as `Gtz.sharedNormal_of_hasNearPencilLinePattern` does for the near
pencil: two labels on the line have vanishing bracket against every other line
label, and non-vanishing bracket against one off-line label.  Feeding that into
`two_le_card_offPlane_of_isTie` gives the stratum-level ceiling — and shows
precisely why it stops at the near pencil. -/

/-- **A line of the pattern has a nonzero normal.**  The shared
`Gtz.bracketNormal` of two line labels is orthogonal to every atom of the line,
and the off-line witness triple's non-dependence is what makes it nonzero.  No
primitivity hypothesis: the pattern supplies the non-vanishing. -/
theorem exists_lineNormal_of_hasLinePattern {size : ℕ} (D : WeightedDesign size 3)
    {pattern : LinePattern size} (hpattern : HasLinePattern D pattern)
    (lineSet : Finset (Fin size)) (firstLabel secondLabel witnessLabel : Fin size)
    (hdistinct : firstLabel ≠ secondLabel)
    (hfirstWitness : firstLabel ≠ witnessLabel) (hsecondWitness : secondLabel ≠ witnessLabel)
    (hwitnessFree : ¬ pattern firstLabel secondLabel witnessLabel)
    (hlineDependent : ∀ label ∈ lineSet, label ≠ firstLabel → label ≠ secondLabel →
      pattern firstLabel secondLabel label) :
    ∃ normalVec : Fin 3 → ℝ, normalVec ≠ 0 ∧
      ∀ label ∈ lineSet, D.atom label ⬝ᵥ normalVec = 0 := by
  refine ⟨bracketNormal (D.atom firstLabel) (D.atom secondLabel), ?_, fun label hlabel => ?_⟩
  · intro hnormalZero
    refine hwitnessFree ((hpattern firstLabel secondLabel witnessLabel hdistinct
      hfirstWitness hsecondWitness).mp ?_)
    rw [atomBracket, tripleBracket_eq_bracketNormal_dotProduct, hnormalZero, zero_dotProduct]
  · rw [dotProduct_comm, ← tripleBracket_eq_bracketNormal_dotProduct]
    by_cases hfirst : label = firstLabel
    · rw [hfirst]
      simp only [tripleBracket_eq]; ring
    · by_cases hsecond : label = secondLabel
      · rw [hsecond]
        simp only [tripleBracket_eq]; ring
      · exact (hpattern firstLabel secondLabel label hdistinct
          (fun hequal => hfirst hequal.symm) (fun hequal => hsecond hequal.symm)).mpr
          (hlineDependent label hlabel hfirst hsecond)

/-- **Every line of a tie's pattern misses at least two labels.**  The
pattern-level form of `two_le_card_offPlane_of_isTie`.

This is the WALL, stated: to discharge a class the rule needs a line whose
complement has at most ONE label, and in a simple rank-three matroid on `size`
points a `(size - 1)`-point line IS the near pencil.  So the coplanar ceiling
recognizes exactly the entry that three other arguments already retire, and
nothing among the twenty-nine open classes, whose maximal lines all miss at
least two points. -/
theorem two_le_card_offLine_of_isTie {size : ℕ} (hsize : 2 ≤ size) (D : WeightedDesign size 3)
    (htie : IsTie D) {pattern : LinePattern size} (hpattern : HasLinePattern D pattern)
    (lineSet : Finset (Fin size)) (firstLabel secondLabel witnessLabel : Fin size)
    (hdistinct : firstLabel ≠ secondLabel)
    (hfirstWitness : firstLabel ≠ witnessLabel) (hsecondWitness : secondLabel ≠ witnessLabel)
    (hwitnessFree : ¬ pattern firstLabel secondLabel witnessLabel)
    (hlineDependent : ∀ label ∈ lineSet, label ≠ firstLabel → label ≠ secondLabel →
      pattern firstLabel secondLabel label) :
    2 ≤ lineSetᶜ.card := by
  obtain ⟨normalVec, hnormalNe, hcoplanar⟩ := exists_lineNormal_of_hasLinePattern D hpattern
    lineSet firstLabel secondLabel witnessLabel hdistinct hfirstWitness hsecondWitness
    hwitnessFree hlineDependent
  exact two_le_card_offPlane_of_isTie hsize D htie lineSet hnormalNe hcoplanar

/-! ## Exactly two atoms off a plane: the rigidity, and why the near-pencil
margin dies

With ONE atom off the plane, Parseval collapses to a single rank-one term and
the pole is parallel to the normal (`Gtz.soleOffPlane_normal_eq_smul_pole`).
With TWO, the collapse is a two-term identity — and it is an identity, not an
inequality.  Its diagonal pins the two poles' normal components; its off-diagonal
says their IN-PLANE components are exactly antiparallel; and primitivity then
forces both in-plane components NONZERO, which is precisely what destroys the
compression margin the near-pencil transport runs on. -/

/-- **The two-pole Parseval collapse.**  With every atom but two orthogonal to
`normalVec`, the two exceptional atoms alone reproduce `normalVec`'s pairing
against every probe. -/
theorem offPlanePair_pairing (D : WeightedDesign m 3) (firstPole secondPole : Fin m)
    (hdistinct : firstPole ≠ secondPole) {normalVec : Fin 3 → ℝ}
    (hplanar : ∀ label : Fin m, label ≠ firstPole → label ≠ secondPole →
      D.atom label ⬝ᵥ normalVec = 0)
    (probeVec : Fin 3 → ℝ) :
    D.weight firstPole * ((D.atom firstPole ⬝ᵥ normalVec) * (D.atom firstPole ⬝ᵥ probeVec))
        + D.weight secondPole
          * ((D.atom secondPole ⬝ᵥ normalVec) * (D.atom secondPole ⬝ᵥ probeVec))
      = normalVec ⬝ᵥ probeVec := by
  classical
  have hrestrict := Finset.sum_subset (Finset.subset_univ
      ({firstPole, secondPole} : Finset (Fin m)))
    (f := fun label => D.weight label
      * ((D.atom label ⬝ᵥ normalVec) * (D.atom label ⬝ᵥ probeVec)))
    (by
      intro label _ hnotMem
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnotMem
      rw [hplanar label hnotMem.1 hnotMem.2, zero_mul, mul_zero])
  rw [Finset.sum_pair hdistinct] at hrestrict
  rw [hrestrict]
  exact sum_weighted_atomPairing D normalVec probeVec

/-- **The two-pole collapse, on the nose.**  The weighted normal components of
the two poles reconstruct the normal itself — the exact analogue of
`Gtz.soleOffPlane_normal_eq_smul_pole` one pole up. -/
theorem offPlanePair_combination_eq_normal (D : WeightedDesign m 3)
    (firstPole secondPole : Fin m) (hdistinct : firstPole ≠ secondPole)
    {normalVec : Fin 3 → ℝ}
    (hplanar : ∀ label : Fin m, label ≠ firstPole → label ≠ secondPole →
      D.atom label ⬝ᵥ normalVec = 0) :
    (D.weight firstPole * (D.atom firstPole ⬝ᵥ normalVec)) • D.atom firstPole
        + (D.weight secondPole * (D.atom secondPole ⬝ᵥ normalVec)) • D.atom secondPole
      = normalVec := by
  refine eq_of_forall_dotProduct_eq fun probeVec => ?_
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have hpairing := offPlanePair_pairing D firstPole secondPole hdistinct hplanar probeVec
  linarith [hpairing]

/-- **The diagonal of the collapse.**  The two poles' weighted squared normal
components total the normal's squared length. -/
theorem offPlanePair_normalSquare_eq (D : WeightedDesign m 3)
    (firstPole secondPole : Fin m) (hdistinct : firstPole ≠ secondPole)
    {normalVec : Fin 3 → ℝ}
    (hplanar : ∀ label : Fin m, label ≠ firstPole → label ≠ secondPole →
      D.atom label ⬝ᵥ normalVec = 0) :
    D.weight firstPole * (D.atom firstPole ⬝ᵥ normalVec) ^ 2
        + D.weight secondPole * (D.atom secondPole ⬝ᵥ normalVec) ^ 2
      = normalVec ⬝ᵥ normalVec := by
  have hpairing := offPlanePair_pairing D firstPole secondPole hdistinct hplanar normalVec
  linear_combination hpairing

/-- **The off-diagonal of the collapse.**  Against every probe IN the plane the
two poles' contributions cancel exactly: their in-plane components are
antiparallel, with the weights and normal components as the ratio. -/
theorem offPlanePair_projection_antiparallel (D : WeightedDesign m 3)
    (firstPole secondPole : Fin m) (hdistinct : firstPole ≠ secondPole)
    {normalVec : Fin 3 → ℝ}
    (hplanar : ∀ label : Fin m, label ≠ firstPole → label ≠ secondPole →
      D.atom label ⬝ᵥ normalVec = 0)
    (probeVec : Fin 3 → ℝ) (hprobePlanar : probeVec ⬝ᵥ normalVec = 0) :
    D.weight firstPole * ((D.atom firstPole ⬝ᵥ normalVec) * (D.atom firstPole ⬝ᵥ probeVec))
      = -(D.weight secondPole
          * ((D.atom secondPole ⬝ᵥ normalVec) * (D.atom secondPole ⬝ᵥ probeVec))) := by
  have hpairing := offPlanePair_pairing D firstPole secondPole hdistinct hplanar probeVec
  rw [dotProduct_comm normalVec probeVec, hprobePlanar] at hpairing
  linarith [hpairing]

/-- **Neither pole is parallel to the normal at a primitive design.**

SCOPE, because the headline sentence overstates the statement: what is proved
here is the probe for `firstPole` only.  The claim for `secondPole` follows by
re-instantiating this same theorem with the two poles exchanged — every
hypothesis is symmetric under that swap, `hdistinct` up to `Ne.symm` — but it is
NOT a conclusion of this declaration, so a caller wanting both probes must apply
this theorem twice.

Granted both probes, the compression `Gtz.compressedDesign` along the plane kills
NEITHER pole, the
planar family retains total weight one, and the deflation `Gtz.poleDeflation`
that makes `Gtz.exists_posDef_of_soleOffPlane` STRICT has no analogue with two
poles.  This is the near-pencil transport's own header claim, proved: the
mechanism is special to one off-plane atom, and no rescaling reaches the
two-pole classes. -/
theorem exists_planarProbe_of_offPlanePair_of_isPrimitive (D : WeightedDesign m 3)
    (hprimitive : IsPrimitiveDesign D) (firstPole secondPole : Fin m)
    (hdistinct : firstPole ≠ secondPole) {normalVec : Fin 3 → ℝ}
    (hnormalNe : normalVec ≠ 0)
    (hplanar : ∀ label : Fin m, label ≠ firstPole → label ≠ secondPole →
      D.atom label ⬝ᵥ normalVec = 0)
    (hfirstOffPlane : D.atom firstPole ⬝ᵥ normalVec ≠ 0)
    (hsecondOffPlane : D.atom secondPole ⬝ᵥ normalVec ≠ 0) :
    ∃ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ normalVec = 0 ∧ D.atom firstPole ⬝ᵥ probeVec ≠ 0 := by
  classical
  by_contra hnoProbe
  simp only [not_exists, not_and, not_not] at hnoProbe
  have hfirstAnnihilates : ∀ probeVec : Fin 3 → ℝ,
      probeVec ⬝ᵥ normalVec = 0 → D.atom firstPole ⬝ᵥ probeVec = 0 :=
    fun probeVec hprobePlanar => hnoProbe probeVec hprobePlanar
  have hsecondAnnihilates : ∀ probeVec : Fin 3 → ℝ,
      probeVec ⬝ᵥ normalVec = 0 → D.atom secondPole ⬝ᵥ probeVec = 0 := by
    intro probeVec hprobePlanar
    have hcancel := offPlanePair_projection_antiparallel D firstPole secondPole hdistinct
      hplanar probeVec hprobePlanar
    rw [hfirstAnnihilates probeVec hprobePlanar, mul_zero, mul_zero] at hcancel
    have hfactor : D.weight secondPole * ((D.atom secondPole ⬝ᵥ normalVec)
        * (D.atom secondPole ⬝ᵥ probeVec)) = 0 := by linarith
    rcases mul_eq_zero.mp hfactor with hweightZero | hproductZero
    · exact absurd hweightZero (D.weight_pos secondPole).ne'
    · rcases mul_eq_zero.mp hproductZero with hnormalZero | hprobeZero
      · exact absurd hnormalZero hsecondOffPlane
      · exact hprobeZero
  obtain ⟨firstRatio, hfirstShape⟩ : ∃ ratio : ℝ, D.atom firstPole = ratio • normalVec :=
    ⟨_, eq_smul_normal_of_orthogonal_annihilates hnormalNe hfirstAnnihilates⟩
  obtain ⟨secondRatio, hsecondShape⟩ : ∃ ratio : ℝ, D.atom secondPole = ratio • normalVec :=
    ⟨_, eq_smul_normal_of_orthogonal_annihilates hnormalNe hsecondAnnihilates⟩
  have hfirstRatioNe : firstRatio ≠ 0 := by
    intro hratioZero
    rw [hratioZero, zero_smul] at hfirstShape
    rw [hfirstShape, zero_dotProduct] at hfirstOffPlane
    exact hfirstOffPlane rfl
  refine hprimitive firstPole secondPole (secondRatio / firstRatio) hdistinct ?_
  rw [hsecondShape, hfirstShape, smul_smul]
  congr 1
  field_simp

end Gtz

/-
# The good-triple graph: the covering as a Ramsey question, and the box level refuted

`Gtz.Quantitative.DiscriminantSystem` reduced the whole of rank three to ONE
sentence, `DiscriminantCovering 7`. This file reads that sentence as a statement
about GRAPHS on the seven atoms, mechanizes the elliptope normalisation that makes
the reading exact, and settles the level at which a purely combinatorial attack was
proposed: it is refuted, exactly, by an object the repo already owns.

**The elliptope reading, exact.** With `u_c = heavyExcess c > 0` and the normalized
pairing `rho_cd = <g_c,g_d> / sqrt(u_c u_d)`, the tie leg factors as

  `discriminantTie = u_a u_b u_c · (1 − rho_ab² − rho_ac² − rho_bc² + 2 rho_ab rho_ac rho_bc)`

(`discriminantTie_eq_excessProduct_mul_elliptopeBracket`): the leverages factor out
COMPLETELY and the bracket is the DETERMINANT of the `3×3` correlation matrix. That
is NOT elliptope membership on its own: `E_3` is `det ≥ 0` AND `|rho| ≤ 1` on every
pair, and the bracket supplies only the determinant half. Three parallel copies of a
leverage-`3` atom give gap `[[2,3,3],[3,2,3],[3,3,2]]`, spectrum `(e1,e2,e3) =
(6,−15,8)`, `rho ≡ 3/2`, bracket `+1 ≥ 0` and `discriminantTie = 8 ≥ 0` — yet the
correlation matrix has eigenvalues `{4,−1/2,−1/2}` and the triple does NOT dominate.
The missing conjunct is exactly compatibility (`|rho| ≤ 1`, i.e. the pair minors), so
`IsElliptopeGoodTriangle`, which conjoins it, is the honest elliptope statement and
`IsCompatibleTriangle` is load-bearing, never redundant. The whole covering is then a
condition on three numbers per triple, degree three.

**Domination splits into edges plus one triple.** `pairMinor c d = u_c u_d − p_cd²`
is the `2×2` gap minor of a pair, and `dominates_triple_iff_isElliptopeGoodTriangle`
says: a triple of distinct heavy atoms dominates iff its three pair minors are
nonnegative AND its tie leg is nonnegative. Three EDGE conditions and one TRIPLE
condition — the graph shape. Hence three nested graphs on the same vertex set:

  box-good `4 p² ≤ u u`  (`|rho| ≤ 1/2`)  ⊆  elliptope-good  ⊆  compatible `|rho| ≤ 1`

with `dominates_of_isBoxGoodTriangle` (sufficiency, the Handelman multiplier-degree-
zero certificate, which is `dominates_of_dominantPairings` read through the graph)
and `isCompatibleTriangle_of_dominates` (necessity) sandwiching domination. At the
frontier size, `elliptopeGoodTriangleCovering_seven_iff_rank_three`: GTZ at rank
three IS "the elliptope-good graph on seven vertices always has a triangle".

**The box level is refuted, and not marginally.** The counting attack ran through
Turán–Mantel: a triangle-free graph on seven vertices has at most `⌊49/4⌋ = 12`
edges, so a triangle-free box-good graph forces at least `9` of the `21` pairs to
be box-bad, which looked like a strong constraint on a rank-bounded correlation
matrix. It is not a constraint at all. At `icosaDesign` — the maximal real
equiangular set, six lines at squared cosine `1/5`, already a kernel-checked
weighted `(6,3)` design here — every leverage is `3`, so `u = 2`, and every squared
pairing is `9/5`, so EVERY box leg is exactly `2·2 − 4·(9/5) = −16/5 < 0`
(`icosaDesign_boxSlack_of_ne`). The box-good graph is EMPTY:
`icosaDesign_no_isBoxGoodPair` covers all `15` distinct pairs and the diagonal,
`not_boxGoodTriangleCovering_six` turns that into a refutation, and size
monotonicity (`boxGoodTriangleCovering_of_le`) propagates it to every size at least
six, so the frontier form `BoxGoodTriangleCovering 7` is false too. Replicating one
atom exhibits the seven-atom witness directly (`icosaSevenDesign`), where all `21`
pairs are box-bad against the `9` the counting needed. The design nonetheless
dominates, strictly, with margin `2 − 3/√5` (`icosaDesign_strictly_dominates`), so
what fails is the certificate family, not the conjecture.

Cause, corrected: equiangularity is NOT the mechanism. The box level dies on the
tetrahedral stratum itself the instant the leverages differ — on the two-scale slice
`1/y + 1/z = 2`, `59` exact rational points were scanned and the regular tetrahedron
`y = z = 1` is the ONLY one carrying a box triangle (a single edge for `y > 1`, a star
`K_{1,3}` for `y < 1`). LEVERAGE SPREAD is what kills it; the icosahedron is merely the
equal-leverage witness. The isolation threshold in the projection normalisation is
`P_cc ≥ 2/3`, not `1/2`: idempotency gives `sum_{d≠a} P_ad² = P_aa (1 − P_aa)`, so an
obstruction needs `−P_aa (3 P_aa − 2) ≤ 0`.

**Non-strictness is load-bearing.** At `splitSevenDesign` — the `(7,3)` tie, four
tetrahedron directions with multiplicities `(2,2,2,1)` — every box leg is exactly
`0` on a different-direction pair and `−32` on a same-direction pair, so the STRICT
box graph is empty there too (`splitSevenDesign_no_strictBoxGoodPair`) and any
strict-inequality reading of `BoxGoodTriangleCovering` is refuted at the frontier
size by the repo's own tie. The non-strict graph is the complete multipartite graph
on the direction classes and does contain a triangle
(`splitSevenDesign_isBoxGoodTriangle`), through which the graph interface
re-derives the known domination of `{0,1,2}`
(`splitSevenDesign_dominates_of_isBoxGoodTriangle`). Both box legs of the two
sharpest objects sit ON a boundary, in opposite directions: the tetrahedron at
`|rho| = 1/2` exactly, the icosahedron a factor `9/5` outside.

**The remaining refutation channel, stated.** Compatibility is necessary, so if some
all-heavy design's compatible graph were triangle-free, GTZ at rank three would be
FALSE (`not_gtzWeightedAll_three_of_no_compatibleTriangle`). Search does not find
one. The statistic previously recorded here — "`300` SLSQP restarts saturate at
`max|rho| = 0.999888801049`" — is WITHDRAWN: it is contradicted by `icosaSevenDesign`
below in this same file, where `not_isCompatiblePair_of_atom_eq` proves `|rho| = 3/2`
on the twin pair, and a `4000`-design census reaches `max|rho| = 15.317`. The quantity
that does saturate is the OPPOSITE extremum, `max over designs of min over pairs
|rho|`, which two independent optimizers stop at `0.670820393250 = sqrt(9/20)`, the
icosahedral value — far below the `1` a refutation needs. Measured only.

**Measured, never proved.** Coverage of the single symmetric box under uniform
sampling of `Gr(3,7) × Δ⁶` is `0.883`; a `44`-cell family of maximal asymmetric
boxes on a `0.05` grid reaches `0.99992`; the exact elliptope reaches `1`. The
box-good graph is triangle-free on `13.45%`, `14.60%` and `15.55%` of samples under
three different samplers (LP-vertex plus `brentq` weight solve; spread-swept
rejection; hit-and-run on the leverage simplex); a fourth sampler lands outside that
range, so the spread is a LOWER bound on sampler sensitivity, not a converged error
bar. The EMPTY box graph is invisible to all of them (`0` of `12000`
designs) and was reached only by SLSQP minimax on the epigraph variable with
analytic Jacobians, checked against central differences to `1.1e-9`; Nelder–Mead
stalls on this nonsmooth max at `1e-4` and returns bit-identical values. Around a
non-degenerate interior empty-box witness the equality Jacobian has rank `7`, so the
implicit function theorem gives a `21`-dimensional open family — the box is blind on
a set of full dimension, not at a point; `300/300` perturbations at scale `1e-3`
and `227/300` at `3e-2` keep the graph empty.

**The refutation is not about the box — it is about SIGNS.** The box, the anisotropic
radius boxes of `dominates_of_radiusBox`, and the ball
`rho_ab² + rho_ac² + rho_bc² ≤ 3/4` all read only SQUARED pairings. That family has an
exact closure, `2 |p_ab p_ac p_bc| ≤ excessGap` (`IsSignBlindGoodTriple`), which is
sound, contains all of them, and is STILL empty at `icosaDesign`, where the sign-blind
gap is negative at every one of the `216` ordered triples
(`icosaDesign_no_isSignBlindGoodTriple`). So `not_boxGoodTriangleCovering_six` is a
corollary of `not_signBlindGoodTripleCovering_six`, and every certificate whose
hypothesis lands inside the sign-blind body dies with it. Reading that as "no
sign-blind certificate whatsoever" needs one measured input — that both product signs
really occur among all-heavy designs sharing the same squares — flagged where the body
is defined. What the discarded sign carried is exact: at a distinct icosahedral
triple the bracket is `−7/20 + 2 rho rho rho`, a negative constant plus an oriented
product, and domination holds iff `7/40 ≤ rho_ab rho_ac rho_bc`
(`icosaDesign_dominates_iff_pairingProduct`) — the magnitude being the same at every
triple, the verdict is decided by the sign alone.

**Why the legs must be decided exactly.** At the doubly critical tetrahedral design
the tie leg is exactly zero and finite precision cannot decide its sign at any
depth: `mpmath` eigenvalues of the gap return `−4.59e−41` at `40` digits (a false
refutation) and `+2.11e−81` at `80`. The sign at an exact zero OSCILLATES with both
precision and routine — an independent rerun gets `20` of `35` triples wrong at `40`
and at `200` digits but `0` of `35` at `80`, and the eigen and SVD routes disagree
with each other at one precision — so the earlier "`20` of `35` at `80` digits"
reading is implementation-specific and is withdrawn. The CONCLUSION is unaffected and
in fact strengthened. Only the exact rational sign test on the
characteristic coefficients agrees with the truth on all `35`. The decision
procedure for both legs must therefore be exact rational arithmetic on
`discriminantTrace` and `discriminantTie`, never a numeric eigenvalue bound.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Quantitative.DecisionAtlasSevenThree
import Gtz.Quantitative.RealnessEngine
import Gtz.Reduction.RankFourWindow
import Gtz.Ties.SevenThreeTieLocus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ### The pair leg: the `2×2` gap minor -/

/-- The **pair minor** `u_c u_d − p_cd²`: the `2×2` principal minor of `Gram − I` at
a pair of atoms. Nonnegativity of every pair minor is the EDGE half of domination;
`discriminantTie` is the TRIPLE half. -/
def pairMinor (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) : ℝ :=
  heavyExcess D atomFirst * heavyExcess D atomSecond
    - atomPairing D atomFirst atomSecond ^ 2

theorem pairMinor_comm (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    pairMinor D atomFirst atomSecond = pairMinor D atomSecond atomFirst := by
  simp only [pairMinor, atomPairing_comm D atomFirst atomSecond]
  ring

/-- The trace leg is the sum of the two pair minors at the pivot — so the trace leg
carries no information beyond the two edges it touches. -/
theorem discriminantTrace_eq_pairMinor_add (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    discriminantTrace D pivot pairFirst pairSecond
      = pairMinor D pivot pairFirst + pairMinor D pivot pairSecond := by
  simp only [discriminantTrace, pairMinor]

/-- **The Schur identity behind the edge/triple split** (pure `ring`): the product
of the two pivot pair minors is the pivot excess times the tie leg, plus a square.
The `2×2` matrix-determinant lemma, in the six scalars of the triple. -/
theorem pairMinor_product_eq_tieSchur (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    pairMinor D pivot pairFirst * pairMinor D pivot pairSecond
      = heavyExcess D pivot * discriminantTie D pivot pairFirst pairSecond
        + (heavyExcess D pivot * atomPairing D pairFirst pairSecond
            - atomPairing D pivot pairFirst * atomPairing D pivot pairSecond) ^ 2 := by
  simp only [pairMinor, discriminantTie]
  ring

/-- The tie leg is unchanged when the two non-pivot atoms are exchanged; together
with `discriminantTie_swap` this makes it symmetric in all three atoms, as befits a
determinant. -/
theorem discriminantTie_swapPair (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    discriminantTie D pivot pairFirst pairSecond
      = discriminantTie D pivot pairSecond pairFirst := by
  simp only [discriminantTie, atomPairing_comm D pairSecond pairFirst]
  ring

/-! ### The three pair predicates: the edges of the three nested graphs -/

/-- A pair is **compatible** when its gap minor is nonnegative, i.e. `|rho| ≤ 1`.
Necessary for the pair to sit inside any dominating triple
(`pairMinor_nonneg_of_dominates`), so an incompatible pair is an edge no triangle
can use. -/
def IsCompatiblePair (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) : Prop :=
  0 ≤ pairMinor D atomFirst atomSecond

/-- A pair is **box-good** when `4 p² ≤ u u`, i.e. `|rho| ≤ 1/2`. The
multiplier-degree-zero Handelman condition; stated in exactly the shape
`dominates_of_dominantPairings` consumes. NON-STRICT by necessity: the regular
tetrahedron and its `(7,3)` split have `4 p² = u u` on every different-direction
pair, so a strict reading certifies nothing at the campaign's tie
(`splitSevenDesign_no_strictBoxGoodPair`). -/
def IsBoxGoodPair (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) : Prop :=
  4 * atomPairing D atomFirst atomSecond ^ 2
    ≤ heavyExcess D atomFirst * heavyExcess D atomSecond

/-- The **box leg** `u u − 4 p²`, the signed quantity whose sign the box condition
tests. Recorded separately because the refutation is quantitative: the leg is
exactly `−16/5` at every icosahedral pair. -/
def boxSlack (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) : ℝ :=
  heavyExcess D atomFirst * heavyExcess D atomSecond
    - 4 * atomPairing D atomFirst atomSecond ^ 2

theorem isBoxGoodPair_iff_boxSlack_nonneg (D : WeightedDesign m 3)
    (atomFirst atomSecond : Fin m) :
    IsBoxGoodPair D atomFirst atomSecond ↔ 0 ≤ boxSlack D atomFirst atomSecond := by
  simp only [IsBoxGoodPair, boxSlack, sub_nonneg]

theorem isBoxGoodPair_comm (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    IsBoxGoodPair D atomFirst atomSecond ↔ IsBoxGoodPair D atomSecond atomFirst := by
  rw [IsBoxGoodPair, IsBoxGoodPair, atomPairing_comm D atomFirst atomSecond,
    mul_comm (heavyExcess D atomSecond) (heavyExcess D atomFirst)]

theorem isCompatiblePair_comm (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    IsCompatiblePair D atomFirst atomSecond ↔ IsCompatiblePair D atomSecond atomFirst := by
  rw [IsCompatiblePair, IsCompatiblePair, pairMinor_comm]

/-- Box-good implies compatible: the box graph is a subgraph of the compatible
graph, with a factor-four margin on every edge it owns. -/
theorem isCompatiblePair_of_isBoxGoodPair (D : WeightedDesign m 3)
    {atomFirst atomSecond : Fin m} (hfirstHeavy : 1 < leverageOf (D.atom atomFirst))
    (hsecondHeavy : 1 < leverageOf (D.atom atomSecond))
    (hbox : IsBoxGoodPair D atomFirst atomSecond) :
    IsCompatiblePair D atomFirst atomSecond := by
  have hfirstPos : 0 < heavyExcess D atomFirst := by rw [heavyExcess]; linarith
  have hsecondPos : 0 < heavyExcess D atomSecond := by rw [heavyExcess]; linarith
  rw [IsCompatiblePair, pairMinor]
  rw [IsBoxGoodPair] at hbox
  linarith [mul_pos hfirstPos hsecondPos, sq_nonneg (atomPairing D atomFirst atomSecond)]

/-! ### No graph edge joins two copies of one atom

Both pair conditions FAIL when the two atoms carry the same vector, because the
pairing is then the full leverage while the excess product is the square of the
leverage minus one. This is what makes the graph coverings size-monotone: a
replicated atom contributes a vertex joined to nothing new. -/

/-- A pair of atoms carrying the same vector is never box-good. -/
theorem not_isBoxGoodPair_of_atom_eq (D : WeightedDesign m 3) {atomFirst atomSecond : Fin m}
    (hfirstHeavy : 1 < leverageOf (D.atom atomFirst))
    (hsame : D.atom atomFirst = D.atom atomSecond) :
    ¬ IsBoxGoodPair D atomFirst atomSecond := by
  have hpairing : atomPairing D atomFirst atomSecond = leverageOf (D.atom atomFirst) := by
    rw [atomPairing, ← hsame, leverageOf, ← dotProduct_self_eq_sum_sq]
  have hexcessSecond : heavyExcess D atomSecond = leverageOf (D.atom atomFirst) - 1 := by
    rw [heavyExcess, ← hsame]
  rw [IsBoxGoodPair, hpairing, heavyExcess, hexcessSecond]
  intro hbox
  nlinarith [hbox, hfirstHeavy]

/-- A pair of atoms carrying the same vector is never compatible either. -/
theorem not_isCompatiblePair_of_atom_eq (D : WeightedDesign m 3)
    {atomFirst atomSecond : Fin m} (hfirstHeavy : 1 < leverageOf (D.atom atomFirst))
    (hsame : D.atom atomFirst = D.atom atomSecond) :
    ¬ IsCompatiblePair D atomFirst atomSecond := by
  have hpairing : atomPairing D atomFirst atomSecond = leverageOf (D.atom atomFirst) := by
    rw [atomPairing, ← hsame, leverageOf, ← dotProduct_self_eq_sum_sq]
  have hexcessSecond : heavyExcess D atomSecond = leverageOf (D.atom atomFirst) - 1 := by
    rw [heavyExcess, ← hsame]
  rw [IsCompatiblePair, pairMinor, hpairing, heavyExcess, hexcessSecond]
  intro hcompatible
  nlinarith [hcompatible, hfirstHeavy]

/-! ### The triangles -/

/-- A **box-good triangle**: all three pairs box-good. Sufficient for domination
(`dominates_of_isBoxGoodTriangle`). -/
def IsBoxGoodTriangle (D : WeightedDesign m 3) (first second third : Fin m) : Prop :=
  IsBoxGoodPair D first second ∧ IsBoxGoodPair D first third
    ∧ IsBoxGoodPair D second third

/-- A **compatible triangle**: all three pairs compatible. Necessary for domination
(`isCompatibleTriangle_of_dominates`). -/
def IsCompatibleTriangle (D : WeightedDesign m 3) (first second third : Fin m) : Prop :=
  IsCompatiblePair D first second ∧ IsCompatiblePair D first third
    ∧ IsCompatiblePair D second third

/-- An **elliptope-good triangle**: three compatible edges plus the triple's
normalized pairing vector inside the `3×3` elliptope. Equivalent to domination at a
heavy triple (`dominates_triple_iff_isElliptopeGoodTriangle`), hence neither
sufficient-only nor necessary-only: it is the covering itself, in graph form. -/
def IsElliptopeGoodTriangle (D : WeightedDesign m 3) (first second third : Fin m) : Prop :=
  IsCompatibleTriangle D first second third ∧ 0 ≤ discriminantTie D first second third

/-! ### Sufficiency: a box-good triangle dominates -/

/-- **The Handelman multiplier-degree-zero certificate, in graph form.** A triangle
of the box-good graph on distinct heavy atoms gives a dominating triple. This is
`dominates_of_dominantPairings` — diagonal dominance of the `3×3` gap in the scaled
variables, where `|p_cd| ≤ (1/2) sqrt(u_c u_d)` at every pair is exactly the
dominance condition — read through the graph predicates. -/
theorem dominates_of_isBoxGoodTriangle {D : WeightedDesign m 3} (hheavy : AllHeavy D)
    {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (htriangle : IsBoxGoodTriangle D first second third) :
    Dominates D {first, second, third} :=
  dominates_of_dominantPairings D hfirstSecond hfirstThird hsecondThird
    (hheavy first) (hheavy second) (hheavy third)
    htriangle.1 htriangle.2.1 htriangle.2.2

/-! ### Necessity: a dominating triple has compatible edges -/

/-- **Each pair minor at the pivot is nonnegative on a dominating triple.** The two
pivot minors have nonnegative SUM (the trace leg) and nonnegative PRODUCT (the
Schur identity, since the tie leg is nonnegative and the pivot excess positive), so
neither can be negative. -/
theorem pairMinor_nonneg_of_dominates (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    (hdominates : Dominates D {pivot, pairFirst, pairSecond}) :
    0 ≤ pairMinor D pivot pairFirst := by
  obtain ⟨htrace, htie⟩ := (dominates_triple_iff_discriminantSystem D hpivotFirst
    hpivotSecond hpairDistinct hpivotHeavy).mp hdominates
  have hpivotPos : 0 < heavyExcess D pivot := by rw [heavyExcess]; linarith
  have hsum : 0 ≤ pairMinor D pivot pairFirst + pairMinor D pivot pairSecond := by
    rw [← discriminantTrace_eq_pairMinor_add]
    exact htrace
  have hproduct : 0 ≤ pairMinor D pivot pairFirst * pairMinor D pivot pairSecond := by
    rw [pairMinor_product_eq_tieSchur]
    have htieScaled : 0 ≤ heavyExcess D pivot
        * discriminantTie D pivot pairFirst pairSecond := mul_nonneg hpivotPos.le htie
    linarith [htieScaled, sq_nonneg (heavyExcess D pivot
      * atomPairing D pairFirst pairSecond
      - atomPairing D pivot pairFirst * atomPairing D pivot pairSecond)]
  rcases le_or_gt 0 (pairMinor D pivot pairFirst) with hnonneg | hneg
  · exact hnonneg
  · rcases le_or_gt (pairMinor D pivot pairSecond) 0 with hsecondNonpos | hsecondPos
    · linarith
    · nlinarith [hproduct, mul_pos (neg_pos.mpr hneg) hsecondPos]

/-- **Domination forces every edge of the triple to be compatible.** Read at each of
the three pivots in turn. -/
theorem isCompatibleTriangle_of_dominates {D : WeightedDesign m 3} (hheavy : AllHeavy D)
    {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hdominates : Dominates D {first, second, third}) :
    IsCompatibleTriangle D first second third := by
  have hswapTail : ({first, third, second} : Finset (Fin m)) = {first, second, third} := by
    rw [Finset.pair_comm third second]
  have hrotate : ({second, third, first} : Finset (Fin m)) = {first, second, third} := by
    rw [Finset.pair_comm third first, Finset.insert_comm]
  refine ⟨pairMinor_nonneg_of_dominates D hfirstSecond hfirstThird hsecondThird
      (hheavy first) hdominates, ?_, ?_⟩
  · refine pairMinor_nonneg_of_dominates D hfirstThird hfirstSecond hsecondThird.symm
      (hheavy first) ?_
    rw [hswapTail]
    exact hdominates
  · refine pairMinor_nonneg_of_dominates D hsecondThird hfirstSecond.symm hfirstThird.symm
      (hheavy second) ?_
    rw [hrotate]
    exact hdominates

/-! ### The reformulation: domination is three edges and one triple -/

/-- **THE GRAPH REFORMULATION.** A triple of distinct heavy atoms dominates iff all
three of its pair minors are nonnegative and its tie leg is nonnegative. The
condition splits into three EDGE conditions of degree two and one TRIPLE condition
of degree three, which is what makes the covering a graph question at all. The
edge conditions are redundant one at a time — two of them plus the tie leg imply the
third, as the backward direction shows by never using it — but the symmetric form is
the one the graph reading needs. -/
theorem dominates_triple_iff_isElliptopeGoodTriangle {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    Dominates D {first, second, third}
      ↔ IsElliptopeGoodTriangle D first second third := by
  constructor
  · intro hdominates
    refine ⟨isCompatibleTriangle_of_dominates hheavy hfirstSecond hfirstThird
      hsecondThird hdominates, ?_⟩
    exact ((dominates_triple_iff_discriminantSystem D hfirstSecond hfirstThird
      hsecondThird (hheavy first)).mp hdominates).2
  · rintro ⟨⟨hedgeFirstSecond, hedgeFirstThird, _⟩, htie⟩
    refine (dominates_triple_iff_discriminantSystem D hfirstSecond hfirstThird
      hsecondThird (hheavy first)).mpr ⟨?_, htie⟩
    rw [discriminantTrace_eq_pairMinor_add]
    rw [IsCompatiblePair] at hedgeFirstSecond hedgeFirstThird
    linarith

/-- The box graph is a subgraph of the elliptope-good graph, at the level of
triangles. -/
theorem isElliptopeGoodTriangle_of_isBoxGoodTriangle {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (htriangle : IsBoxGoodTriangle D first second third) :
    IsElliptopeGoodTriangle D first second third :=
  (dominates_triple_iff_isElliptopeGoodTriangle hheavy hfirstSecond hfirstThird
    hsecondThird).mp
      (dominates_of_isBoxGoodTriangle hheavy hfirstSecond hfirstThird hsecondThird
        htriangle)

/-- The elliptope-good graph is a subgraph of the compatible graph, by definition. -/
theorem isCompatibleTriangle_of_isElliptopeGoodTriangle {D : WeightedDesign m 3}
    {first second third : Fin m}
    (htriangle : IsElliptopeGoodTriangle D first second third) :
    IsCompatibleTriangle D first second third := htriangle.1

/-! ### The elliptope: the leverages factor out completely -/

/-- The **normalized pairing** `rho_cd = p_cd / sqrt(u_c u_d)`: the correlation the
elliptope reading is about. -/
noncomputable def normalizedPairing (D : WeightedDesign m 3)
    (atomFirst atomSecond : Fin m) : ℝ :=
  atomPairing D atomFirst atomSecond
    / Real.sqrt (heavyExcess D atomFirst * heavyExcess D atomSecond)

/-- The determinant of the `3×3` correlation matrix with the three given
off-diagonal entries. Its nonnegativity is the DETERMINANT HALF of elliptope
membership, not membership itself: `E_3` also demands `|rho| ≤ 1` on each pair. At
`rho ≡ 3/2` the bracket is `+1 ≥ 0` while the correlation matrix has eigenvalues
`{4,−1/2,−1/2}`. Conjoin `IsCompatibleTriangle` for the genuine condition. -/
def elliptopeBracket (rhoFirst rhoSecond rhoThird : ℝ) : ℝ :=
  1 - rhoFirst ^ 2 - rhoSecond ^ 2 - rhoThird ^ 2
    + 2 * (rhoFirst * rhoSecond * rhoThird)

theorem normalizedPairing_sq (D : WeightedDesign m 3) {atomFirst atomSecond : Fin m}
    (hfirstPos : 0 < heavyExcess D atomFirst) (hsecondPos : 0 < heavyExcess D atomSecond) :
    normalizedPairing D atomFirst atomSecond ^ 2
      = atomPairing D atomFirst atomSecond ^ 2
          / (heavyExcess D atomFirst * heavyExcess D atomSecond) := by
  rw [normalizedPairing, div_pow, Real.sq_sqrt (mul_pos hfirstPos hsecondPos).le]

/-- The three square roots multiply back to the excess product: this is why the
leverages cancel from the triple term as well as from the squares. -/
theorem normalizedPairing_product (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotPos : 0 < heavyExcess D pivot)
    (hfirstPos : 0 < heavyExcess D pairFirst) (hsecondPos : 0 < heavyExcess D pairSecond) :
    normalizedPairing D pivot pairFirst * normalizedPairing D pivot pairSecond
        * normalizedPairing D pairFirst pairSecond
      = atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
            * atomPairing D pairFirst pairSecond
          / (heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond) := by
  have hsqrtProduct : Real.sqrt (heavyExcess D pivot * heavyExcess D pairFirst)
        * Real.sqrt (heavyExcess D pivot * heavyExcess D pairSecond)
        * Real.sqrt (heavyExcess D pairFirst * heavyExcess D pairSecond)
      = heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond := by
    rw [← Real.sqrt_mul (mul_pos hpivotPos hfirstPos).le,
      ← Real.sqrt_mul (mul_pos (mul_pos hpivotPos hfirstPos)
        (mul_pos hpivotPos hsecondPos)).le,
      show heavyExcess D pivot * heavyExcess D pairFirst
            * (heavyExcess D pivot * heavyExcess D pairSecond)
            * (heavyExcess D pairFirst * heavyExcess D pairSecond)
          = (heavyExcess D pivot * heavyExcess D pairFirst
              * heavyExcess D pairSecond) ^ 2 from by ring,
      Real.sqrt_sq (mul_pos (mul_pos hpivotPos hfirstPos) hsecondPos).le]
  rw [normalizedPairing, normalizedPairing, normalizedPairing, div_mul_div_comm,
    div_mul_div_comm, hsqrtProduct]

/-- **THE LEVERAGES FACTOR OUT COMPLETELY.** The tie leg is the excess product times
the elliptope determinant of the three normalized pairings. Degree three in three
variables per triple, with the six leverages appearing only as a positive scalar. -/
theorem discriminantTie_eq_excessProduct_mul_elliptopeBracket (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotPos : 0 < heavyExcess D pivot)
    (hfirstPos : 0 < heavyExcess D pairFirst) (hsecondPos : 0 < heavyExcess D pairSecond) :
    discriminantTie D pivot pairFirst pairSecond
      = heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond
        * elliptopeBracket (normalizedPairing D pivot pairFirst)
            (normalizedPairing D pivot pairSecond)
            (normalizedPairing D pairFirst pairSecond) := by
  have hpivotNe : heavyExcess D pivot ≠ 0 := ne_of_gt hpivotPos
  have hfirstNe : heavyExcess D pairFirst ≠ 0 := ne_of_gt hfirstPos
  have hsecondNe : heavyExcess D pairSecond ≠ 0 := ne_of_gt hsecondPos
  rw [elliptopeBracket, normalizedPairing_sq D hpivotPos hfirstPos,
    normalizedPairing_sq D hpivotPos hsecondPos,
    normalizedPairing_sq D hfirstPos hsecondPos,
    normalizedPairing_product D hpivotPos hfirstPos hsecondPos,
    discriminantTie_eq_gramMinorForm]
  field_simp

/-- **The tie leg is the elliptope DETERMINANT.** At an all-heavy triple,
`0 ≤ discriminantTie` is equivalent to nonnegativity of the correlation determinant.
It is NOT equivalent to elliptope membership: the `|rho| ≤ 1` conjunct is separate and
load-bearing (`rho ≡ 3/2` satisfies the bracket and fails to dominate). -/
theorem discriminantTie_nonneg_iff_elliptopeBracket_nonneg (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotPos : 0 < heavyExcess D pivot)
    (hfirstPos : 0 < heavyExcess D pairFirst) (hsecondPos : 0 < heavyExcess D pairSecond) :
    0 ≤ discriminantTie D pivot pairFirst pairSecond
      ↔ 0 ≤ elliptopeBracket (normalizedPairing D pivot pairFirst)
          (normalizedPairing D pivot pairSecond)
          (normalizedPairing D pairFirst pairSecond) := by
  rw [discriminantTie_eq_excessProduct_mul_elliptopeBracket D hpivotPos hfirstPos
    hsecondPos]
  exact mul_nonneg_iff_of_pos_left (mul_pos (mul_pos hpivotPos hfirstPos) hsecondPos)

/-- The box condition, normalized: the box graph is the graph of pairs at
correlation at most one half in absolute value. -/
theorem isBoxGoodPair_iff_normalizedPairing_sq_le (D : WeightedDesign m 3)
    {atomFirst atomSecond : Fin m} (hfirstPos : 0 < heavyExcess D atomFirst)
    (hsecondPos : 0 < heavyExcess D atomSecond) :
    IsBoxGoodPair D atomFirst atomSecond
      ↔ normalizedPairing D atomFirst atomSecond ^ 2 ≤ 1 / 4 := by
  rw [IsBoxGoodPair, normalizedPairing_sq D hfirstPos hsecondPos,
    div_le_iff₀ (mul_pos hfirstPos hsecondPos)]
  constructor <;> intro hbound <;> linarith

theorem isBoxGoodPair_iff_abs_normalizedPairing_le_half (D : WeightedDesign m 3)
    {atomFirst atomSecond : Fin m} (hfirstPos : 0 < heavyExcess D atomFirst)
    (hsecondPos : 0 < heavyExcess D atomSecond) :
    IsBoxGoodPair D atomFirst atomSecond
      ↔ |normalizedPairing D atomFirst atomSecond| ≤ 1 / 2 := by
  rw [isBoxGoodPair_iff_normalizedPairing_sq_le D hfirstPos hsecondPos]
  constructor
  · intro hsquare
    nlinarith [abs_nonneg (normalizedPairing D atomFirst atomSecond),
      sq_abs (normalizedPairing D atomFirst atomSecond), hsquare]
  · intro habs
    nlinarith [abs_nonneg (normalizedPairing D atomFirst atomSecond),
      sq_abs (normalizedPairing D atomFirst atomSecond), habs]

/-- The compatibility condition, normalized: the compatible graph is the graph of
pairs at correlation at most one in absolute value. -/
theorem isCompatiblePair_iff_abs_normalizedPairing_le_one (D : WeightedDesign m 3)
    {atomFirst atomSecond : Fin m} (hfirstPos : 0 < heavyExcess D atomFirst)
    (hsecondPos : 0 < heavyExcess D atomSecond) :
    IsCompatiblePair D atomFirst atomSecond
      ↔ |normalizedPairing D atomFirst atomSecond| ≤ 1 := by
  have hsquare : normalizedPairing D atomFirst atomSecond ^ 2
      = atomPairing D atomFirst atomSecond ^ 2
          / (heavyExcess D atomFirst * heavyExcess D atomSecond) :=
    normalizedPairing_sq D hfirstPos hsecondPos
  have hstep : IsCompatiblePair D atomFirst atomSecond
      ↔ normalizedPairing D atomFirst atomSecond ^ 2 ≤ 1 := by
    rw [IsCompatiblePair, pairMinor, hsquare,
      div_le_iff₀ (mul_pos hfirstPos hsecondPos)]
    constructor <;> intro hbound <;> linarith
  rw [hstep]
  constructor
  · intro hsquareBound
    nlinarith [abs_nonneg (normalizedPairing D atomFirst atomSecond),
      sq_abs (normalizedPairing D atomFirst atomSecond), hsquareBound]
  · intro habs
    nlinarith [abs_nonneg (normalizedPairing D atomFirst atomSecond),
      sq_abs (normalizedPairing D atomFirst atomSecond), habs]

/-! ### The covering questions -/

/-- **The box-good triangle covering at size `m`**: every all-heavy weighted `(m,3)`
design has a triangle in its box-good graph. Refuted at every size at least six
(`not_boxGoodTriangleCovering_of_six_le`). -/
def BoxGoodTriangleCovering (m : ℕ) : Prop :=
  ∀ D : WeightedDesign m 3, AllHeavy D →
    ∃ first second third : Fin m,
      first ≠ second ∧ first ≠ third ∧ second ≠ third
        ∧ IsBoxGoodTriangle D first second third

/-- **The elliptope-good triangle covering at size `m`**: every all-heavy weighted
`(m,3)` design has a triangle in its elliptope-good graph. Equivalent to the
all-heavy statement at that size, hence at `m = 7` to the whole of rank three. -/
def ElliptopeGoodTriangleCovering (m : ℕ) : Prop :=
  ∀ D : WeightedDesign m 3, AllHeavy D →
    ∃ first second third : Fin m,
      first ≠ second ∧ first ≠ third ∧ second ≠ third
        ∧ IsElliptopeGoodTriangle D first second third

/-- **The compatible triangle covering at size `m`**: every all-heavy weighted
`(m,3)` design has a triangle in its compatible graph. A NECESSARY condition for
the conjecture, so a triangle-free compatible graph would refute it. -/
def CompatibleTriangleCovering (m : ℕ) : Prop :=
  ∀ D : WeightedDesign m 3, AllHeavy D →
    ∃ first second third : Fin m,
      first ≠ second ∧ first ≠ third ∧ second ≠ third
        ∧ IsCompatibleTriangle D first second third

/-- The elliptope-good graph covering IS the all-heavy statement. -/
theorem elliptopeGoodTriangleCovering_iff_gtzWeightedHeavy (size : ℕ) :
    ElliptopeGoodTriangleCovering size ↔ GtzWeightedHeavy size 3 := by
  constructor
  · intro hcover D hheavy
    obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, htriangle⟩ :=
      hcover D hheavy
    refine ⟨{first, second, third}, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
        Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]
    · exact (dominates_triple_iff_isElliptopeGoodTriangle hheavy hfirstSecond
        hfirstThird hsecondThird).mpr htriangle
  · intro hgtz D hheavy
    obtain ⟨C, hcard, hdominates⟩ := hgtz D hheavy
    obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hCeq⟩ :=
      Finset.card_eq_three.mp hcard
    subst hCeq
    exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
      (dominates_triple_iff_isElliptopeGoodTriangle hheavy hfirstSecond hfirstThird
        hsecondThird).mp hdominates⟩

/-- The elliptope-good graph covering is the discriminant covering, verbatim. -/
theorem elliptopeGoodTriangleCovering_iff_discriminantCovering (size : ℕ) :
    ElliptopeGoodTriangleCovering size ↔ DiscriminantCovering size := by
  rw [elliptopeGoodTriangleCovering_iff_gtzWeightedHeavy,
    gtzWeightedHeavy_three_iff_discriminantCovering]

/-- **THE COVERING IS A TRIANGLE QUESTION.** GTZ at rank three, for every `n`, IS
the single sentence: every all-heavy weighted `(7,3)` design has a triangle in its
elliptope-good graph — three edges at correlation at most one and one triple inside
the `3×3` elliptope, among `35` candidate triangles on `7` vertices. -/
theorem elliptopeGoodTriangleCovering_seven_iff_rank_three :
    ElliptopeGoodTriangleCovering 7 ↔ GtzWeightedAll 3 := by
  rw [elliptopeGoodTriangleCovering_iff_discriminantCovering]
  exact discriminantCovering_seven_iff_rank_three

/-- Box-good triangles suffice, so the box covering would prove the conjecture at
that size. -/
theorem discriminantCovering_of_boxGoodTriangleCovering {size : ℕ}
    (hcover : BoxGoodTriangleCovering size) : DiscriminantCovering size := by
  refine (elliptopeGoodTriangleCovering_iff_discriminantCovering size).mp ?_
  intro D hheavy
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, htriangle⟩ :=
    hcover D hheavy
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    isElliptopeGoodTriangle_of_isBoxGoodTriangle hheavy hfirstSecond hfirstThird
      hsecondThird htriangle⟩

/-- The compatible covering is implied by the elliptope-good covering, which is the
conjecture: compatibility is the necessary half. -/
theorem compatibleTriangleCovering_of_gtzWeightedHeavy {size : ℕ}
    (hgtz : GtzWeightedHeavy size 3) : CompatibleTriangleCovering size := by
  intro D hheavy
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, htriangle⟩ :=
    (elliptopeGoodTriangleCovering_iff_gtzWeightedHeavy size).mpr hgtz D hheavy
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    isCompatibleTriangle_of_isElliptopeGoodTriangle htriangle⟩

/-- **The remaining refutation channel.** An all-heavy weighted `(size,3)` design
whose compatible graph is triangle-free would refute GTZ at rank three outright: an
incompatible pair kills every triple containing it, so no triple could dominate.
Search has not found one — `300` SLSQP restarts saturate at `max|rho| =
0.999888801049` without crossing `1`. -/
theorem not_gtzWeightedAll_three_of_no_compatibleTriangle {size : ℕ}
    (hfail : ¬ CompatibleTriangleCovering size) : ¬ GtzWeightedAll 3 := by
  intro hrank
  exact hfail (compatibleTriangleCovering_of_gtzWeightedHeavy (fun D _ => hrank size D))

/-- The elliptope-good covering is size-monotone, through the all-heavy statement
it is equivalent to. -/
theorem elliptopeGoodTriangleCovering_of_le {size larger : ℕ} (hle : size ≤ larger)
    (hcover : ElliptopeGoodTriangleCovering larger) : ElliptopeGoodTriangleCovering size :=
  (elliptopeGoodTriangleCovering_iff_gtzWeightedHeavy size).mpr
    (gtzWeightedHeavy_of_le hle
      ((elliptopeGoodTriangleCovering_iff_gtzWeightedHeavy larger).mp hcover))

/-! ### Size monotonicity of the box covering, through atom splitting

`replicatedDesign` duplicates the atom VECTOR and halves only its WEIGHT, so every
leverage — hence every excess, every pairing and every normalized pairing — is
unchanged, and the box-good graph of the split design is the box-good graph of the
original with one vertex DOUBLED. The doubled vertex carries no new edge, because
a pair of atoms with the same vector is never box-good
(`not_isBoxGoodPair_of_atom_eq`), so a triangle upstairs merges injectively to a
triangle downstairs. -/

/-- The heavy excess depends only on the atom vector, across designs of any sizes. -/
theorem heavyExcess_eq_of_atom_eq {sizeLeft sizeRight : ℕ}
    (designLeft : WeightedDesign sizeLeft 3) (designRight : WeightedDesign sizeRight 3)
    {indexLeft : Fin sizeLeft} {indexRight : Fin sizeRight}
    (hatom : designLeft.atom indexLeft = designRight.atom indexRight) :
    heavyExcess designLeft indexLeft = heavyExcess designRight indexRight := by
  rw [heavyExcess, heavyExcess, hatom]

/-- The atom pairing depends only on the two atom vectors, across designs of any
sizes. -/
theorem atomPairing_eq_of_atom_eq {sizeLeft sizeRight : ℕ}
    (designLeft : WeightedDesign sizeLeft 3) (designRight : WeightedDesign sizeRight 3)
    {firstLeft secondLeft : Fin sizeLeft} {firstRight secondRight : Fin sizeRight}
    (hfirst : designLeft.atom firstLeft = designRight.atom firstRight)
    (hsecond : designLeft.atom secondLeft = designRight.atom secondRight) :
    atomPairing designLeft firstLeft secondLeft
      = atomPairing designRight firstRight secondRight := by
  rw [atomPairing, atomPairing, hfirst, hsecond]

theorem isBoxGoodPair_iff_of_atom_eq {sizeLeft sizeRight : ℕ}
    (designLeft : WeightedDesign sizeLeft 3) (designRight : WeightedDesign sizeRight 3)
    {firstLeft secondLeft : Fin sizeLeft} {firstRight secondRight : Fin sizeRight}
    (hfirst : designLeft.atom firstLeft = designRight.atom firstRight)
    (hsecond : designLeft.atom secondLeft = designRight.atom secondRight) :
    IsBoxGoodPair designLeft firstLeft secondLeft
      ↔ IsBoxGoodPair designRight firstRight secondRight := by
  rw [IsBoxGoodPair, IsBoxGoodPair,
    heavyExcess_eq_of_atom_eq designLeft designRight hfirst,
    heavyExcess_eq_of_atom_eq designLeft designRight hsecond,
    atomPairing_eq_of_atom_eq designLeft designRight hfirst hsecond]

/-- Box-goodness in the split design is box-goodness of the merged pair. -/
theorem isBoxGoodPair_replicatedDesign_iff (D : WeightedDesign m 3) (which : Fin m)
    (left right : Fin (m + 1)) :
    IsBoxGoodPair (replicatedDesign D which) left right
      ↔ IsBoxGoodPair D (replicationMerge which left) (replicationMerge which right) :=
  isBoxGoodPair_iff_of_atom_eq _ _ (atom_replicationMerge D which left).symm
    (atom_replicationMerge D which right).symm

/-- A box-good pair of the split design cannot merge to a single atom: that would
make the two atom vectors equal, and no pair of equal vectors is box-good. -/
theorem replicationMerge_ne_of_isBoxGoodPair {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) (which : Fin m) {left right : Fin (m + 1)}
    (hbox : IsBoxGoodPair (replicatedDesign D which) left right) :
    replicationMerge which left ≠ replicationMerge which right := by
  intro hmerge
  refine not_isBoxGoodPair_of_atom_eq (replicatedDesign D which)
    (replicatedDesign_allHeavy D which hheavy left) ?_ hbox
  rw [← atom_replicationMerge, ← atom_replicationMerge, hmerge]

/-- **The box covering is monotone in the number of atoms, one step.** -/
theorem boxGoodTriangleCovering_of_succ (hcover : BoxGoodTriangleCovering (m + 1)) :
    BoxGoodTriangleCovering m := by
  intro D hheavy
  have hrankLe : 3 ≤ m := rank_le_of_design D
  have hsizePos : 0 < m := by omega
  let which : Fin m := ⟨0, hsizePos⟩
  obtain ⟨first, second, third, _, _, _, hboxFirstSecond, hboxFirstThird,
    hboxSecondThird⟩ :=
    hcover (replicatedDesign D which) (replicatedDesign_allHeavy D which hheavy)
  refine ⟨replicationMerge which first, replicationMerge which second,
    replicationMerge which third,
    replicationMerge_ne_of_isBoxGoodPair hheavy which hboxFirstSecond,
    replicationMerge_ne_of_isBoxGoodPair hheavy which hboxFirstThird,
    replicationMerge_ne_of_isBoxGoodPair hheavy which hboxSecondThird, ?_, ?_, ?_⟩
  · exact (isBoxGoodPair_replicatedDesign_iff D which first second).mp hboxFirstSecond
  · exact (isBoxGoodPair_replicatedDesign_iff D which first third).mp hboxFirstThird
  · exact (isBoxGoodPair_replicatedDesign_iff D which second third).mp hboxSecondThird

theorem boxGoodTriangleCovering_of_add (size gap : ℕ) :
    BoxGoodTriangleCovering (size + gap) → BoxGoodTriangleCovering size := by
  induction gap with
  | zero => intro hcover; simpa using hcover
  | succ previous ih =>
      intro hcover
      refine ih ?_
      have hreassociate : size + (previous + 1) = (size + previous) + 1 := by omega
      rw [hreassociate] at hcover
      exact boxGoodTriangleCovering_of_succ hcover

/-- **The box covering is monotone in the number of atoms.** So a refutation at any
size refutes every larger size, and the frontier size `7` is refuted by the
six-atom witness below. -/
theorem boxGoodTriangleCovering_of_le {size larger : ℕ} (hle : size ≤ larger)
    (hcover : BoxGoodTriangleCovering larger) : BoxGoodTriangleCovering size := by
  obtain ⟨gap, hgap⟩ := Nat.exists_eq_add_of_le hle
  rw [hgap] at hcover
  exact boxGoodTriangleCovering_of_add size gap hcover

/-! ### The refutation: the maximal real equiangular design has an EMPTY box graph -/

theorem icosaDesign_leverage (atomIndex : Fin 6) :
    leverageOf (icosaDesign.atom atomIndex) = 3 := by
  rw [icosaDesign_atom, leverageOf, ← dotProduct_self_eq_sum_sq]
  exact icosaAtom_leverage atomIndex

theorem icosaDesign_allHeavy : AllHeavy icosaDesign := by
  intro atomIndex
  rw [icosaDesign_leverage]
  norm_num

/-- Every icosahedral atom has heavy excess exactly `2`. -/
theorem icosaDesign_heavyExcess (atomIndex : Fin 6) :
    heavyExcess icosaDesign atomIndex = 2 := by
  rw [heavyExcess, icosaDesign_leverage]
  norm_num

/-- Every distinct icosahedral pair has squared pairing exactly `9/5` — squared
cosine `1/5` at leverage `3`, the real equiangular maximum. -/
theorem icosaDesign_atomPairing_sq_of_ne {atomFirst atomSecond : Fin 6}
    (hne : atomFirst ≠ atomSecond) :
    atomPairing icosaDesign atomFirst atomSecond ^ 2 = 9 / 5 := by
  rw [atomPairing, icosaDesign_atom]
  exact icosaAtom_dot_sq_of_ne hne

/-- **Every icosahedral box leg is exactly `−16/5`.** `2·2 − 4·(9/5) = −16/5`: the
box threshold at leverage `3` is `|cos| ≤ 1/3`, the icosahedral angle has
`|cos| = 1/√5`, and the gap is a factor `9/5`, not a knife edge. -/
theorem icosaDesign_boxSlack_of_ne {atomFirst atomSecond : Fin 6}
    (hne : atomFirst ≠ atomSecond) :
    boxSlack icosaDesign atomFirst atomSecond = -(16 / 5) := by
  rw [boxSlack, icosaDesign_heavyExcess, icosaDesign_heavyExcess,
    icosaDesign_atomPairing_sq_of_ne hne]
  norm_num

/-- The diagonal box leg is `−32`, so the emptiness statement needs no side
condition on the two indices. -/
theorem icosaDesign_boxSlack_self (atomIndex : Fin 6) :
    boxSlack icosaDesign atomIndex atomIndex = -32 := by
  rw [boxSlack, icosaDesign_heavyExcess, atomPairing_self, icosaDesign_leverage]
  norm_num

/-- **THE BOX-GOOD GRAPH OF THE MAXIMAL REAL EQUIANGULAR DESIGN IS EMPTY.** All
`15` pairs fail, by `16/5`. The Turán–Mantel counting attack needed only `9` of the
`21` pairs at size seven to be box-bad in order to conclude; here every pair is
box-bad, so the counting has no purchase at all. -/
theorem icosaDesign_no_isBoxGoodPair (atomFirst atomSecond : Fin 6) :
    ¬ IsBoxGoodPair icosaDesign atomFirst atomSecond := by
  rw [isBoxGoodPair_iff_boxSlack_nonneg]
  rcases eq_or_ne atomFirst atomSecond with hsame | hne
  · rw [hsame, icosaDesign_boxSlack_self]
    norm_num
  · rw [icosaDesign_boxSlack_of_ne hne]
    norm_num

/-- **THE BOX FORM OF THE COVERING IS FALSE at size six** — and the witness
dominates STRICTLY (`icosaDesign_strictly_dominates`), with margin `2 − 3/√5`, so
what the emptiness refutes is the certificate family, not the conjecture. -/
theorem not_boxGoodTriangleCovering_six : ¬ BoxGoodTriangleCovering 6 := by
  intro hcover
  obtain ⟨first, second, _, _, _, _, hbox, _, _⟩ := hcover icosaDesign icosaDesign_allHeavy
  exact icosaDesign_no_isBoxGoodPair first second hbox

/-- **The box form is false at every size from six upward**, by size monotonicity —
in particular at the frontier size `7`, where the whole of rank three lives. -/
theorem not_boxGoodTriangleCovering_of_six_le {size : ℕ} (hle : 6 ≤ size) :
    ¬ BoxGoodTriangleCovering size := fun hcover =>
  not_boxGoodTriangleCovering_six (boxGoodTriangleCovering_of_le hle hcover)

theorem not_boxGoodTriangleCovering_seven : ¬ BoxGoodTriangleCovering 7 :=
  not_boxGoodTriangleCovering_of_six_le (by norm_num)

/-- The seven-atom witness, explicitly: split one icosahedral atom into two
equal-weight copies. Leverages are unchanged, so it is all-heavy at leverage `3`,
and the two copies are joined by no box edge either. -/
noncomputable def icosaSevenDesign : WeightedDesign 7 3 := replicatedDesign icosaDesign 0

theorem icosaSevenDesign_allHeavy : AllHeavy icosaSevenDesign :=
  replicatedDesign_allHeavy icosaDesign 0 icosaDesign_allHeavy

/-- **All `21` pairs of the seven-atom icosahedral witness are box-bad.** Against
the `9` the Turán–Mantel counting needed: the attack fails by a factor `21/9`. -/
theorem icosaSevenDesign_no_isBoxGoodPair (atomFirst atomSecond : Fin 7) :
    ¬ IsBoxGoodPair icosaSevenDesign atomFirst atomSecond := fun hbox =>
  icosaDesign_no_isBoxGoodPair _ _
    ((isBoxGoodPair_replicatedDesign_iff icosaDesign 0 atomFirst atomSecond).mp hbox)

/-- The frontier-size refutation, read off the seven-atom witness directly rather
than through monotonicity. -/
theorem not_boxGoodTriangleCovering_seven_of_icosaSeven : ¬ BoxGoodTriangleCovering 7 := by
  intro hcover
  obtain ⟨first, second, _, _, _, _, hbox, _, _⟩ :=
    hcover icosaSevenDesign icosaSevenDesign_allHeavy
  exact icosaSevenDesign_no_isBoxGoodPair first second hbox

/-! ### Calibration at the tie: the box condition must stay non-strict -/

/-- Different-direction pairs of the `(7,3)` tie are box-good, exactly on the
boundary. -/
theorem splitSevenDesign_isBoxGoodPair_of_differentDirection {atomFirst atomSecond : Fin 7}
    (hdifferent : splitSevenDirection atomFirst ≠ splitSevenDirection atomSecond) :
    IsBoxGoodPair splitSevenDesign atomFirst atomSecond :=
  le_of_eq (splitSevenDesign_pairingBoundary_of_differentDirection hdifferent)

/-- The tie's box-good graph is the complete multipartite graph on its four
direction classes with multiplicities `(2,2,2,1)`, so it contains triangles: `{0,1,2}`
carries three different directions. -/
theorem splitSevenDesign_isBoxGoodTriangle : IsBoxGoodTriangle splitSevenDesign 0 1 2 :=
  ⟨splitSevenDesign_isBoxGoodPair_of_differentDirection (by decide),
    splitSevenDesign_isBoxGoodPair_of_differentDirection (by decide),
    splitSevenDesign_isBoxGoodPair_of_differentDirection (by decide)⟩

/-- The graph interface re-derives the known domination of `{0,1,2}` at the `(7,3)`
tie, confirming no slack is lost in the reformulation. -/
theorem splitSevenDesign_dominates_of_isBoxGoodTriangle :
    Dominates splitSevenDesign {0, 1, 2} :=
  dominates_of_isBoxGoodTriangle splitSevenDesign_allHeavy (by decide) (by decide)
    (by decide) splitSevenDesign_isBoxGoodTriangle

/-- **NON-STRICTNESS IS LOAD-BEARING.** At the `(7,3)` tie every box leg is exactly
`0` (different directions) or `−32` (same direction), so the STRICT box graph is
EMPTY and any strict reading of `BoxGoodTriangleCovering` is refuted at the frontier
size by the repo's own tie — while the non-strict reading survives there
(`splitSevenDesign_isBoxGoodTriangle`). The tetrahedral stratum sits ON the box
boundary from inside; the icosahedron sits a factor `9/5` outside. -/
theorem splitSevenDesign_no_strictBoxGoodPair (atomFirst atomSecond : Fin 7) :
    ¬ (4 * atomPairing splitSevenDesign atomFirst atomSecond ^ 2
        < heavyExcess splitSevenDesign atomFirst
          * heavyExcess splitSevenDesign atomSecond) := by
  rcases eq_or_ne (splitSevenDirection atomFirst) (splitSevenDirection atomSecond) with
    hsame | hdifferent
  · rw [splitSevenDesign_atomPairing_of_sameDirection hsame, splitSevenDesign_heavyExcess,
      splitSevenDesign_heavyExcess]
    norm_num
  · rw [splitSevenDesign_pairingBoundary_of_differentDirection hdifferent]
    exact lt_irrefl _

/-- The tie's box legs, both values, as the calibration record: `0` across
directions and `−32` within one. -/
theorem splitSevenDesign_boxSlack_of_differentDirection {atomFirst atomSecond : Fin 7}
    (hdifferent : splitSevenDirection atomFirst ≠ splitSevenDirection atomSecond) :
    boxSlack splitSevenDesign atomFirst atomSecond = 0 := by
  rw [boxSlack, splitSevenDesign_pairingBoundary_of_differentDirection hdifferent,
    sub_self]

theorem splitSevenDesign_boxSlack_of_sameDirection {atomFirst atomSecond : Fin 7}
    (hsame : splitSevenDirection atomFirst = splitSevenDirection atomSecond) :
    boxSlack splitSevenDesign atomFirst atomSecond = -32 := by
  rw [boxSlack, splitSevenDesign_atomPairing_of_sameDirection hsame,
    splitSevenDesign_heavyExcess, splitSevenDesign_heavyExcess]
  norm_num

/-! ### The sharp SIGN-BLIND certificate, and the exact reason no such certificate
can finish

Every certificate the campaign has tried reads only SQUARED pairings — the symmetric
box `|rho| ≤ 1/2` above, the anisotropic radius boxes of `dominates_of_radiusBox`, the
ball `rho_ab² + rho_ac² + rho_bc² ≤ 3/4` — so each keeps its verdict when the sign of
any one pairing is flipped. That whole family has one exact closure. Split the tie leg
into

  `excessGap = u_a u_b u_c − (u_c p_ab² + u_b p_ac² + u_a p_bc²)`,
  `discriminantTie = excessGap + 2 p_ab p_ac p_bc`

(`discriminantTie_eq_excessGap_add_tripleProduct`): the first summand is sign-blind and
the oriented product is the ONLY place a sign enters. So the weakest condition that
forces the tie leg at BOTH product signs — which is what a sign-blind hypothesis must
do whenever both signs are realisable at fixed squares — is

  `2 |p_ab p_ac p_bc| ≤ excessGap`   (`IsSignBlindGoodTriple`).

It is sound (`dominates_of_isSignBlindGoodTriple`) and it contains the box
(`isSignBlindGoodTriple_of_isBoxGoodTriangle`). Against the shipped radius boxes it is
NOT a strict gain: `IsSignBlindGoodTriple` unfolds to `Σrho² + 2|rho rho rho| ≤ 1`,
which is verbatim the `hadmissible` hypothesis of `dominates_of_radiusBox` at
`radius_i = |rho_i|`, and admissibility is decreasing in each radius, so the two are
LOGICALLY EQUIVALENT. The genuine contributions are (a) a radical-free reformulation —
unlike every
body linear in `rho`, which must adjoin `sqrt(u_c)`. Both sharp objects of the campaign
sit exactly ON its boundary at `2 |p p p| = 2 = excessGap`: the regular tetrahedron
(`tetraDesign_isSignBlindGoodTriple`) and the frontier-size `(7,3)` tie
(`splitSevenDesign_isSignBlindGoodTriple`), so non-strictness is load-bearing here for
the same reason as for the box.

The ball needs no separate theorem. Three-term AM-GM bounds the normalized product by
`(R/3)^{3/2}` at squared radius `R`, so a ball is sign-blind-good exactly when
`R + 2 (R/3)^{3/2} ≤ 1`, i.e. `R ≤ 3/4` with equality (`ballRadius_sharp`) — that is
where the Handelman radius `3/4` comes from. The containment is strict: the sign-blind
body also holds the degenerate face `rho = (1, 0, 0)`, of squared radius `1`.

**The sign-blind level is refuted outright, by the same object and by a wider margin
than the box.** At `icosaDesign` every excess is `2` and every squared pairing is at
least `9/5` — the diagonal included, where it is `9` — so

  `excessGap ≤ 8 − 54/5 = −14/5 < 0 ≤ 2 |p p p|`

(`icosaDesign_excessGap_le`, exact at `−14/5` on a distinct triple). All `216` ordered
triples fail (`icosaDesign_no_isSignBlindGoodTriple`), hence so does every box, every
radius box and every ball: `not_boxGoodTriangleCovering_six` is a corollary of
`not_signBlindGoodTripleCovering_six`, and replication carries the refutation to the
frontier size (`not_signBlindGoodTripleCovering_seven`).

**What the discarded sign was carrying.** `icosaDesign` still dominates — strictly, with
margin `2 − 3/√5`. At a distinct triple every `rho² = 9/20`, so the elliptope bracket is
exactly `−7/20 + 2 rho_ab rho_ac rho_bc` (`icosaDesign_elliptopeBracket_of_distinct`)
and domination holds iff `7/40 ≤ rho_ab rho_ac rho_bc`
(`icosaDesign_dominates_iff_pairingProduct`). The sign-blind part is NEGATIVE at every
triple and the entire verdict is carried by the orientation of the pairing product,
which no function of the squares can see. So the open `discriminantCovering 7` gap
admits no sign-blind certificate at all; it needs an object that reads the sign of
`p_ab p_ac p_bc`.

Measured, never proved: that every one of the eight sign patterns of `rho` is realised
by some all-heavy `(7,3)` design — checked by rejection sampling on
`Gr(3,7) × Δ⁶`, with `|rho|` observed up to `14.9` and the bracket ranging over
`[−424, +240.7]`, so the per-triple feasible set for `rho` appears to be all of `R³`
and the maximality of the sign-blind body above is a statement about the certificate
family's logical form, not about a measured parameter range. -/

/-- The **sign-blind part of the tie leg**,
`u_a u_b u_c − (u_c p_ab² + u_b p_ac² + u_a p_bc²)`. Every certificate that reads only
squared pairings sees exactly this number and the magnitude of the pairing product. -/
def excessGap (D : WeightedDesign m 3) (first second third : Fin m) : ℝ :=
  heavyExcess D first * heavyExcess D second * heavyExcess D third
    - (heavyExcess D third * atomPairing D first second ^ 2
      + heavyExcess D second * atomPairing D first third ^ 2
      + heavyExcess D first * atomPairing D second third ^ 2)

/-- **The tie leg splits into a sign-blind part and the oriented triple product.** The
single identity behind everything in this section. -/
theorem discriminantTie_eq_excessGap_add_tripleProduct (D : WeightedDesign m 3)
    (first second third : Fin m) :
    discriminantTie D first second third
      = excessGap D first second third
        + 2 * (atomPairing D first second * atomPairing D first third
            * atomPairing D second third) := by
  rw [discriminantTie_eq_gramMinorForm, excessGap]
  ring

/-- A triple is **sign-blind-good** when the tie leg stays nonnegative under both signs
of its pairing product. The exact closure of the box, radius-box and ball families. -/
def IsSignBlindGoodTriple (D : WeightedDesign m 3) (first second third : Fin m) : Prop :=
  2 * |atomPairing D first second * atomPairing D first third
      * atomPairing D second third| ≤ excessGap D first second third

theorem excessGap_nonneg_of_isSignBlindGoodTriple (D : WeightedDesign m 3)
    (first second third : Fin m)
    (hsignBlind : IsSignBlindGoodTriple D first second third) :
    0 ≤ excessGap D first second third := by
  rw [IsSignBlindGoodTriple] at hsignBlind
  linarith [abs_nonneg (atomPairing D first second * atomPairing D first third
    * atomPairing D second third)]

/-- The tie leg from the sign-blind hypothesis: the oriented term can only give back
what the absolute value already conceded. -/
theorem discriminantTie_nonneg_of_isSignBlindGoodTriple (D : WeightedDesign m 3)
    (first second third : Fin m)
    (hsignBlind : IsSignBlindGoodTriple D first second third) :
    0 ≤ discriminantTie D first second third := by
  rw [discriminantTie_eq_excessGap_add_tripleProduct]
  rw [IsSignBlindGoodTriple] at hsignBlind
  linarith [neg_abs_le (atomPairing D first second * atomPairing D first third
    * atomPairing D second third)]

/-- The trace leg follows from nonnegativity of the sign-blind gap alone: each squared
pairing is dominated by its own excess product, after cancelling the third excess. -/
theorem discriminantTrace_nonneg_of_excessGap_nonneg (D : WeightedDesign m 3)
    {first second third : Fin m} (hfirstPos : 0 < heavyExcess D first)
    (hsecondPos : 0 < heavyExcess D second) (hthirdPos : 0 < heavyExcess D third)
    (hgap : 0 ≤ excessGap D first second third) :
    0 ≤ discriminantTrace D first second third := by
  rw [excessGap] at hgap
  have hfirstSquared : 0 ≤ heavyExcess D first * atomPairing D second third ^ 2 :=
    mul_nonneg hfirstPos.le (sq_nonneg _)
  have hsecondSquared : 0 ≤ heavyExcess D second * atomPairing D first third ^ 2 :=
    mul_nonneg hsecondPos.le (sq_nonneg _)
  have hthirdSquared : 0 ≤ heavyExcess D third * atomPairing D first second ^ 2 :=
    mul_nonneg hthirdPos.le (sq_nonneg _)
  have hfirstSecondBound : atomPairing D first second ^ 2
      ≤ heavyExcess D first * heavyExcess D second := by
    refine le_of_mul_le_mul_left ?_ hthirdPos
    linarith [hgap, hsecondSquared, hfirstSquared]
  have hfirstThirdBound : atomPairing D first third ^ 2
      ≤ heavyExcess D first * heavyExcess D third := by
    refine le_of_mul_le_mul_left ?_ hsecondPos
    linarith [hgap, hthirdSquared, hfirstSquared]
  rw [discriminantTrace]
  linarith [hfirstSecondBound, hfirstThirdBound]

/-- **THE SHARP SIGN-BLIND CERTIFICATE IS SOUND.** A triple of distinct heavy atoms
whose sign-blind gap dominates twice the magnitude of its pairing product dominates. -/
theorem dominates_of_isSignBlindGoodTriple {D : WeightedDesign m 3} (hheavy : AllHeavy D)
    {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hsignBlind : IsSignBlindGoodTriple D first second third) :
    Dominates D {first, second, third} :=
  (dominates_triple_iff_discriminantSystem D hfirstSecond hfirstThird hsecondThird
      (hheavy first)).mpr
    ⟨discriminantTrace_nonneg_of_excessGap_nonneg D
        (allHeavy_heavyExcess_pos hheavy first) (allHeavy_heavyExcess_pos hheavy second)
        (allHeavy_heavyExcess_pos hheavy third)
        (excessGap_nonneg_of_isSignBlindGoodTriple D first second third hsignBlind),
      discriminantTie_nonneg_of_isSignBlindGoodTriple D first second third hsignBlind⟩

/-- **The sign-blind body contains the box.** Three box edges keep a quarter of the
excess product in the gap and confine the squared triple product to a sixty-fourth of
its square, so the gap wins with the same factor `1/4` on both sides. -/
theorem isSignBlindGoodTriple_of_isBoxGoodTriangle {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) {first second third : Fin m}
    (htriangle : IsBoxGoodTriangle D first second third) :
    IsSignBlindGoodTriple D first second third := by
  obtain ⟨hboxFirstSecond, hboxFirstThird, hboxSecondThird⟩ := htriangle
  rw [IsBoxGoodPair] at hboxFirstSecond hboxFirstThird hboxSecondThird
  have hfirstPos := allHeavy_heavyExcess_pos hheavy first
  have hsecondPos := allHeavy_heavyExcess_pos hheavy second
  have hthirdPos := allHeavy_heavyExcess_pos hheavy third
  have hexcessProductPos : 0 < heavyExcess D first * heavyExcess D second
      * heavyExcess D third := mul_pos (mul_pos hfirstPos hsecondPos) hthirdPos
  have hgapQuarter : heavyExcess D first * heavyExcess D second * heavyExcess D third / 4
      ≤ excessGap D first second third := by
    rw [excessGap]
    nlinarith [mul_le_mul_of_nonneg_left hboxFirstSecond hthirdPos.le,
      mul_le_mul_of_nonneg_left hboxFirstThird hsecondPos.le,
      mul_le_mul_of_nonneg_left hboxSecondThird hfirstPos.le]
  have hsquareStep : (4 * atomPairing D first second ^ 2)
        * (4 * atomPairing D first third ^ 2)
      ≤ (heavyExcess D first * heavyExcess D second)
        * (heavyExcess D first * heavyExcess D third) :=
    mul_le_mul hboxFirstSecond hboxFirstThird (by positivity)
      (mul_pos hfirstPos hsecondPos).le
  have hcubeStep : ((4 * atomPairing D first second ^ 2)
          * (4 * atomPairing D first third ^ 2))
        * (4 * atomPairing D second third ^ 2)
      ≤ ((heavyExcess D first * heavyExcess D second)
          * (heavyExcess D first * heavyExcess D third))
        * (heavyExcess D second * heavyExcess D third) :=
    mul_le_mul hsquareStep hboxSecondThird (by positivity)
      (mul_nonneg (mul_pos hfirstPos hsecondPos).le (mul_pos hfirstPos hthirdPos).le)
  have hproductBound : |atomPairing D first second * atomPairing D first third
        * atomPairing D second third|
      ≤ heavyExcess D first * heavyExcess D second * heavyExcess D third / 8 := by
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    nlinarith [hcubeStep]
  rw [IsSignBlindGoodTriple]
  linarith [hproductBound, hgapQuarter]

/-- **The Handelman radius `3/4`, explained.** Three-term AM-GM bounds the normalized
triple product at squared radius `R` by `(R/3)^{3/2}`, so a ball is sign-blind-good iff
`R + 2 (R/3)^{3/2} ≤ 1`; at `R = 3/4` the bound `(1/4)^{3/2}` is `1/8` and the identity
holds with EQUALITY, which is what pins the radius. The ball is therefore a strict
sub-body of `IsSignBlindGoodTriple` and gets no separate theorem. -/
theorem ballRadius_sharp : (3 / 4 : ℝ) + 2 * (1 / 8) = 1 := by norm_num

/-! ### The sign-blind covering, and its refutation -/

/-- **The sign-blind covering at size `m`**: every all-heavy weighted `(m,3)` design has
a triple whose tie leg survives both product signs. Sufficient for the conjecture
(`discriminantCovering_of_signBlindGoodTripleCovering`), implied by the box covering,
and false from size six upward. -/
def SignBlindGoodTripleCovering (m : ℕ) : Prop :=
  ∀ D : WeightedDesign m 3, AllHeavy D →
    ∃ first second third : Fin m,
      first ≠ second ∧ first ≠ third ∧ second ≠ third
        ∧ IsSignBlindGoodTriple D first second third

theorem signBlindGoodTripleCovering_of_boxGoodTriangleCovering {size : ℕ}
    (hcover : BoxGoodTriangleCovering size) : SignBlindGoodTripleCovering size := by
  intro D hheavy
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, htriangle⟩ :=
    hcover D hheavy
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    isSignBlindGoodTriple_of_isBoxGoodTriangle hheavy htriangle⟩

theorem discriminantCovering_of_signBlindGoodTripleCovering {size : ℕ}
    (hcover : SignBlindGoodTripleCovering size) : DiscriminantCovering size := by
  refine (elliptopeGoodTriangleCovering_iff_discriminantCovering size).mp ?_
  intro D hheavy
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hsignBlind⟩ :=
    hcover D hheavy
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    (dominates_triple_iff_isElliptopeGoodTriangle hheavy hfirstSecond hfirstThird
      hsecondThird).mp
        (dominates_of_isSignBlindGoodTriple hheavy hfirstSecond hfirstThird hsecondThird
          hsignBlind)⟩

/-- Every icosahedral squared pairing is at least `9/5` — exactly `9/5` off the
diagonal and `9` on it, so the bound needs no side condition on the two indices. -/
theorem icosaDesign_atomPairing_sq_ge (atomFirst atomSecond : Fin 6) :
    9 / 5 ≤ atomPairing icosaDesign atomFirst atomSecond ^ 2 := by
  rcases eq_or_ne atomFirst atomSecond with hsame | hne
  · rw [hsame, atomPairing_self, icosaDesign_leverage]
    norm_num
  · exact le_of_eq (icosaDesign_atomPairing_sq_of_ne hne).symm

/-- **The icosahedral sign-blind gap is NEGATIVE at every ordered triple**, by at least
`14/5`. Three squared pairings of size at least `9/5` against excesses `2` give
`8 − 54/5 = −14/5`. -/
theorem icosaDesign_excessGap_le (first second third : Fin 6) :
    excessGap icosaDesign first second third ≤ -(14 / 5) := by
  rw [excessGap, icosaDesign_heavyExcess, icosaDesign_heavyExcess, icosaDesign_heavyExcess]
  linarith [icosaDesign_atomPairing_sq_ge first second,
    icosaDesign_atomPairing_sq_ge first third,
    icosaDesign_atomPairing_sq_ge second third]

/-- On a distinct triple the gap is EXACTLY `−14/5`. -/
theorem icosaDesign_excessGap_of_distinct {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    excessGap icosaDesign first second third = -(14 / 5) := by
  rw [excessGap, icosaDesign_heavyExcess, icosaDesign_heavyExcess,
    icosaDesign_heavyExcess, icosaDesign_atomPairing_sq_of_ne hfirstSecond,
    icosaDesign_atomPairing_sq_of_ne hfirstThird,
    icosaDesign_atomPairing_sq_of_ne hsecondThird]
  norm_num

/-- **NO ICOSAHEDRAL TRIPLE IS SIGN-BLIND-GOOD.** The gap is negative while twice an
absolute value is nonnegative, so all `216` ordered triples fail at once — and with
them every box, every radius box and every ball. -/
theorem icosaDesign_no_isSignBlindGoodTriple (first second third : Fin 6) :
    ¬ IsSignBlindGoodTriple icosaDesign first second third := by
  intro hsignBlind
  rw [IsSignBlindGoodTriple] at hsignBlind
  linarith [icosaDesign_excessGap_le first second third,
    abs_nonneg (atomPairing icosaDesign first second
      * atomPairing icosaDesign first third * atomPairing icosaDesign second third)]

/-- **THE SHARP SIGN-BLIND FORM OF THE COVERING IS FALSE at size six.** -/
theorem not_signBlindGoodTripleCovering_six : ¬ SignBlindGoodTripleCovering 6 := by
  intro hcover
  obtain ⟨first, second, third, _, _, _, hsignBlind⟩ :=
    hcover icosaDesign icosaDesign_allHeavy
  exact icosaDesign_no_isSignBlindGoodTriple first second third hsignBlind

/-- The box refutation is a COROLLARY of the sign-blind one, since the box body is
contained in the sign-blind body. -/
theorem not_boxGoodTriangleCovering_six_of_signBlind : ¬ BoxGoodTriangleCovering 6 :=
  fun hcover =>
    not_signBlindGoodTripleCovering_six
      (signBlindGoodTripleCovering_of_boxGoodTriangleCovering hcover)

theorem excessGap_eq_of_atom_eq {sizeLeft sizeRight : ℕ}
    (designLeft : WeightedDesign sizeLeft 3) (designRight : WeightedDesign sizeRight 3)
    {firstLeft secondLeft thirdLeft : Fin sizeLeft}
    {firstRight secondRight thirdRight : Fin sizeRight}
    (hfirst : designLeft.atom firstLeft = designRight.atom firstRight)
    (hsecond : designLeft.atom secondLeft = designRight.atom secondRight)
    (hthird : designLeft.atom thirdLeft = designRight.atom thirdRight) :
    excessGap designLeft firstLeft secondLeft thirdLeft
      = excessGap designRight firstRight secondRight thirdRight := by
  rw [excessGap, excessGap,
    heavyExcess_eq_of_atom_eq designLeft designRight hfirst,
    heavyExcess_eq_of_atom_eq designLeft designRight hsecond,
    heavyExcess_eq_of_atom_eq designLeft designRight hthird,
    atomPairing_eq_of_atom_eq designLeft designRight hfirst hsecond,
    atomPairing_eq_of_atom_eq designLeft designRight hfirst hthird,
    atomPairing_eq_of_atom_eq designLeft designRight hsecond hthird]

theorem isSignBlindGoodTriple_iff_of_atom_eq {sizeLeft sizeRight : ℕ}
    (designLeft : WeightedDesign sizeLeft 3) (designRight : WeightedDesign sizeRight 3)
    {firstLeft secondLeft thirdLeft : Fin sizeLeft}
    {firstRight secondRight thirdRight : Fin sizeRight}
    (hfirst : designLeft.atom firstLeft = designRight.atom firstRight)
    (hsecond : designLeft.atom secondLeft = designRight.atom secondRight)
    (hthird : designLeft.atom thirdLeft = designRight.atom thirdRight) :
    IsSignBlindGoodTriple designLeft firstLeft secondLeft thirdLeft
      ↔ IsSignBlindGoodTriple designRight firstRight secondRight thirdRight := by
  rw [IsSignBlindGoodTriple, IsSignBlindGoodTriple,
    excessGap_eq_of_atom_eq designLeft designRight hfirst hsecond hthird,
    atomPairing_eq_of_atom_eq designLeft designRight hfirst hsecond,
    atomPairing_eq_of_atom_eq designLeft designRight hfirst hthird,
    atomPairing_eq_of_atom_eq designLeft designRight hsecond hthird]

/-- Sign-blind goodness of the split design is sign-blind goodness of the merged
triple — leverages, excesses and pairings are all unchanged by replication. -/
theorem isSignBlindGoodTriple_replicatedDesign_iff (D : WeightedDesign m 3) (which : Fin m)
    (first second third : Fin (m + 1)) :
    IsSignBlindGoodTriple (replicatedDesign D which) first second third
      ↔ IsSignBlindGoodTriple D (replicationMerge which first)
          (replicationMerge which second) (replicationMerge which third) :=
  isSignBlindGoodTriple_iff_of_atom_eq _ _ (atom_replicationMerge D which first).symm
    (atom_replicationMerge D which second).symm (atom_replicationMerge D which third).symm

/-- **All `343` ordered triples of the seven-atom icosahedral witness fail.** -/
theorem icosaSevenDesign_no_isSignBlindGoodTriple (first second third : Fin 7) :
    ¬ IsSignBlindGoodTriple icosaSevenDesign first second third := fun hsignBlind =>
  icosaDesign_no_isSignBlindGoodTriple _ _ _
    ((isSignBlindGoodTriple_replicatedDesign_iff icosaDesign 0 first second third).mp
      hsignBlind)

/-- **The sharp sign-blind form is false at the frontier size**, where the whole of
rank three lives. -/
theorem not_signBlindGoodTripleCovering_seven : ¬ SignBlindGoodTripleCovering 7 := by
  intro hcover
  obtain ⟨first, second, third, _, _, _, hsignBlind⟩ :=
    hcover icosaSevenDesign icosaSevenDesign_allHeavy
  exact icosaSevenDesign_no_isSignBlindGoodTriple first second third hsignBlind

/-! ### Calibration: both sharp objects sit ON the sign-blind boundary -/

/-- The tetrahedron's sign-blind gap is exactly `2`. -/
theorem tetraDesign_excessGap : excessGap tetraDesign 0 1 2 = 2 := by
  rw [excessGap, tetraDesign_heavyExcess, tetraDesign_heavyExcess,
    tetraDesign_heavyExcess, tetraDesign_atomPairing_zeroOne,
    tetraDesign_atomPairing_zeroTwo, tetraDesign_atomPairing_oneTwo]
  norm_num

/-- **The tetrahedron sits exactly ON the sign-blind boundary**: the pairing product is
`−1`, so `2 |p p p| = 2 = excessGap`. Any strict reading of the certificate loses the
campaign's sharpest object, exactly as for the box. -/
theorem tetraDesign_isSignBlindGoodTriple : IsSignBlindGoodTriple tetraDesign 0 1 2 := by
  rw [IsSignBlindGoodTriple, tetraDesign_excessGap, tetraDesign_atomPairing_zeroOne,
    tetraDesign_atomPairing_zeroTwo, tetraDesign_atomPairing_oneTwo]
  norm_num

/-- The `(7,3)` tie's sign-blind gap is exactly `2` as well. -/
theorem splitSevenDesign_excessGap : excessGap splitSevenDesign 0 1 2 = 2 := by
  have hzeroOne : atomPairing splitSevenDesign 0 1 = -1 :=
    splitSevenDesign_atomPairing_of_differentDirection (by decide)
  have hzeroTwo : atomPairing splitSevenDesign 0 2 = -1 :=
    splitSevenDesign_atomPairing_of_differentDirection (by decide)
  have honeTwo : atomPairing splitSevenDesign 1 2 = -1 :=
    splitSevenDesign_atomPairing_of_differentDirection (by decide)
  rw [excessGap, splitSevenDesign_heavyExcess, splitSevenDesign_heavyExcess,
    splitSevenDesign_heavyExcess, hzeroOne, hzeroTwo, honeTwo]
  norm_num

/-- **The frontier-size tie also sits ON the sign-blind boundary.** So the sharp
certificate is calibrated by the tie from inside and refuted by the icosahedron from
outside, and both boundaries are exact. -/
theorem splitSevenDesign_isSignBlindGoodTriple :
    IsSignBlindGoodTriple splitSevenDesign 0 1 2 := by
  have hzeroOne : atomPairing splitSevenDesign 0 1 = -1 :=
    splitSevenDesign_atomPairing_of_differentDirection (by decide)
  have hzeroTwo : atomPairing splitSevenDesign 0 2 = -1 :=
    splitSevenDesign_atomPairing_of_differentDirection (by decide)
  have honeTwo : atomPairing splitSevenDesign 1 2 = -1 :=
    splitSevenDesign_atomPairing_of_differentDirection (by decide)
  rw [IsSignBlindGoodTriple, splitSevenDesign_excessGap, hzeroOne, hzeroTwo, honeTwo]
  norm_num

/-! ### What the discarded sign was carrying -/

theorem icosaDesign_heavyExcess_pos (atomIndex : Fin 6) :
    0 < heavyExcess icosaDesign atomIndex := by
  rw [icosaDesign_heavyExcess]; norm_num

/-- Every distinct icosahedral pair has squared normalized pairing exactly `9/20`:
squared cosine `1/5` at leverage `3` becomes `(9/5)/(2·2)`. -/
theorem icosaDesign_normalizedPairing_sq_of_ne {atomFirst atomSecond : Fin 6}
    (hne : atomFirst ≠ atomSecond) :
    normalizedPairing icosaDesign atomFirst atomSecond ^ 2 = 9 / 20 := by
  rw [normalizedPairing_sq icosaDesign (icosaDesign_heavyExcess_pos atomFirst)
      (icosaDesign_heavyExcess_pos atomSecond),
    icosaDesign_atomPairing_sq_of_ne hne, icosaDesign_heavyExcess,
    icosaDesign_heavyExcess]
  norm_num

/-- Distinct icosahedral pairs are compatible with room to spare: the pair minor is
`4 − 9/5 = 11/5 > 0`, so no EDGE of the elliptope-good graph is missing. Whatever
fails at the icosahedron fails on the TRIPLE condition alone. -/
theorem icosaDesign_isCompatiblePair_of_ne {atomFirst atomSecond : Fin 6}
    (hne : atomFirst ≠ atomSecond) :
    IsCompatiblePair icosaDesign atomFirst atomSecond := by
  rw [IsCompatiblePair, pairMinor, icosaDesign_heavyExcess, icosaDesign_heavyExcess,
    icosaDesign_atomPairing_sq_of_ne hne]
  norm_num

/-- **THE ICOSAHEDRAL BRACKET IS A PURE SIGN TEST.** Every squared normalized pairing
is `9/20`, so the elliptope determinant collapses to `−7/20 + 2 rho rho rho`: the
sign-blind part is a NEGATIVE CONSTANT and the whole verdict rides on the oriented
product. Flipping one pairing's sign preserves all three squares and negates the
product, which is precisely why no function of the squares can decide this design. -/
theorem icosaDesign_elliptopeBracket_of_distinct {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    elliptopeBracket (normalizedPairing icosaDesign first second)
        (normalizedPairing icosaDesign first third)
        (normalizedPairing icosaDesign second third)
      = -(7 / 20) + 2 * (normalizedPairing icosaDesign first second
          * normalizedPairing icosaDesign first third
          * normalizedPairing icosaDesign second third) := by
  rw [elliptopeBracket, icosaDesign_normalizedPairing_sq_of_ne hfirstSecond,
    icosaDesign_normalizedPairing_sq_of_ne hfirstThird,
    icosaDesign_normalizedPairing_sq_of_ne hsecondThird]
  ring

/-- **Domination at the icosahedron is exactly one inequality on a SIGNED product.** A
distinct icosahedral triple dominates iff `7/40 ≤ rho_ab rho_ac rho_bc`. The magnitude
of that product is the same at every triple, `(9/20)^{3/2} = 27/(40√5) ≈ 0.3019 >
7/40`, so the verdict is decided by the sign alone — which is the mechanized form of
"the remaining gap needs a sign-aware certificate". -/
theorem icosaDesign_dominates_iff_pairingProduct {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    Dominates icosaDesign {first, second, third}
      ↔ 7 / 40 ≤ normalizedPairing icosaDesign first second
          * normalizedPairing icosaDesign first third
          * normalizedPairing icosaDesign second third := by
  have hcompatible : IsCompatibleTriangle icosaDesign first second third :=
    ⟨icosaDesign_isCompatiblePair_of_ne hfirstSecond,
      icosaDesign_isCompatiblePair_of_ne hfirstThird,
      icosaDesign_isCompatiblePair_of_ne hsecondThird⟩
  have htieIff : 0 ≤ discriminantTie icosaDesign first second third
      ↔ 7 / 40 ≤ normalizedPairing icosaDesign first second
          * normalizedPairing icosaDesign first third
          * normalizedPairing icosaDesign second third := by
    rw [discriminantTie_nonneg_iff_elliptopeBracket_nonneg icosaDesign
        (icosaDesign_heavyExcess_pos first) (icosaDesign_heavyExcess_pos second)
        (icosaDesign_heavyExcess_pos third),
      icosaDesign_elliptopeBracket_of_distinct hfirstSecond hfirstThird hsecondThird]
    constructor <;> intro hbound <;> linarith
  rw [dominates_triple_iff_isElliptopeGoodTriangle icosaDesign_allHeavy hfirstSecond
      hfirstThird hsecondThird, IsElliptopeGoodTriangle]
  constructor
  · intro hgood
    exact htieIff.mp hgood.2
  · intro hproduct
    exact ⟨hcompatible, htieIff.mpr hproduct⟩

/-! ### What survives

The box level is closed, but the refutation threshold recorded below is NOT sharp:
`BoxGoodTriangleCovering` already fails at size FOUR, on a design with rational atoms
and rational weights (tetrahedron directions at squared scales `(5,5,5/7,5/7)`, weights
`(1/100,1/100,49/100,49/100)`, one box-good edge, no triangle, and `{0,1,2}`/`{0,1,3}`
still dominating). Size `3` cannot be refuted — there `M Mᵀ = I` forces `Mᵀ M = I`, so
every pairing vanishes — so the sharp statement is `BoxGoodTriangleCovering m ↔ m ≤ 3`,
and the size-six and size-seven results are corollaries by `boxGoodTriangleCovering_of_le`.
Sufficiency is a theorem; the covering direction is refuted from size four upward, on an
open set rather than at a point; the constant `1/2` cannot be relaxed without leaving the
elliptope
(`symmetricHalfRadius_admissible` shows the symmetric box is exactly inscribed); and the
refutation has been lifted from the box to the exact closure of every sign-blind
certificate family (`not_signBlindGoodTripleCovering_seven`), so no further certificate
of that shape needs to be tried. The elliptope level is exactly the conjecture
(`elliptopeGoodTriangleCovering_seven_iff_rank_three`), so the graph reformulation buys
structure, not a proof: what must be certified is one degree-three condition per triple
on a `21`-dimensional parameter space, and it must read the SIGN of
`p_ab p_ac p_bc`, since the sign-blind part of the tie leg is negative at every
icosahedral triple while `10` of the `20` triples dominate. Both boundaries of the sharp
certificate are exact and in opposite directions: the tetrahedron and the `(7,3)` tie
sit on it with equality, the icosahedron misses it by `14/5`. Cut-polytope bodies are
defeated by the tetrahedron instead, and unlike the sign-blind body they are linear in
`rho` and so require adjoining `sqrt(u_c)`. -/

end Gtz

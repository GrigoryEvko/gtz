/-
# The floored spread region at `(6,3)` with a MARGIN: the sentence a certificate
# would supply, the chart it would be found in, and the ceiling it cannot exceed

`Gtz.Quantitative.FlooredSpreadRegion` fixes the region and names the
QUALITATIVE hypothesis `Gtz.FlooredSpreadCovering` — some triple has both
`S_3`-invariant legs nonnegative.  A Positivstellensatz certificate does not
produce that sentence directly.  It produces a strictly positive MARGIN, because
strict feasibility is what lets a numerical solution be rounded to rationals at
all; a certificate of `>= 0` on a region whose infimum is exactly `0` cannot be
rounded, and the whole point of excising the ties is to move the infimum off
zero.  This file states the margin version, connects it back to the qualitative one,
translates it into the projection chart with explicit constants, builds the chart
MATRIX and proves the two structural constraints a solver-side certificate
assumes about it (`P * P = P`, `trace P = 3`), and proves the boundaries any
search must respect: the region is EMPTY above weight floor `1/6` and again above
spread `1`, so the hypothesis is vacuous on both sides, and the region CONTAINS
the icosahedral design, so no certificate at usable parameters can claim a margin
above `51/25`.

THERE IS NO CERTIFICATE HERE.  The hunt stage that preceded this file did not
round one; the MEASURED section below is its obstruction ledger, stated as
measurement and not as proof.  Rank three is not proved and nothing below claims
it is.

## What this file does NOT re-define

The region predicates `Gtz.HasSpreadAtLeast`, `Gtz.HasWeightFloor`,
`Gtz.IsFlooredSpreadDesign` and their monotonicity already exist in
`Gtz.Quantitative.FlooredSpreadRegion`, and the chart
`Gtz.chartEntry` / `Gtz.chartGapDeterminant` / `Gtz.chartGapWeightedMinorSum`
with both leg translations already exists in
`Gtz.Quantitative.ProjectionChartLegs`.  This file imports both and adds only
the quantitative layer.  A separate warning about names: `Gtz.SpreadFloorCertificate`
in `Gtz.Reduction.SplitTransfer` is a DIFFERENT statement — it is the branch of
the compact shell for designs with no exactly parallel pair and no dust, an OPEN
region carrying no margin.  `SpreadFloorCertificateSixThree` below is the CLOSED
floored spread region with a margin, at size six only.  The two are not
specialisations of one another.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

**The margin hypothesis and its qualitative shadow.**
`HasLegMarginAtLeast D margin` says some triple of distinct atoms has both
`discriminantMinorSum` and `discriminantTie` at least `margin`;
`SpreadFloorCertificateSixThree spread floor margin` asserts it for every design
in the floored spread region at rational parameters.  At margin zero it IS
`Gtz.FlooredSpreadCovering` (`spreadFloorCertificateSixThree_zero_iff_flooredSpreadCovering`),
and at any nonnegative margin it implies it
(`flooredSpreadCovering_of_spreadFloorCertificateSixThree`) — which is how a
certificate reaches the assembly, since
`Gtz.flooredSpreadDominationCertificate_six_of_flooredSpreadCovering` and
`Gtz.gtzWeightedSix_of_compactBranches` in `Gtz.Reduction.SplitTransfer` consume
exactly `Gtz.FlooredSpreadCovering`.  Both parameters move the right way:
raising `spread` or `floor` shrinks the region, so a certificate transfers to
the larger parameters (`spreadFloorCertificateSixThree_shrinkRegion`), and
lowering the margin weakens the conclusion
(`spreadFloorCertificateSixThree_weakenMargin`).  Those two and
`hasLegMarginAtLeast_weaken` are ANTITONE in the named parameter, which is why
none of them is called `_mono`.

**The chart form, with the constants, and no bridge hypothesis.**
`HasChartLegMarginAtLeast` and `ChartSpreadFloorCertificateSixThree` are the same
statements written in the projection chart.  Because `Gtz.chartTie_eq` and
`Gtz.chartMinorSum_eq` scale each leg by the weight product, the two margins are
related by explicit constants and NOTHING is assumed:

  `weightProduct_le_cube_div_twentySeven` — three positive weights summing to at
    most `B` have product at most `B^3/27` (AM-GM); at `B = 1` this is
    `weightProduct_le_inv_twentySeven`, so a chart margin `c >= 0` yields a raw
    margin `27 c` (`hasLegMarginAtLeast_of_hasChartLegMarginAtLeast`);
  `weightTripleSum_le_of_hasWeightFloor` — at size six the three atoms outside a
    triple each carry at least `floor`, so `B = 1 - 3 floor` and the
    amplification improves to `27 / (1 - 3 floor)^3`
    (`weightProduct_le_of_hasWeightFloor`,
    `hasLegMarginAtLeast_of_hasChartLegMarginAtLeast_floored`): `43.97` at
    `floor = 1/20`, `78.7` at `1/10`;
  `floorCube_le_weightProduct` — under a weight floor the product is at least
    `floor^3`, so a raw margin `eps >= 0` yields a chart margin `floor^3 eps`
    (`hasChartLegMarginAtLeast_of_hasLegMarginAtLeast`).

Both certificates therefore imply each other with those constants
(`spreadFloorCertificateSixThree_of_chartCertificate`,
`chartCertificate_of_spreadFloorCertificateSixThree`).

**The chart MATRIX, so a solver's own statement is consumable.**  The chart
statements above quantify over DESIGNS.  A Positivstellensatz search does not:
it proves something about a symmetric matrix `P` constrained by `P * P = P` and
`trace P = 3` together with a weight vector.  `chartMatrix` is that matrix,
`chartFrame` its Stiefel factor, and the constraints are THEOREMS here, not
hypotheses: `chartFrame_transpose_mul_self` (Parseval IS `V^T V = I`),
`chartMatrix_isIdempotent`, `chartMatrix_isSymm`, `chartMatrix_trace`, plus
`chartMatrix_diagonal_gt_weight_of_allHeavy` for all-heaviness and
`Gtz.chartSpread_iff` for the spread generator.  So
`FreeChartCertificateSixThree` — quantified over ALL such `(P, weight)` pairs,
a strictly stronger statement since it covers pairs no design produces — implies
this file's hypothesis outright, through
`chartCertificateSixThree_of_freeChartCertificate` and
`spreadFloorCertificateSixThree_of_freeChartCertificate`, with no bridge left
open.  (An earlier revision of this header recorded `P^2 = P` and `trace P = 3`
as true-but-unproved; they are proved now, and the abstract leg polynomials
`chartGapDeterminantOf` / `chartGapWeightedMinorSumOf` agree with the design-side
ones by `rfl`.)

**The region is bounded, which is why a certificate can exist at all.**
`leverageOf_le_of_hasWeightFloor` (from `Gtz.weighted_leverage_le_one`) caps every
leverage at `1/floor`, `heavyExcess_le_of_hasWeightFloor` caps every excess at
`1/floor - 1`, and `atomPairing_sq_le_of_hasWeightFloor` caps every squared
pairing at `1/floor^2` — the last through
`atomPairing_sq_le_leverage_product`, which is Cauchy-Schwarz and needs no
design hypothesis at all, so the box is set by the FLOOR ALONE and neither the
spread parameter nor all-heaviness enters.  That is the Archimedean input every
Putinar-style argument needs, and the reason
`Gtz.Certificates.PositivstellensatzObstruction` does not apply here.  It
degenerates exactly as the floor goes to zero, which is the proved shadow of the
measured quartic.

**The three boundaries.**  `spreadFloorCertificateSixThree_of_sixth_lt_floor`:
six weights summing to one cannot all exceed `1/6`, so above that floor the
region is empty and the hypothesis holds vacuously at EVERY margin — a
certificate there proves nothing.
`spreadFloorCertificateSixThree_of_one_lt_spread`: above spread `1` the spread
bound asks a square to be at most a negative number, so the region is empty
again.  (The window `(4/5, 1]` is guarded by NEITHER: the region is measured
empty well before `1`, since six real lines in three-space cannot beat the
icosahedron's `4/5`, but nothing here proves that.)  In the other direction
`icosaDesign_isFlooredSpreadDesign` (already proved in
`Gtz.Quantitative.FlooredSpreadRegion`) puts the icosahedral design in the region
at `spread = 4/5`, `floor = 1/6`, and `icosaDesign_discriminantTie_le` computes
its tie leg: every excess is `2` and every squared pairing is `9/5`, so the leg is
`-14/5` plus twice the triangle product, whose square is `(9/5)^3` — hence at
most `51/25` at EVERY triple.  `margin_le_of_spreadFloorCertificateSixThree`
reads that back as a CEILING: no certificate at `spread <= 4/5`, `floor <= 1/6`
can carry a margin above `51/25`.  That ceiling is `98` times weaker than the
measured leg margin at the recommended parameters, so it rules out gross
overclaims and nothing finer; see its docstring.
`icosaDesign_discriminantMinorSum_eq` records the companion exact value `33/5`,
which shows the minor-sum leg is not the binding one there.

## CITED (proved elsewhere in this repo, used in the proofs below)

`WeightedDesign`, `atomMatrix`, `leverageOf` (`Gtz.Core.Basic`);
`weighted_leverage_le_one`, `leverage_le_of_weight_floor`
(`Gtz.Design.LeverageBound`); `AllHeavy` (`Gtz.Reduction.Reductions`, reached
transitively); `heavyExcess`, `atomPairing`, `discriminantMinorSum`,
`discriminantTie` (`Gtz.Quantitative.DiscriminantSystem`); `SymmetricCovering`
(`Gtz.Quantitative.PositivstellensatzRankThree`); `HasSpreadAtLeast`,
`HasWeightFloor`, `IsFlooredSpreadDesign`, `isFlooredSpreadDesign_mono`,
`FlooredSpreadCovering`, `leverageOf_nonneg`, `icosaDesign_leverage`,
`icosaDesign_isFlooredSpreadDesign` (`Gtz.Quantitative.FlooredSpreadRegion`);
`icosaDesign`, `icosaDesign_atom`, `icosaAtom_dot_sq_of_ne`
(`Gtz.Quantitative.RealnessEngine`); `chartBasis`, `chartEntry`,
`chartEntry_comm`, `chartEntry_self`, `chartGapDeterminant`,
`chartGapWeightedMinorSum`, `chartTie_eq`, `chartMinorSum_eq`,
`chartSpread_iff`, `weightProduct_pos` (`Gtz.Quantitative.ProjectionChartLegs`);
`Finset.sum_mul_sq_le_sq_mul_sq` (Mathlib, discrete Cauchy-Schwarz).

## REFERENCED IN PROSE ONLY (not imported — importing `Gtz.Reduction.*` from
## `Gtz.Quantitative.*` would be a cycle)

`Gtz.SpreadFloorCertificate`, `Gtz.NearParallelCertificate`,
`Gtz.DustDropCertificate`, `Gtz.flooredSpreadDominationCertificate_six_of_flooredSpreadCovering`,
`Gtz.gtzWeightedSix_of_compactBranches`, `Gtz.not_isFlooredSpreadDesign_of_sizeInv_lt_floor`
(all `Gtz.Reduction.SplitTransfer`).  The composite an orchestrator would build
is: this file's certificate, then
`flooredSpreadCovering_of_spreadFloorCertificateSixThree`, then
`Gtz.gtzWeightedSix_of_compactBranches` against the other two branch
obligations.

## MEASURED (computed outside Lean, NOT proved here, stated as such)

Numbers carry a PROVENANCE TAG.  [PRIOR] came from the epsilon-surface or
certificate-hunt stage and was not recomputed here.  [RECHECKED] was recomputed
independently by this file's author, harness described at the end of the
section.  Four [PRIOR] claims are REFUTED below; they are kept, marked and
corrected rather than deleted, so that a later hunt does not re-derive them.

The chart computations rest on the leg translation of
`Gtz.Quantitative.ProjectionChartLegs`, cross-validated against the raw `(g,t)`
definitions symbolically over `Q` (difference identically zero on seven exactly
rational design families), at seventy digits (worst relative discrepancy
`2.5e-68` at Parseval residual `3.6e-71`), and in float64 division-free form
(worst absolute discrepancy `3.3e-16` over `500` designs times `20` triples).
No design of value below one was found at any setting.

* THE TWO ANCHORS [RECHECKED].  `icosaDesign`: every leverage `3`, every squared
  pairing `9/5`, minor-sum leg `33/5` at all twenty triples, tie leg taking two
  values whose maximum is `2.029906831399546` — reproducing
  `icosaDesign_discriminantMinorSum_eq` and the sharp value behind
  `icosaDesign_discriminantTie_le` to sixteen figures; least squared sine `4/5`;
  Parseval residual `2.2e-16`.  `splitTetraDesign` at the balanced split: leg
  margin EXACTLY `0.0`, eigenvalue margin `-1.1e-16`, least weight `1/8`, every
  leverage `3`, least squared sine `0` (the duplicated pair).  Any harness that
  fails these two is measuring something else.
* THE MARGIN SURFACE IN THE FLOOR [PRIOR].  Writing `epsilon` for the least
  eigenvalue margin — the minimum over the region of `max over triples of the
  least eigenvalue of the triple Gram`, minus one — the surface at `floor` in
  `{0.01, 0.03, 0.05, 0.10}` is `6.4e-7`, `5.176468e-5`, `3.9765868e-4`,
  `6.21287002e-3`: about `64 * floor^4`, log-log slope `3.95` to `4.01` on
  `[0.012, 0.16]`.  The campaign's older "roughly like `floor^2`" is REFUTED by
  that.  The LEG margin — the minimum over the region of `max over triples of
  min of the two legs`, which is the quantity `SpreadFloorCertificateSixThree` is
  stated in — measures `7.62e-4`, `7.0579268e-3`, `2.0901626e-2`, `9.9364866e-2`
  at the same four floors, about `8 * floor^2`.  Below `floor` about `0.008` the
  solver loses the branch, so all reported values are UPPER bounds.
* CORRECTION 1 [RECHECKED, REFUTES a PRIOR claim].  The prior ledger said
  `epsilon` is "CONSTANT to ten significant figures across `spread` in
  `(0, 0.56]`" and that spread "only has to be nonzero".  FALSE.  Measured leg
  margins at `floor = 1/20`, each attained at a verified feasible design (so each
  is an UPPER bound on the regional minimum, and any value below the plateau
  refutes constancy outright):

    `spread = 1e-10`  leg margin `9.2185e-6`   (spread constraint ACTIVE)
    `spread = 1e-8`   leg margin `5.5908e-5`   (ACTIVE)
    `spread = 1e-6`   leg margin `4.7250e-4`   (ACTIVE)
    `spread = 1e-5`   leg margin `1.3539e-3`   (ACTIVE)
    `spread = 1e-4`   leg margin `4.0975e-3`   (ACTIVE)
    `spread = 3e-4`   leg margin `6.9174e-3`   (ACTIVE)
    `spread = 1e-3`   leg margin `1.2328e-2`   (ACTIVE)

  which are `2270`, `374`, `44`, `15`, `5.1`, `3.0` and `1.7` times BELOW the
  plateau value `2.09e-2`, at a fitted exponent between `0.44` (over the whole
  range) and `0.48` (locally at `1e-4`) — a square-root cusp in `spread`, not a
  plateau.  The spread constraint is ACTIVE at every one of those minimisers,
  which the plateau geometry never is.  So the plateau is not yet entered at
  `spread = 1e-3`; extrapolating the cusp it begins around `3e-3`.
  `Gtz.Quantitative.FlooredSpreadRegion` states the correct, narrower claim
  ("INACTIVE ... for every `spread` in `[0.02, 0.5]`"); the widening to
  `(0, 0.56]` happened between the two files and is the error.
  THE STRUCTURAL REASON, for which no measurement is needed: the balanced split
  tetrahedron is an EXACT tie whose least weight is `1/8`, so it satisfies
  `HasWeightFloor` at every floor up to `1/8` and `HasSpreadAtLeast` at spread
  zero.  `Gtz.splitTetraDesign_not_hasSpreadAtLeast` removes it at every POSITIVE
  spread, but removes nothing near it, and the legs are polynomial in the design.
  The regional infimum therefore tends to zero as spread tends to zero.  A hunt
  may not take `spread` as small as convenience wants.
* CORRECTION 2 [RECHECKED, REFUTES a PRIOR figure].  The prior ledger said that
  opening a duplicated pair to squared sine `s` costs about `0.8 sqrt s`,
  "exceeding the floor margin already at `spread` about `2.5e-7`".  The cusp law
  is right; the crossover is not.  It was computed against the EIGENVALUE margin
  `3.98e-4` when the quantity being exceeded is the LEG margin `2.09e-2`:
  `0.8 sqrt s = 3.98e-4` gives exactly `2.5e-7`, and `0.8 sqrt s = 2.09e-2` gives
  `6.8e-4`.  A units mismatch of four orders of magnitude.  Measured, the
  crossover sits ABOVE `1e-3` (the margin there is still `1.7` times short of the
  plateau, with the spread constraint active) and below `1e-2`.  The
  RECOMMENDED `spread = 1/10` is
  safely inside the plateau either way — the recommendation stands, its stated
  justification does not.
* CORRECTION 3 [RECHECKED, reframes a PRIOR claim].  The prior ledger called the
  leg margin "far more comfortable" than the eigenvalue margin, `50` to `1200`
  times.  That ratio is `1 / (8 floor^2)`: it is the LEVERAGE SCALE the floor
  sets, i.e. a change of units, not slack.  The legs are the second and third
  elementary symmetric functions of the Gram gap, so they carry two extra factors
  of the leverage, and the leverage diverges exactly where the design degenerates.
  Sharpest demonstration, at a design OUTSIDE the region (no floor, spread at
  least `0.3`, least weight `1.9e-5`, Parseval residual `2.6e-16`): eigenvalue
  margin `1.84e-4` while the LEG margin is `8.7e+4`.  The leg margin is not a
  distance-to-failure proxy, and certifying leg margin `8 floor^2` is exactly as
  strong as certifying eigenvalue margin `64 floor^4` — one law, stated twice.
* CORRECTION 4 [RECHECKED, REFUTES a PRIOR claim].  "The tie leg binds
  everywhere" is false as stated: at the triple attaining `max over triples of
  min of the two legs`, the tie is the smaller leg in `87.9%` of `709` sampled
  region designs at `spread = 1/5`, `floor = 1/20` (the region-audit stage
  measured `82.4%` on its own sample).  It binds AT THE MINIMISERS; a certificate
  may not assume the minor-sum leg is slack.  See also the obstruction ledger's
  item (a).
* THE MINIMISER [PRIOR], identical in all sixteen measured cells IN THE PLATEAU:
  six atoms in three orbits of size two under a Klein four-group in `O(3)`
  (residual `4e-14`), four weights pinned at the floor and two free at
  `(1 - 4 floor)/2`, ten of the twenty triples exactly at the level.  There the
  active set is the FLOOR ALONE — spread strictly inactive (squared sine about
  `0.598`), all-heaviness strictly inactive (least leverage `1.65` to `2.18`).
  Mechanism: a four-atom tight core plus two dust atoms at the floor; the quartic
  is the rate at which floor-pinned dust lifts a four-atom tie, quartic because
  the perturbation moves ALONG the tie manifold to first order.  BELOW the
  plateau this geometry is not the minimiser at all: correction 1's designs sit
  ON the spread constraint at squared sine equal to `spread`, which is the
  split-tetrahedron cusp and a different mechanism.
* RECOMMENDED TARGET `spread = 1/10`, `floor = 1/20`: leg margin `2.09e-2` at
  eigenvalue margin `3.97658684366e-4`.  `floor = 1/10` raises the leg margin to
  `9.9e-2` if the assembly can afford weights that large.  Do not push the floor
  below `1/50` (fourth-power decay) and do not push the spread below `1e-2`
  (square-root cusp, correction 1) — the recommendation is a plateau interior
  point in BOTH parameters, which is the whole reason to prefer it.
* THE COMPLEX TRINE IS IN THE REGION, exactly, and cannot be escaped.  Its
  minimum pairwise squared sine is exactly `2/3` and every weight is exactly
  `1/6`, so it clears every cell of the measured grid; none of its twenty triples
  dominates.  Raising `spread` past `2/3` excises it but does NOT lift the
  obstruction: minimising over HERMITIAN designs, the complex margin stays
  negative (`-0.236` at `spread <= 1/2`, `-0.121` at `0.75`, `-0.0067` at `0.78`)
  and turns positive only in the degenerate corner `spread >= 0.78`, while the
  real region is already empty by `0.81`.  So at every usable parameter a real
  certificate MUST engage realness.  In this chart that is free: the triangle
  monomial is literally the product of three real coordinates
  (`Gtz.chartEntry_triangle`), so the relation the phase-free no-go demands is a
  monomial identity, and the work moves to the ideal `P^2 - P`, which the trine
  provably fails — an exhaustive search over all `1024` gauge-canonical sign
  patterns finds no real symmetric rank-three idempotent with the trine's
  magnitudes, although those magnitudes satisfy every phase-free consequence of
  idempotency exactly.
* THE OBSTRUCTION LEDGER — why no certificate was rounded.  (a) The minor-sum leg
  is GENUINELY ACTIVE, so the failure system cannot be reduced to the tie leg:
  at eighty digits, on a design verifiably in the region (least weight `0.0537`,
  least squared sine `0.2211`), the minimum minor-sum over triples is
  `-14.613593823493521334`, and only about `8` to `10%` of sampled region designs
  have it positive at every triple (`8.3%` [PRIOR], `9.8%` on the region-audit
  stage's independent sample).  The disjunction must therefore be lifted, one
  multiplier per engaged triple, giving `27 + 20 = 47` variables and degree-four
  failure generators — about `1.2e9` monomials at degree eight, not
  constructible.  (The same lift, at `20` multipliers and `45` variables, is what
  makes the leg-margin MINIMISATION tractable; that part is cheap.  It is the
  certificate side that blows up.)  (b) The near-orthogonality bridge
  `Gtz.flooredSpreadCovering_of_alwaysDominantPairingTriangle` FAILS on the
  region: about `19` to `21%` of sampled region designs have a triangle-free
  good-pair graph.  The hunt stage recorded a triangle margin of
  `-3.1218130729731571859` at eighty digits but did NOT record the `(spread,
  floor)` it was minimising over, so it cannot be compared with the `-3.03e-1`
  recorded in `Gtz.Quantitative.FlooredSpreadRegion` at `spread = 1/5`,
  `floor = 1/20`; only the SIGN transfers, and only the sign is used.  Read
  through Mantel's theorem the bridge asks a six-vertex graph to contain a
  triangle, and the complex trine realises the extremal triangle-free graph
  `K_{3,3}` exactly, its nine good pairs being precisely the cross-block ones at
  defect exactly zero.  (c) The kernel itself is the binding cost, not the
  solver: `ring` on a rational sum-of-squares identity in twenty-seven variables
  costs `4.8s` at `33` monomials, `24.4s` at `194`, and `149.3s` at `579` with
  `4.3 GB` peak — roughly quadratic in monomial count.  Any certificate must be
  designed to a monomial budget, or discharged reflectively rather than by
  tactic.
* THE ICOSAHEDRAL CEILING IS NEARLY SHARP AS A BOUND ON THE ICOSAHEDRON, AND
  FAR FROM SHARP AS A CEILING [PRIOR + RECHECKED].
  `icosaDesign_discriminantTie_le` proves the rational bound `51/25 = 2.04`; the
  exact maximum of the tie leg over the icosahedron's triples is
  `54 * sqrt 5 / 25 - 14/5 = 2.029906831399546`, attained (the triangle product
  has one sign for the dominating triples and the other for the rest, which is
  the realness content in its smallest instance), so the rational bound loses
  `0.497%`.  Against the MEASURED leg margin at the recommended target it is `98`
  times too weak: the ceiling excludes gross overclaims only.  SHARPENING IT
  needs a second in-region witness near the plateau minimiser, and exactly
  rational witnesses are available in bulk — pick rational `s_c > 0` with
  `sum s_c^2 = 1` and a rational `V` (six by three) with `V^T V = I` (Cayley
  transform of a rational skew matrix), then `g_c = V_c / s_c` has rational
  atoms, rational weights `t_c = s_c^2`, exact Parseval, and hence rational legs.
  Weight profiles with every entry a rational square and floor above `1/20`
  exist, e.g. `(9,9,9,9,9,4)/49` (floor `4/49`) and `(25,25,16,16,9,9)/100`
  (floor `9/100`).  NOT DONE HERE; the cost is the twenty-triple case analysis in
  Lean, not the search.
* THE HARNESS behind every [RECHECKED] number.  Designs are carried as `(V, t)`
  with `V` the six-by-three frame from a QR factorisation, so `V^T V = I` and
  Parseval hold by construction and the residual is reported with every design
  (worst `2.6e-16` anywhere in this section); atoms are `g_c = V_c / sqrt(t_c)`;
  weights are floor plus a scaled softmax, so the floor is exact.  Eigenvalues
  come from `eigh`, never from a characteristic polynomial.  The nonsmooth
  objective `max over triples of min of the two legs` is minimised through the
  EXACT disjunction lift `min(a,b) <= s` iff `exists lambda in [0,1]` with
  `lambda a + (1 - lambda) b <= s`, one lifted multiplier per triple, giving a
  smooth `45`-variable program that SLSQP solves; sixty restarts per cell.
  Plain SLSQP on the unlifted objective stalls at the kink and returns `0.2`
  where `2.09e-2` is reachable, which is why the lift is not optional.  Only
  UPPER bounds are claimed: every reported value is the leg margin of an actual
  feasible design, and nothing here asserts a regional minimum.

## WHAT IS STILL OPEN, named

There is no certificate at any parameters.  The ceiling is `98` times weaker than
the measured truth.  The spread window `(4/5, 1]` is guarded by no theorem.  The
chart matrix now discharges the structural constraints a solver-side certificate
assumes, but a solver still has to produce one.  And the claim that the spread
parameter removes THE TIES — as opposed to the split-tetrahedron family, which
`Gtz.splitTetraDesign_not_hasSpreadAtLeast` does remove — is
`Gtz.HingeHoldsAtSize 6 3`, which `Gtz.Reduction.SplitTransfer` records as OPEN
and which is FALSE one size down (`Gtz.not_hingeHoldsAtSize_five_three`).  Prose
anywhere in this repo asserting that ties carry parallel pairs is asserting that
open hypothesis.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.LeverageBound
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Quantitative.PositivstellensatzRankThree
import Gtz.Quantitative.RealnessEngine
import Gtz.Quantitative.FlooredSpreadRegion
import Gtz.Quantitative.ProjectionChartLegs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## The margin, and the sentence a certificate would supply -/

/-- **A triple carrying a margin.** Three distinct atoms at which BOTH
`S_3`-invariant legs are at least `margin`. At `margin = 0` this is the
conclusion of `Gtz.FlooredSpreadCovering`; a Positivstellensatz certificate
produces it at a strictly positive `margin`, because rounding a numerical
solution to rationals needs strict feasibility. -/
def HasLegMarginAtLeast (D : WeightedDesign m 3) (margin : ℝ) : Prop :=
  ∃ first second third : Fin m,
    first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ margin ≤ discriminantMinorSum D first second third
      ∧ margin ≤ discriminantTie D first second third

/-- Lowering the margin weakens the statement. Named for what it does: the
conclusion is ANTITONE in `margin`, so `_mono` would be a false telling-word. -/
theorem hasLegMarginAtLeast_weaken {D : WeightedDesign m 3} {margin smallerMargin : ℝ}
    (hle : smallerMargin ≤ margin) (hmargin : HasLegMarginAtLeast D margin) :
    HasLegMarginAtLeast D smallerMargin := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hminor, htie⟩ :=
    hmargin
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hle.trans hminor, hle.trans htie⟩

/-- **THE QUANTITATIVE SENTENCE A CERTIFICATE FOR THIS BRANCH WOULD SUPPLY.**
Every all-heavy weighted `(6,3)` design whose pairwise squared sines are at least
`spread` and whose weights are at least `floor` has a triple at which both
`S_3`-invariant legs are at least `margin`. The parameters are RATIONAL because
kernel-checkable certificate data is rational.

At `margin = 0` this is exactly `Gtz.FlooredSpreadCovering spread floor`. It is
vacuous for `floor > 1/6` (`spreadFloorCertificateSixThree_of_sixth_lt_floor`)
and impossible for `margin > 51/25` at any `spread <= 4/5`, `floor <= 1/6`
(`margin_le_of_spreadFloorCertificateSixThree`). NOT PROVED at any parameters
where it is neither vacuous nor impossible. -/
def SpreadFloorCertificateSixThree (spread floor margin : ℚ) : Prop :=
  ∀ D : WeightedDesign 6 3, IsFlooredSpreadDesign D (spread : ℝ) (floor : ℝ) →
    HasLegMarginAtLeast D (margin : ℝ)

/-- At margin zero the quantitative hypothesis IS the qualitative one. -/
theorem spreadFloorCertificateSixThree_zero_iff_flooredSpreadCovering (spread floor : ℚ) :
    SpreadFloorCertificateSixThree spread floor 0
      ↔ FlooredSpreadCovering (spread : ℝ) (floor : ℝ) := by
  simp only [SpreadFloorCertificateSixThree, FlooredSpreadCovering, HasLegMarginAtLeast,
    Rat.cast_zero]

/-- **How a certificate reaches the assembly.** A nonnegative margin gives the
qualitative covering, which `Gtz.Reduction.SplitTransfer` consumes through
`Gtz.flooredSpreadDominationCertificate_six_of_flooredSpreadCovering` and
`Gtz.gtzWeightedSix_of_compactBranches`. -/
theorem flooredSpreadCovering_of_spreadFloorCertificateSixThree {spread floor margin : ℚ}
    (hmarginNonneg : 0 ≤ margin)
    (hcertificate : SpreadFloorCertificateSixThree spread floor margin) :
    FlooredSpreadCovering (spread : ℝ) (floor : ℝ) := by
  have hmarginNonnegReal : (0 : ℝ) ≤ (margin : ℝ) := by exact_mod_cast hmarginNonneg
  intro D hregion
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hminor, htie⟩ :=
    hcertificate D hregion
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hmarginNonnegReal.trans hminor, hmarginNonnegReal.trans htie⟩

/-- Lowering the margin weakens the conclusion (antitone in `margin`). -/
theorem spreadFloorCertificateSixThree_weakenMargin {spread floor margin smallerMargin : ℚ}
    (hle : smallerMargin ≤ margin)
    (hcertificate : SpreadFloorCertificateSixThree spread floor margin) :
    SpreadFloorCertificateSixThree spread floor smallerMargin := by
  intro D hregion
  have hleReal : (smallerMargin : ℝ) ≤ (margin : ℝ) := by exact_mod_cast hle
  exact hasLegMarginAtLeast_weaken hleReal (hcertificate D hregion)

/-- **Certificates transfer to the smaller region.** Raising either parameter
shrinks the region, so a certificate at the smaller parameters — the larger
region — implies the one at the larger parameters. -/
theorem spreadFloorCertificateSixThree_shrinkRegion
    {spread floor smallerSpread smallerFloor margin : ℚ}
    (hspreadLe : smallerSpread ≤ spread) (hfloorLe : smallerFloor ≤ floor)
    (hcertificate : SpreadFloorCertificateSixThree smallerSpread smallerFloor margin) :
    SpreadFloorCertificateSixThree spread floor margin := by
  intro D hregion
  have hspreadLeReal : (smallerSpread : ℝ) ≤ (spread : ℝ) := by exact_mod_cast hspreadLe
  have hfloorLeReal : (smallerFloor : ℝ) ≤ (floor : ℝ) := by exact_mod_cast hfloorLe
  exact hcertificate D (isFlooredSpreadDesign_mono hspreadLeReal hfloorLeReal hregion)

/-- The trivial direction, at a nonpositive margin: the unrestricted symmetric
covering already gives the legs their sign, and nothing more. -/
theorem spreadFloorCertificateSixThree_of_symmetricCovering {spread floor margin : ℚ}
    (hmarginNonpos : margin ≤ 0) (hcovering : SymmetricCovering 6) :
    SpreadFloorCertificateSixThree spread floor margin := by
  intro D hregion
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hminor, htie⟩ :=
    hcovering D hregion.1
  have hmarginNonposReal : (margin : ℝ) ≤ 0 := by exact_mod_cast hmarginNonpos
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hmarginNonposReal.trans hminor, hmarginNonposReal.trans htie⟩

/-! ## The region is bounded, which is what makes a certificate possible

`Gtz.Certificates.PositivstellensatzObstruction` kills the global
Positivstellensatz because the unrestricted tie system is inhabited. On the
floored spread region two things change. First the split-tetrahedron tie family
is excised (`Gtz.splitTetraDesign_not_hasSpreadAtLeast`) — the NAMED family, not
every tie: that every tie carries a parallel pair is `Gtz.HingeHoldsAtSize 6 3`,
which the repo records as OPEN and which is FALSE at `(5,3)`. Second the region
is BOUNDED, by the floor alone. The bound below is the Archimedean input a
Putinar-style argument consumes, and it degenerates exactly as the floor goes to
zero — the proved shadow of the measured quartic degeneration. -/

/-- **The floor caps the leverage.** `Gtz.weighted_leverage_le_one` says
`t_c * leverage_c <= 1` in any design, so a weight floor turns into a leverage
ceiling. -/
theorem leverageOf_le_of_hasWeightFloor (D : WeightedDesign m 3) {floor : ℝ}
    (hfloorPos : 0 < floor) (hfloor : HasWeightFloor D floor) (atomIndex : Fin m) :
    leverageOf (D.atom atomIndex) ≤ 1 / floor :=
  leverage_le_of_weight_floor D hfloorPos hfloor atomIndex

/-- **The floor caps the heavy excess**, the diagonal of the Gram gap. -/
theorem heavyExcess_le_of_hasWeightFloor (D : WeightedDesign m 3) {floor : ℝ}
    (hfloorPos : 0 < floor) (hfloor : HasWeightFloor D floor) (atomIndex : Fin m) :
    heavyExcess D atomIndex ≤ 1 / floor - 1 := by
  have hleverage := leverageOf_le_of_hasWeightFloor D hfloorPos hfloor atomIndex
  rw [heavyExcess]
  linarith

/-- **Cauchy-Schwarz on the atoms**: the squared pairing never exceeds the
product of the two leverages. No design hypothesis at all — this is the
inequality the spread parameter measures the slack in. -/
theorem atomPairing_sq_le_leverage_product (D : WeightedDesign m 3)
    (atomFirst atomSecond : Fin m) :
    atomPairing D atomFirst atomSecond ^ 2
      ≤ leverageOf (D.atom atomFirst) * leverageOf (D.atom atomSecond) := by
  rw [atomPairing, dotProduct, leverageOf, leverageOf]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (D.atom atomFirst) (D.atom atomSecond)

/-- **The floor caps the pairing too.** Cauchy-Schwarz bounds the squared
pairing by the leverage product and the floor caps each leverage, so the
FLOOR ALONE boxes the off-diagonal: neither the spread parameter nor
all-heaviness is used. Together with the excess bound this boxes the whole
region. -/
theorem atomPairing_sq_le_of_hasWeightFloor (D : WeightedDesign m 3)
    {floor : ℝ} (hfloorPos : 0 < floor) (hfloor : HasWeightFloor D floor)
    (atomFirst atomSecond : Fin m) :
    atomPairing D atomFirst atomSecond ^ 2 ≤ (1 / floor) ^ 2 := by
  have hleverageFirst := leverageOf_le_of_hasWeightFloor D hfloorPos hfloor atomFirst
  have hleverageSecond := leverageOf_le_of_hasWeightFloor D hfloorPos hfloor atomSecond
  have hleverageFirstNonneg : 0 ≤ leverageOf (D.atom atomFirst) := leverageOf_nonneg _
  have hleverageSecondNonneg : 0 ≤ leverageOf (D.atom atomSecond) := leverageOf_nonneg _
  have hcauchy := atomPairing_sq_le_leverage_product D atomFirst atomSecond
  nlinarith [hcauchy, hleverageFirst, hleverageSecond, hleverageFirstNonneg,
    hleverageSecondNonneg]

/-! ## The chart form, and the two constants that relate the margins

`Gtz.chartTie_eq` and `Gtz.chartMinorSum_eq` scale each leg by the weight product
of the triple. A margin therefore does not transfer verbatim: it transfers with
whatever bound on the weight product is available. Both bounds are elementary and
both are proved here, so the chart certificate and the raw certificate imply each
other with explicit constants and no assumption. -/

/-- The three weights of a triple of DISTINCT atoms sum to at most one — they are
part of a positive family summing to one. -/
theorem weightTripleSum_le_one (D : WeightedDesign m 3)
    {atomFirst atomSecond atomThird : Fin m} (hfirstSecond : atomFirst ≠ atomSecond)
    (hfirstThird : atomFirst ≠ atomThird) (hsecondThird : atomSecond ≠ atomThird) :
    D.weight atomFirst + D.weight atomSecond + D.weight atomThird ≤ 1 := by
  classical
  have hpart : ∑ atomIndex ∈ ({atomFirst, atomSecond, atomThird} : Finset (Fin m)),
      D.weight atomIndex ≤ ∑ atomIndex, D.weight atomIndex :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun atomIndex _ _ => (D.weight_pos atomIndex).le)
  rw [D.weight_sum_one] at hpart
  rwa [Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
    Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton, ← add_assoc] at hpart

/-- **Arithmetic-geometric mean, in the form the bridge consumes**: three
positive weights summing to at most `tripleBound` have product at most
`tripleBound^3 / 27`. Every weight-product ceiling below is this lemma at a
different bound. -/
theorem weightProduct_le_cube_div_twentySeven (D : WeightedDesign m 3) {tripleBound : ℝ}
    {atomFirst atomSecond atomThird : Fin m}
    (hsum : D.weight atomFirst + D.weight atomSecond + D.weight atomThird ≤ tripleBound) :
    D.weight atomFirst * D.weight atomSecond * D.weight atomThird ≤ tripleBound ^ 3 / 27 := by
  have hfirstPos := D.weight_pos atomFirst
  have hsecondPos := D.weight_pos atomSecond
  have hthirdPos := D.weight_pos atomThird
  have hamgm : 27 * (D.weight atomFirst * D.weight atomSecond * D.weight atomThird)
      ≤ (D.weight atomFirst + D.weight atomSecond + D.weight atomThird) ^ 3 := by
    nlinarith [sq_nonneg (D.weight atomFirst - D.weight atomSecond),
      sq_nonneg (D.weight atomSecond - D.weight atomThird),
      sq_nonneg (D.weight atomFirst - D.weight atomThird),
      mul_nonneg hthirdPos.le (sq_nonneg (D.weight atomFirst - D.weight atomSecond)),
      mul_nonneg hfirstPos.le (sq_nonneg (D.weight atomSecond - D.weight atomThird)),
      mul_nonneg hsecondPos.le (sq_nonneg (D.weight atomFirst - D.weight atomThird))]
  have hsumNonneg : (0 : ℝ) ≤ D.weight atomFirst + D.weight atomSecond + D.weight atomThird := by
    linarith
  have hcube : (D.weight atomFirst + D.weight atomSecond + D.weight atomThird) ^ 3
      ≤ tripleBound ^ 3 := pow_le_pow_left₀ hsumNonneg hsum 3
  linarith

/-- **The weight product of a distinct triple is at most `1/27`** — three positive
numbers summing to at most one. This is the constant that turns a chart margin
into a raw margin at any size and without a floor. -/
theorem weightProduct_le_inv_twentySeven (D : WeightedDesign m 3)
    {atomFirst atomSecond atomThird : Fin m} (hfirstSecond : atomFirst ≠ atomSecond)
    (hfirstThird : atomFirst ≠ atomThird) (hsecondThird : atomSecond ≠ atomThird) :
    D.weight atomFirst * D.weight atomSecond * D.weight atomThird ≤ 1 / 27 := by
  have hproduct := weightProduct_le_cube_div_twentySeven D
    (weightTripleSum_le_one D hfirstSecond hfirstThird hsecondThird)
  norm_num at hproduct
  exact hproduct

/-- **At size six a floor sharpens the triple sum**: the three atoms OUTSIDE the
triple each carry at least `floor`, so the triple itself carries at most
`1 - 3 floor`. The `1/27` above throws this away. -/
theorem weightTripleSum_le_of_hasWeightFloor (D : WeightedDesign 6 3) {floor : ℝ}
    (hfloor : HasWeightFloor D floor)
    {atomFirst atomSecond atomThird : Fin 6} (hfirstSecond : atomFirst ≠ atomSecond)
    (hfirstThird : atomFirst ≠ atomThird) (hsecondThird : atomSecond ≠ atomThird) :
    D.weight atomFirst + D.weight atomSecond + D.weight atomThird ≤ 1 - 3 * floor := by
  classical
  have hcard : ({atomFirst, atomSecond, atomThird} : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
      Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]
  have hsplit := Finset.sum_sdiff (f := D.weight)
    (Finset.subset_univ ({atomFirst, atomSecond, atomThird} : Finset (Fin 6)))
  have htripleSum : ∑ atomIndex ∈ ({atomFirst, atomSecond, atomThird} : Finset (Fin 6)),
      D.weight atomIndex
        = D.weight atomFirst + D.weight atomSecond + D.weight atomThird := by
    rw [Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
      Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton, ← add_assoc]
  have hcomplementCard :
      (Finset.univ \ ({atomFirst, atomSecond, atomThird} : Finset (Fin 6))).card = 3 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hcard, Finset.card_univ,
      Fintype.card_fin]
  have hcomplementLower : (3 : ℝ) * floor
      ≤ ∑ atomIndex ∈ Finset.univ \ ({atomFirst, atomSecond, atomThird} : Finset (Fin 6)),
        D.weight atomIndex := by
    calc (3 : ℝ) * floor
        = ∑ _atomIndex ∈ Finset.univ \ ({atomFirst, atomSecond, atomThird} : Finset (Fin 6)),
            floor := by
          rw [Finset.sum_const, hcomplementCard, nsmul_eq_mul]
          norm_num
      _ ≤ _ := Finset.sum_le_sum fun atomIndex _ => hfloor atomIndex
  rw [D.weight_sum_one, htripleSum] at hsplit
  linarith

/-- **The floored weight-product ceiling at size six.** Strictly sharper than
`1/27` for every positive floor — at `floor = 1/20` it is `(17/20)^3/27`, so the
chart-to-raw amplification improves from `27` to about `44`. -/
theorem weightProduct_le_of_hasWeightFloor (D : WeightedDesign 6 3) {floor : ℝ}
    (hfloor : HasWeightFloor D floor)
    {atomFirst atomSecond atomThird : Fin 6} (hfirstSecond : atomFirst ≠ atomSecond)
    (hfirstThird : atomFirst ≠ atomThird) (hsecondThird : atomSecond ≠ atomThird) :
    D.weight atomFirst * D.weight atomSecond * D.weight atomThird
      ≤ (1 - 3 * floor) ^ 3 / 27 :=
  weightProduct_le_cube_div_twentySeven D
    (weightTripleSum_le_of_hasWeightFloor D hfloor hfirstSecond hfirstThird hsecondThird)

/-- **Under a weight floor the product is at least `floor^3`** — the constant that
turns a raw margin into a chart margin. -/
theorem floorCube_le_weightProduct (D : WeightedDesign m 3) {floor : ℝ}
    (hfloorPos : 0 < floor) (hfloor : HasWeightFloor D floor)
    (atomFirst atomSecond atomThird : Fin m) :
    floor ^ 3 ≤ D.weight atomFirst * D.weight atomSecond * D.weight atomThird := by
  calc floor ^ 3 = floor * floor * floor := by ring
    _ ≤ D.weight atomFirst * floor * floor :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hfloor atomFirst) hfloorPos.le) hfloorPos.le
    _ ≤ D.weight atomFirst * D.weight atomSecond * floor :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hfloor atomSecond) (D.weight_pos atomFirst).le)
          hfloorPos.le
    _ ≤ D.weight atomFirst * D.weight atomSecond * D.weight atomThird :=
        mul_le_mul_of_nonneg_left (hfloor atomThird)
          (mul_pos (D.weight_pos atomFirst) (D.weight_pos atomSecond)).le

/-- **A triple carrying a margin in the projection chart.** The same statement as
`HasLegMarginAtLeast`, in the coordinates a certificate would actually be
searched in — gauge-quotiented, square-root free, and Archimedean for free. -/
def HasChartLegMarginAtLeast (D : WeightedDesign m 3) (margin : ℝ) : Prop :=
  ∃ first second third : Fin m,
    first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ margin ≤ chartGapWeightedMinorSum D first second third
      ∧ margin ≤ chartGapDeterminant D first second third

/-- **A chart margin is a raw margin, amplified by `27`.** The scaling factor
between the two is the weight product, at most `1/27` on a distinct triple. -/
theorem hasLegMarginAtLeast_of_hasChartLegMarginAtLeast (D : WeightedDesign m 3)
    {margin : ℝ} (hmarginNonneg : 0 ≤ margin)
    (hchart : HasChartLegMarginAtLeast D margin) :
    HasLegMarginAtLeast D (27 * margin) := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hchartMinor, hchartTie⟩ := hchart
  have hproductLe :=
    weightProduct_le_inv_twentySeven D hfirstSecond hfirstThird hsecondThird
  have hproductPos := weightProduct_pos D first second third
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_, ?_⟩
  · rw [← chartMinorSum_eq] at hchartMinor
    have hminorNonneg : 0 ≤ discriminantMinorSum D first second third :=
      (mul_nonneg_iff_of_pos_left hproductPos).mp (hmarginNonneg.trans hchartMinor)
    have hscaled := mul_le_mul_of_nonneg_right hproductLe hminorNonneg
    linarith
  · rw [← chartTie_eq] at hchartTie
    have htieNonneg : 0 ≤ discriminantTie D first second third :=
      (mul_nonneg_iff_of_pos_left hproductPos).mp (hmarginNonneg.trans hchartTie)
    have hscaled := mul_le_mul_of_nonneg_right hproductLe htieNonneg
    linarith

/-- **The floored amplification, at size six.** The same transfer through the
sharper product ceiling: with a weight floor the amplification is
`27 / (1 - 3 floor)^3` instead of `27`, which at `floor = 1/20` is `43.97` and
at `floor = 1/10` is `78.7`. Strictly better than
`hasLegMarginAtLeast_of_hasChartLegMarginAtLeast` whenever the floor is
positive, and the hypothesis `3 floor < 1` is free in the usable range
(`floor <= 1/6`). -/
theorem hasLegMarginAtLeast_of_hasChartLegMarginAtLeast_floored (D : WeightedDesign 6 3)
    {margin floor : ℝ} (hmarginNonneg : 0 ≤ margin) (hfloorBelowThird : 3 * floor < 1)
    (hfloor : HasWeightFloor D floor) (hchart : HasChartLegMarginAtLeast D margin) :
    HasLegMarginAtLeast D (27 / (1 - 3 * floor) ^ 3 * margin) := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hchartMinor, hchartTie⟩ := hchart
  have hproductLe :=
    weightProduct_le_of_hasWeightFloor D hfloor hfirstSecond hfirstThird hsecondThird
  have hproductPos := weightProduct_pos D first second third
  have hgapPos : (0 : ℝ) < 1 - 3 * floor := by linarith
  have hcubePos : (0 : ℝ) < (1 - 3 * floor) ^ 3 := pow_pos hgapPos 3
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_, ?_⟩
  · rw [← chartMinorSum_eq] at hchartMinor
    have hminorNonneg : 0 ≤ discriminantMinorSum D first second third :=
      (mul_nonneg_iff_of_pos_left hproductPos).mp (hmarginNonneg.trans hchartMinor)
    have hscaled := mul_le_mul_of_nonneg_right hproductLe hminorNonneg
    rw [div_mul_eq_mul_div, div_le_iff₀ hcubePos]
    nlinarith [hchartMinor, hscaled]
  · rw [← chartTie_eq] at hchartTie
    have htieNonneg : 0 ≤ discriminantTie D first second third :=
      (mul_nonneg_iff_of_pos_left hproductPos).mp (hmarginNonneg.trans hchartTie)
    have hscaled := mul_le_mul_of_nonneg_right hproductLe htieNonneg
    rw [div_mul_eq_mul_div, div_le_iff₀ hcubePos]
    nlinarith [hchartTie, hscaled]

/-- **A raw margin is a chart margin, damped by `floor^3`.** -/
theorem hasChartLegMarginAtLeast_of_hasLegMarginAtLeast (D : WeightedDesign m 3)
    {margin floor : ℝ} (hmarginNonneg : 0 ≤ margin) (hfloorPos : 0 < floor)
    (hfloor : HasWeightFloor D floor) (hraw : HasLegMarginAtLeast D margin) :
    HasChartLegMarginAtLeast D (floor ^ 3 * margin) := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hminor, htie⟩ :=
    hraw
  have hcube := floorCube_le_weightProduct D hfloorPos hfloor first second third
  have hcubePos := pow_pos hfloorPos 3
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_, ?_⟩
  · rw [← chartMinorSum_eq]
    nlinarith [hcube, hmarginNonneg, hminor, hcubePos]
  · rw [← chartTie_eq]
    nlinarith [hcube, hmarginNonneg, htie, hcubePos]

/-- **The chart-side hypothesis, still stated on designs**, so that
`Gtz.Quantitative.ProjectionChartLegs` supplies the translation and no bridge is
assumed. The free-standing version over all symmetric idempotents is
`FreeChartCertificateSixThree` below, and it implies this one outright. -/
def ChartSpreadFloorCertificateSixThree (spread floor margin : ℚ) : Prop :=
  ∀ D : WeightedDesign 6 3, IsFlooredSpreadDesign D (spread : ℝ) (floor : ℝ) →
    HasChartLegMarginAtLeast D (margin : ℝ)

/-- **A chart certificate is a raw certificate**, at twenty-seven times the
margin. -/
theorem spreadFloorCertificateSixThree_of_chartCertificate {spread floor margin : ℚ}
    (hmarginNonneg : 0 ≤ margin)
    (hchart : ChartSpreadFloorCertificateSixThree spread floor margin) :
    SpreadFloorCertificateSixThree spread floor (27 * margin) := by
  intro D hregion
  have hmarginNonnegReal : (0 : ℝ) ≤ (margin : ℝ) := by exact_mod_cast hmarginNonneg
  have hraw :=
    hasLegMarginAtLeast_of_hasChartLegMarginAtLeast D hmarginNonnegReal (hchart D hregion)
  rwa [show ((27 * margin : ℚ) : ℝ) = 27 * (margin : ℝ) by push_cast; ring]

/-- **A raw certificate is a chart certificate**, at `floor^3` times the margin —
so nothing is lost by searching in the chart. -/
theorem chartCertificate_of_spreadFloorCertificateSixThree {spread floor margin : ℚ}
    (hmarginNonneg : 0 ≤ margin) (hfloorPos : 0 < floor)
    (hcertificate : SpreadFloorCertificateSixThree spread floor margin) :
    ChartSpreadFloorCertificateSixThree spread floor (floor ^ 3 * margin) := by
  intro D hregion
  have hmarginNonnegReal : (0 : ℝ) ≤ (margin : ℝ) := by exact_mod_cast hmarginNonneg
  have hfloorPosReal : (0 : ℝ) < (floor : ℝ) := by exact_mod_cast hfloorPos
  have hchart := hasChartLegMarginAtLeast_of_hasLegMarginAtLeast D hmarginNonnegReal
    hfloorPosReal hregion.2.2 (hcertificate D hregion)
  rwa [show ((floor ^ 3 * margin : ℚ) : ℝ) = (floor : ℝ) ^ 3 * (margin : ℝ) by
    push_cast; ring]

/-! ## The chart MATRIX, and the certificate a solver would actually produce

Everything above quantifies over DESIGNS, so the chart translation of
`Gtz.Quantitative.ProjectionChartLegs` supplies the identity and nothing is
assumed. But a Positivstellensatz search does not see a design: it sees a
symmetric matrix constrained by `P * P = P` and `trace P = 3`, and a weight
vector. This section builds that matrix out of a design and PROVES the two
structural constraints, so a certificate quantified over all such pairs — a
strictly stronger statement, since it covers pairs no design produces — can be
consumed here with no gap left over. -/

/-- The Stiefel frame of a design: the `m x 3` matrix whose rows are the atoms
scaled by the square roots of their weights. Parseval is exactly the statement
that its COLUMNS are orthonormal. -/
noncomputable def chartFrame (D : WeightedDesign m 3) : Matrix (Fin m) (Fin 3) ℝ :=
  fun atomIndex coordinate => chartBasis D atomIndex coordinate

/-- **The projection chart as a MATRIX**, `P = V V^T`, whose entries are
`Gtz.chartEntry`. -/
noncomputable def chartMatrix (D : WeightedDesign m 3) : Matrix (Fin m) (Fin m) ℝ :=
  fun atomFirst atomSecond => chartEntry D atomFirst atomSecond

/-- Parseval read at one entry of the `3 x 3` identity: the weighted atom outer
products resolve the identity coordinatewise. -/
theorem weightedAtomProduct_sum (D : WeightedDesign m 3) (coordFirst coordSecond : Fin 3) :
    ∑ atomIndex, D.weight atomIndex
        * (D.atom atomIndex coordFirst * D.atom atomIndex coordSecond)
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) coordFirst coordSecond := by
  have hparseval := congrFun (congrFun D.isParseval coordFirst) coordSecond
  simpa [Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply, mul_assoc] using hparseval

/-- **Parseval IS column orthonormality of the Stiefel frame**, `V^T V = I`. -/
theorem chartFrame_transpose_mul_self (D : WeightedDesign m 3) :
    (chartFrame D)ᵀ * chartFrame D = 1 := by
  ext coordFirst coordSecond
  rw [Matrix.mul_apply, ← weightedAtomProduct_sum D coordFirst coordSecond]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  have hsquare := Real.mul_self_sqrt (D.weight_pos atomIndex).le
  simp only [Matrix.transpose_apply, chartFrame, chartBasis]
  calc Real.sqrt (D.weight atomIndex) * D.atom atomIndex coordFirst
        * (Real.sqrt (D.weight atomIndex) * D.atom atomIndex coordSecond)
      = Real.sqrt (D.weight atomIndex) * Real.sqrt (D.weight atomIndex)
        * (D.atom atomIndex coordFirst * D.atom atomIndex coordSecond) := by ring
    _ = _ := by rw [hsquare]

theorem chartMatrix_eq_frame_mul_transpose (D : WeightedDesign m 3) :
    chartMatrix D = chartFrame D * (chartFrame D)ᵀ := by
  ext atomFirst atomSecond
  simp only [chartMatrix, chartEntry, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
    chartFrame]

/-- **The chart matrix is IDEMPOTENT**: `(V V^T)(V V^T) = V (V^T V) V^T = V V^T`.
This and the trace are what a free-standing chart certificate assumes about `P`;
both are theorems, not hypotheses. -/
theorem chartMatrix_isIdempotent (D : WeightedDesign m 3) :
    chartMatrix D * chartMatrix D = chartMatrix D := by
  rw [chartMatrix_eq_frame_mul_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (chartFrame D)ᵀ, chartFrame_transpose_mul_self, Matrix.one_mul]

theorem chartMatrix_isSymm (D : WeightedDesign m 3) : (chartMatrix D).IsSymm := by
  ext atomFirst atomSecond
  exact chartEntry_comm D atomSecond atomFirst

/-- **The chart matrix has trace exactly three** — the rank of the design,
recovered from column orthonormality by exchanging the two sums. -/
theorem chartMatrix_trace (D : WeightedDesign m 3) : (chartMatrix D).trace = 3 := by
  have hdiagonal : ∀ atomIndex : Fin m, chartMatrix D atomIndex atomIndex
      = ∑ coordinate, chartBasis D atomIndex coordinate * chartBasis D atomIndex coordinate :=
    fun atomIndex => rfl
  calc (chartMatrix D).trace
      = ∑ atomIndex, ∑ coordinate,
          chartBasis D atomIndex coordinate * chartBasis D atomIndex coordinate := by
        simp only [Matrix.trace, Matrix.diag_apply, hdiagonal]
    _ = ∑ coordinate, ∑ atomIndex,
          chartBasis D atomIndex coordinate * chartBasis D atomIndex coordinate :=
        Finset.sum_comm
    _ = 3 := by
        have hcolumn : ∀ coordinate : Fin 3,
            ∑ atomIndex, chartBasis D atomIndex coordinate * chartBasis D atomIndex coordinate
              = 1 := by
          intro coordinate
          have hframe := congrFun (congrFun (chartFrame_transpose_mul_self D) coordinate)
            coordinate
          rw [Matrix.mul_apply] at hframe
          simpa [Matrix.transpose_apply, chartFrame, Matrix.one_apply] using hframe
        rw [Finset.sum_congr rfl fun coordinate _ => hcolumn coordinate]
        simp

/-- The gap diagonal of an ABSTRACT chart pair `(chart, weight)` — no design in
sight. -/
def chartGapDiagonalOf (chart : Matrix (Fin m) (Fin m) ℝ) (weight : Fin m → ℝ)
    (atomIndex : Fin m) : ℝ :=
  chart atomIndex atomIndex - weight atomIndex

/-- The tie leg of an abstract chart pair: the determinant of the `3 x 3` gap
block. Definitionally `Gtz.chartGapDeterminant` once the pair comes from a
design. -/
def chartGapDeterminantOf (chart : Matrix (Fin m) (Fin m) ℝ) (weight : Fin m → ℝ)
    (atomFirst atomSecond atomThird : Fin m) : ℝ :=
  chartGapDiagonalOf chart weight atomFirst * chartGapDiagonalOf chart weight atomSecond
      * chartGapDiagonalOf chart weight atomThird
    - chartGapDiagonalOf chart weight atomFirst * chart atomSecond atomThird ^ 2
    - chartGapDiagonalOf chart weight atomSecond * chart atomFirst atomThird ^ 2
    - chartGapDiagonalOf chart weight atomThird * chart atomFirst atomSecond ^ 2
    + 2 * (chart atomFirst atomSecond * chart atomFirst atomThird
        * chart atomSecond atomThird)

/-- The minor-sum leg of an abstract chart pair. -/
def chartGapWeightedMinorSumOf (chart : Matrix (Fin m) (Fin m) ℝ) (weight : Fin m → ℝ)
    (atomFirst atomSecond atomThird : Fin m) : ℝ :=
  weight atomThird * (chartGapDiagonalOf chart weight atomFirst
      * chartGapDiagonalOf chart weight atomSecond - chart atomFirst atomSecond ^ 2)
    + weight atomSecond * (chartGapDiagonalOf chart weight atomFirst
      * chartGapDiagonalOf chart weight atomThird - chart atomFirst atomThird ^ 2)
    + weight atomFirst * (chartGapDiagonalOf chart weight atomSecond
      * chartGapDiagonalOf chart weight atomThird - chart atomSecond atomThird ^ 2)

theorem chartGapDeterminantOf_eq (D : WeightedDesign m 3)
    (atomFirst atomSecond atomThird : Fin m) :
    chartGapDeterminantOf (chartMatrix D) D.weight atomFirst atomSecond atomThird
      = chartGapDeterminant D atomFirst atomSecond atomThird := rfl

theorem chartGapWeightedMinorSumOf_eq (D : WeightedDesign m 3)
    (atomFirst atomSecond atomThird : Fin m) :
    chartGapWeightedMinorSumOf (chartMatrix D) D.weight atomFirst atomSecond atomThird
      = chartGapWeightedMinorSum D atomFirst atomSecond atomThird := rfl

/-- **All-heaviness in the chart**: `P_cc > t_c`, since `P_cc = t_c * leverage_c`
and the weight is positive. -/
theorem chartMatrix_diagonal_gt_weight_of_allHeavy {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) (atomIndex : Fin m) :
    D.weight atomIndex < chartMatrix D atomIndex atomIndex := by
  have hself : chartMatrix D atomIndex atomIndex
      = D.weight atomIndex * leverageOf (D.atom atomIndex) := chartEntry_self D atomIndex
  rw [hself]
  nlinarith [hheavy atomIndex, D.weight_pos atomIndex]

/-- **THE FREE-STANDING CHART CERTIFICATE.** Every symmetric idempotent of trace
three, paired with a positive weight vector summing to one that clears the floor,
is all-heavy in the chart sense and spread in the chart sense, has a triple whose
two chart legs are at least `margin`. No design appears; this is a statement
about `(P, t)` pairs, which is what an SOS or LP search proves.

It is STRICTLY STRONGER than `ChartSpreadFloorCertificateSixThree` — the pairs it
ranges over include ones no design produces — and
`chartCertificateSixThree_of_freeChartCertificate` turns it into the design-side
statement with nothing assumed, because `chartMatrix_isSymm`,
`chartMatrix_isIdempotent` and `chartMatrix_trace` are theorems. -/
def FreeChartCertificateSixThree (spread floor margin : ℚ) : Prop :=
  ∀ (chart : Matrix (Fin 6) (Fin 6) ℝ) (weight : Fin 6 → ℝ),
    chart.IsSymm → chart * chart = chart → chart.trace = 3 →
    (∀ atomIndex, 0 < weight atomIndex) → (∑ atomIndex, weight atomIndex) = 1 →
    (∀ atomIndex, (floor : ℝ) ≤ weight atomIndex) →
    (∀ atomIndex, weight atomIndex < chart atomIndex atomIndex) →
    (∀ atomFirst atomSecond, atomFirst ≠ atomSecond →
      chart atomFirst atomSecond ^ 2
        ≤ (1 - (spread : ℝ)) * (chart atomFirst atomFirst * chart atomSecond atomSecond)) →
    ∃ first second third : Fin 6,
      first ≠ second ∧ first ≠ third ∧ second ≠ third
        ∧ (margin : ℝ) ≤ chartGapWeightedMinorSumOf chart weight first second third
        ∧ (margin : ℝ) ≤ chartGapDeterminantOf chart weight first second third

/-- **The solver's output is this file's hypothesis.** Every constraint the free
certificate assumes is discharged for a region design: symmetry, idempotency and
trace by the three theorems above, positivity and normalisation by the design
structure, the floor by region membership, all-heaviness by
`chartMatrix_diagonal_gt_weight_of_allHeavy`, and the spread by
`Gtz.chartSpread_iff`. -/
theorem chartCertificateSixThree_of_freeChartCertificate {spread floor margin : ℚ}
    (hfree : FreeChartCertificateSixThree spread floor margin) :
    ChartSpreadFloorCertificateSixThree spread floor margin := by
  intro D hregion
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hminor, htie⟩ :=
    hfree (chartMatrix D) D.weight (chartMatrix_isSymm D) (chartMatrix_isIdempotent D)
      (chartMatrix_trace D) D.weight_pos D.weight_sum_one hregion.2.2
      (fun atomIndex => chartMatrix_diagonal_gt_weight_of_allHeavy hregion.1 atomIndex)
      (fun atomFirst atomSecond hne =>
        (chartSpread_iff D (spread : ℝ) atomFirst atomSecond).mpr
          (hregion.2.1 atomFirst atomSecond hne))
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_, ?_⟩
  · rwa [chartGapWeightedMinorSumOf_eq] at hminor
  · rwa [chartGapDeterminantOf_eq] at htie

/-- **The whole route in one step**: a free-standing chart certificate at a
nonnegative margin gives the raw certificate at twenty-seven times that margin,
hence — through `flooredSpreadCovering_of_spreadFloorCertificateSixThree` — the
qualitative covering the assembly consumes. -/
theorem spreadFloorCertificateSixThree_of_freeChartCertificate {spread floor margin : ℚ}
    (hmarginNonneg : 0 ≤ margin)
    (hfree : FreeChartCertificateSixThree spread floor margin) :
    SpreadFloorCertificateSixThree spread floor (27 * margin) :=
  spreadFloorCertificateSixThree_of_chartCertificate hmarginNonneg
    (chartCertificateSixThree_of_freeChartCertificate hfree)

/-! ## The three boundaries of the parameter box

Above weight floor `1/6` the region at size six is empty, and above spread `1`
it is empty for a second reason, so on both sides the hypothesis holds at every
margin and says nothing. Below `spread = 4/5`, `floor = 1/6` the region contains
the icosahedral design, whose tie leg is bounded, so no margin above `51/25` is
available. Between them is where a search must live. (A third, uninteresting,
triviality zone sits at very negative margins: the region is bounded, so the legs
are bounded below on it and a sufficiently negative margin is certified for free.
No theorem below names it, because `flooredSpreadCovering_of_...` only consumes
nonnegative margins.) -/

/-- **The hypothesis is VACUOUS above floor `1/6`.** Six positive weights summing
to one cannot all exceed `1/6`, so the region at size six is empty and every
margin is certified for free. A certificate reported at such a floor proves
nothing; the general-size version of the emptiness is
`Gtz.not_isFlooredSpreadDesign_of_sizeInv_lt_floor` in
`Gtz.Reduction.SplitTransfer`, which this layer cannot import without a cycle. -/
theorem spreadFloorCertificateSixThree_of_sixth_lt_floor {spread floor margin : ℚ}
    (hfloorAboveAverage : 1 / 6 < floor) :
    SpreadFloorCertificateSixThree spread floor margin := by
  intro D hregion
  exfalso
  have hfloorAboveAverageReal : (1 : ℝ) / 6 < (floor : ℝ) := by
    rw [show (1 : ℝ) / 6 = ((1 / 6 : ℚ) : ℝ) by norm_num]
    exact_mod_cast hfloorAboveAverage
  have hsixFloorLe : (6 : ℝ) * (floor : ℝ) ≤ ∑ atomIndex, D.weight atomIndex := by
    calc (6 : ℝ) * (floor : ℝ) = ∑ _atomIndex : Fin 6, (floor : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
      _ ≤ ∑ atomIndex, D.weight atomIndex :=
          Finset.sum_le_sum fun atomIndex _ => hregion.2.2 atomIndex
  rw [D.weight_sum_one] at hsixFloorLe
  linarith

/-- **The hypothesis is VACUOUS above spread `1` too.** A spread above one asks
every squared pairing to be at most a NEGATIVE multiple of a positive leverage
product, which no all-heavy design can satisfy. The floor guard alone leaves this
side of the box unguarded, and the guard is needed: the region is measured empty
well below spread `1` — six real lines in three-space cannot beat the
icosahedron's `4/5` — so the genuinely interesting window `(4/5, 1]` is
certified for free by nothing proved here and by this theorem only above `1`. -/
theorem spreadFloorCertificateSixThree_of_one_lt_spread {spread floor margin : ℚ}
    (hspreadAboveOne : 1 < spread) :
    SpreadFloorCertificateSixThree spread floor margin := by
  intro D hregion
  exfalso
  have hspreadReal : (1 : ℝ) < (spread : ℝ) := by exact_mod_cast hspreadAboveOne
  have hheavyFirst := hregion.1 0
  have hheavySecond := hregion.1 1
  have hbound := hregion.2.1 0 1 (by decide)
  have hproductPos : 0 < leverageOf (D.atom 0) * leverageOf (D.atom 1) := by nlinarith
  have hnegative : (1 - (spread : ℝ)) * (leverageOf (D.atom 0) * leverageOf (D.atom 1)) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hproductPos
  nlinarith [hbound, hnegative, sq_nonneg (atomPairing D 0 1)]

/-- The icosahedral design's minor-sum leg is exactly `33/5` at every triple —
every excess is `2`, every squared pairing is `9/5`, and the leg sees only
squares. Recorded because it shows the minor-sum leg is NOT the binding one
there: the ceiling comes from the tie leg. -/
theorem icosaDesign_discriminantMinorSum_eq {atomFirst atomSecond atomThird : Fin 6}
    (hfirstSecond : atomFirst ≠ atomSecond) (hfirstThird : atomFirst ≠ atomThird)
    (hsecondThird : atomSecond ≠ atomThird) :
    discriminantMinorSum icosaDesign atomFirst atomSecond atomThird = 33 / 5 := by
  have hexcessFirst : heavyExcess icosaDesign atomFirst = 2 := by
    rw [heavyExcess, icosaDesign_leverage]; norm_num
  have hexcessSecond : heavyExcess icosaDesign atomSecond = 2 := by
    rw [heavyExcess, icosaDesign_leverage]; norm_num
  have hexcessThird : heavyExcess icosaDesign atomThird = 2 := by
    rw [heavyExcess, icosaDesign_leverage]; norm_num
  have hpairFirstSecond : atomPairing icosaDesign atomFirst atomSecond ^ 2 = 9 / 5 := by
    rw [atomPairing, icosaDesign_atom]; exact icosaAtom_dot_sq_of_ne hfirstSecond
  have hpairFirstThird : atomPairing icosaDesign atomFirst atomThird ^ 2 = 9 / 5 := by
    rw [atomPairing, icosaDesign_atom]; exact icosaAtom_dot_sq_of_ne hfirstThird
  have hpairSecondThird : atomPairing icosaDesign atomSecond atomThird ^ 2 = 9 / 5 := by
    rw [atomPairing, icosaDesign_atom]; exact icosaAtom_dot_sq_of_ne hsecondThird
  rw [discriminantMinorSum, hexcessFirst, hexcessSecond, hexcessThird,
    hpairFirstSecond, hpairFirstThird, hpairSecondThird]
  norm_num

/-- **The icosahedral tie leg is at most `51/25` at EVERY triple.** With every
excess `2` and every squared pairing `9/5` the leg collapses to
`-14/5 + 2 * (triangle product)`, and the triangle product squares to `(9/5)^3`,
so it is at most `27 * sqrt 5 / 25`. The rational bound `51/25 = 2.04` is what a
kernel can check without square roots; MEASURED in exact arithmetic and NOT
proved here, the sharp bound is `54 * sqrt 5 / 25 - 14/5 = 2.02990...`, so this
loses about half a percent. -/
theorem icosaDesign_discriminantTie_le {atomFirst atomSecond atomThird : Fin 6}
    (hfirstSecond : atomFirst ≠ atomSecond) (hfirstThird : atomFirst ≠ atomThird)
    (hsecondThird : atomSecond ≠ atomThird) :
    discriminantTie icosaDesign atomFirst atomSecond atomThird ≤ 51 / 25 := by
  have hexcessFirst : heavyExcess icosaDesign atomFirst = 2 := by
    rw [heavyExcess, icosaDesign_leverage]; norm_num
  have hexcessSecond : heavyExcess icosaDesign atomSecond = 2 := by
    rw [heavyExcess, icosaDesign_leverage]; norm_num
  have hexcessThird : heavyExcess icosaDesign atomThird = 2 := by
    rw [heavyExcess, icosaDesign_leverage]; norm_num
  have hpairFirstSecond : atomPairing icosaDesign atomFirst atomSecond ^ 2 = 9 / 5 := by
    rw [atomPairing, icosaDesign_atom]; exact icosaAtom_dot_sq_of_ne hfirstSecond
  have hpairFirstThird : atomPairing icosaDesign atomFirst atomThird ^ 2 = 9 / 5 := by
    rw [atomPairing, icosaDesign_atom]; exact icosaAtom_dot_sq_of_ne hfirstThird
  have hpairSecondThird : atomPairing icosaDesign atomSecond atomThird ^ 2 = 9 / 5 := by
    rw [atomPairing, icosaDesign_atom]; exact icosaAtom_dot_sq_of_ne hsecondThird
  have htriangleSq : (atomPairing icosaDesign atomFirst atomSecond
        * atomPairing icosaDesign atomFirst atomThird
        * atomPairing icosaDesign atomSecond atomThird) ^ 2 = 729 / 125 := by
    have hexpand : (atomPairing icosaDesign atomFirst atomSecond
          * atomPairing icosaDesign atomFirst atomThird
          * atomPairing icosaDesign atomSecond atomThird) ^ 2
        = atomPairing icosaDesign atomFirst atomSecond ^ 2
          * atomPairing icosaDesign atomFirst atomThird ^ 2
          * atomPairing icosaDesign atomSecond atomThird ^ 2 := by ring
    rw [hexpand, hpairFirstSecond, hpairFirstThird, hpairSecondThird]
    norm_num
  rw [discriminantTie, hexcessFirst, hexcessSecond, hexcessThird,
    hpairFirstSecond, hpairFirstThird, hpairSecondThird]
  nlinarith [htriangleSq, sq_nonneg (atomPairing icosaDesign atomFirst atomSecond
      * atomPairing icosaDesign atomFirst atomThird
      * atomPairing icosaDesign atomSecond atomThird - 121 / 50)]

/-- **THE CEILING.** No certificate at `spread <= 4/5` and `floor <= 1/6` can
carry a margin above `51/25`, because the icosahedral design sits in the region
at those extreme parameters and its tie leg is bounded there. So the margin is a
constrained parameter and not free notation.

HOW WEAK IT IS, stated plainly: the leg margin MEASURED at the recommended
`spread = 1/10`, `floor = 1/20` is about `2.09e-2`, which is `98` times smaller.
A future stage reporting a margin of `1` at those parameters would pass this
ceiling and still be wrong by a factor of fifty. The ceiling rules out only gross
overclaims; sharpening it needs a second in-region witness near the measured
minimiser (see the header's MEASURED section for its geometry, and the note there
on the rational-square-weight construction that would make such a witness
kernel-checkable). -/
theorem margin_le_of_spreadFloorCertificateSixThree {spread floor margin : ℚ}
    (hspreadLe : (spread : ℝ) ≤ 4 / 5) (hfloorLe : (floor : ℝ) ≤ 1 / 6)
    (hcertificate : SpreadFloorCertificateSixThree spread floor margin) :
    (margin : ℝ) ≤ 51 / 25 := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, _, htie⟩ :=
    hcertificate icosaDesign
      (isFlooredSpreadDesign_mono hspreadLe hfloorLe icosaDesign_isFlooredSpreadDesign)
  exact htie.trans (icosaDesign_discriminantTie_le hfirstSecond hfirstThird hsecondThird)

end Gtz

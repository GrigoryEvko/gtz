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
zero.  This file states the margin version, connects it back to the qualitative
one, translates it into the projection chart with explicit constants, and proves
the two boundaries any search must respect: the region is EMPTY above weight
floor `1/6`, so the hypothesis is vacuous there, and the region CONTAINS the
icosahedral design, so no certificate at usable parameters can claim a margin
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
the larger parameters (`spreadFloorCertificateSixThree_mono_region`), and
lowering the margin weakens the conclusion
(`spreadFloorCertificateSixThree_mono_margin`).

**The chart form, with the constants, and no bridge hypothesis.**
`HasChartLegMarginAtLeast` and `ChartSpreadFloorCertificateSixThree` are the same
statements written in the projection chart.  Because `Gtz.chartTie_eq` and
`Gtz.chartMinorSum_eq` scale each leg by the weight product, the two margins are
related by explicit constants and NOTHING is assumed:

  `weightProduct_le_inv_twentySeven` — the weight product of a triple of
    DISTINCT atoms is at most `1/27` (three positive weights out of a family
    summing to one, then AM-GM), so a chart margin `c >= 0` yields a raw margin
    `27 c` (`hasLegMarginAtLeast_of_hasChartLegMarginAtLeast`);
  `floorCube_le_weightProduct` — under a weight floor the product is at least
    `floor^3`, so a raw margin `eps >= 0` yields a chart margin `floor^3 eps`
    (`hasChartLegMarginAtLeast_of_hasLegMarginAtLeast`).

Both certificates therefore imply each other with those constants
(`spreadFloorCertificateSixThree_of_chartCertificate`,
`chartCertificate_of_spreadFloorCertificateSixThree`).  THE HONEST CAVEAT: the
chart statements here quantify over DESIGNS, evaluating `Gtz.chartEntry` on a
design, so the translation is the proved identity of
`Gtz.Quantitative.ProjectionChartLegs` and there is no gap.  A solver-side
certificate quantifying over ALL symmetric idempotents `P` of trace three with a
positive weight vector is a STRICTLY STRONGER statement — it covers a superset —
so it too would suffice, but only once someone proves that a design's chart data
satisfies whatever constraints that certificate assumed.  `P^2 = P` and
`trace P = 3` for a design's chart matrix are true and provable
(`P = V V^T` with `V^T V = I` by Parseval, and the trace is `Gtz.sum_weighted_leverage`)
but are NOT proved here; do not silently read a free-standing chart certificate
as this file's hypothesis without them.

**The region is bounded, which is why a certificate can exist at all.**
`leverageOf_le_of_hasWeightFloor` (from `Gtz.weighted_leverage_le_one`) caps every
leverage at `1/floor`, `heavyExcess_le_of_hasWeightFloor` caps every excess at
`1/floor - 1`, and `atomPairing_sq_le_of_isFlooredSpreadDesign` caps every squared
pairing at `1/floor^2`.  So the floored spread region is contained in a box whose
size is set by the floor alone — the Archimedean input every Putinar-style
argument needs, and the reason `Gtz.Certificates.PositivstellensatzObstruction`
does not apply here.

**The two boundaries.**  `spreadFloorCertificateSixThree_of_sixth_lt_floor`: six
weights summing to one cannot all exceed `1/6`, so above that floor the region is
empty and the hypothesis holds vacuously at EVERY margin — a certificate there
proves nothing.  In the other direction `icosaDesign_isFlooredSpreadDesign`
(already proved in `Gtz.Quantitative.FlooredSpreadRegion`) puts the icosahedral
design in the region at `spread = 4/5`, `floor = 1/6`, and
`icosaDesign_discriminantTie_le` computes its tie leg: every excess is `2` and
every squared pairing is `9/5`, so the leg is `-14/5` plus twice the triangle
product, whose square is `(9/5)^3` — hence at most `51/25` at EVERY triple.
`margin_le_of_spreadFloorCertificateSixThree` reads that back as a CEILING: no
certificate at `spread <= 4/5`, `floor <= 1/6` can carry a margin above `51/25`.
`icosaDesign_discriminantMinorSum_eq` records the companion exact value `33/5`,
which shows the minor-sum leg is not the binding one there.

## CITED (proved elsewhere in this repo, used in the proofs below)

`WeightedDesign`, `leverageOf` (`Gtz.Core.Basic`); `weighted_leverage_le_one`,
`leverage_le_of_weight_floor` (`Gtz.Design.LeverageBound`); `heavyExcess`,
`atomPairing`, `discriminantMinorSum`, `discriminantTie`
(`Gtz.Quantitative.DiscriminantSystem`); `SymmetricCovering`
(`Gtz.Quantitative.PositivstellensatzRankThree`); `HasSpreadAtLeast`,
`HasWeightFloor`, `IsFlooredSpreadDesign`, `isFlooredSpreadDesign_mono`,
`FlooredSpreadCovering`, `leverageOf_nonneg`, `icosaDesign_leverage`,
`icosaDesign_isFlooredSpreadDesign` (`Gtz.Quantitative.FlooredSpreadRegion`);
`icosaDesign`, `icosaDesign_atom`, `icosaAtom_dot_sq_of_ne`
(`Gtz.Quantitative.RealnessEngine`); `chartGapDeterminant`,
`chartGapWeightedMinorSum`, `chartTie_eq`, `chartMinorSum_eq`,
`weightProduct_pos` (`Gtz.Quantitative.ProjectionChartLegs`).

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

Every number below came from the epsilon-surface and certificate-hunt stages.
All were computed in the projection chart, whose leg translation is the PROVED
content of `Gtz.Quantitative.ProjectionChartLegs`, cross-validated against the
raw `(g,t)` definitions symbolically over `Q` (difference identically zero on
seven exactly rational design families), at seventy digits (worst relative
discrepancy `2.5e-68` at Parseval residual `3.6e-71`), and in float64
division-free form (worst absolute discrepancy `3.3e-16` over `500` designs
times `20` triples).  Solver noise floor `1.6e-14`, calibrated on three anchors
containing an exact value-one point.  No design of value below one was found at
any setting.

* THE MARGIN SURFACE, and TWO CORRECTIONS to the campaign's prior ledger.
  Writing `epsilon` for the least eigenvalue margin — the minimum over the
  region of `max over triples of the least eigenvalue of the triple Gram`, minus
  one — the measured surface at `floor` in `{0.01, 0.03, 0.05, 0.10}` is
  `6.4e-7`, `5.176468e-5`, `3.9765868e-4`, `6.21287002e-3`, and it is CONSTANT
  to ten significant figures across `spread` in `(0, 0.56]`.  So (i) the law is
  `epsilon` about `64 * floor^4`, log-log slope `3.95` to `4.01` on
  `[0.012, 0.16]` — the prior "roughly like `floor^2`" is REFUTED; and (ii)
  `epsilon` is INDEPENDENT of `spread`, which only has to be nonzero.  Ties are a
  square-root cusp, not the binding constraint: opening a duplicated pair to
  squared sine `s` costs about `0.8 * sqrt s`, exceeding the floor margin already
  at `spread` about `2.5e-7`.  Below `floor` about `0.008` the solver loses the
  branch, so all reported values are UPPER bounds.
* THE LEG MARGIN, which is what a certificate actually targets, is far more
  comfortable and scales as the SQUARE not the fourth power: the minimum over
  the region of `max over triples of min of the two legs` measures `7.62e-4`,
  `7.0579268e-3`, `2.0901626e-2`, `9.9364866e-2` at the same four floors, i.e.
  about `8 * floor^2`, also independent of `spread`.  The tie leg binds
  everywhere; the minor-sum leg exceeds one at every minimiser.  This is the
  quantity `SpreadFloorCertificateSixThree` is stated in.
* THE MINIMISER, identical in all sixteen measured cells: six atoms in three
  orbits of size two under a Klein four-group in `O(3)` (residual `4e-14`), four
  weights pinned at the floor and two free at `(1 - 4 floor)/2`, ten of the
  twenty triples exactly at the level.  The active set is the FLOOR ALONE —
  spread is strictly inactive (the minimiser sits at squared sine about `0.598`)
  and all-heaviness is strictly inactive (least leverage `1.65` to `2.18`).
  Mechanism: a four-atom tight core plus two dust atoms at the floor; the
  quartic is the rate at which floor-pinned dust lifts a four-atom tie, quartic
  because the perturbation moves ALONG the tie manifold to first order.
* RECOMMENDED TARGET `spread = 1/10`, `floor = 1/20`: leg margin `2.09e-2`,
  twelve orders above the solver floor, at eigenvalue margin `3.97658684366e-4`.
  `floor = 1/10` doubles the leg margin to `9.9e-2` if the assembly can afford
  weights that large.  Do not push the floor below `1/50`: the margin falls as
  the fourth power and rational rounding becomes hopeless.
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
  `-14.613593823493521334`, and only about `8.3%` of sampled region designs have
  it positive at every triple.  The disjunction must therefore be lifted, one
  multiplier per engaged triple, giving `27 + 20 = 47` variables and degree-four
  failure generators — about `1.2e9` monomials at degree eight, not
  constructible.  (b) The near-orthogonality bridge
  `Gtz.flooredSpreadCovering_of_alwaysDominantPairingTriangle` FAILS on the
  region: at eighty digits the triangle margin reaches `-3.1218130729731571859`
  at the hunt stage's parameters, and about `19%` of sampled region designs have
  a triangle-free good-pair graph.  (The figure `-3.03e-1` recorded in
  `Gtz.Quantitative.FlooredSpreadRegion` is the same sign at DIFFERENT parameters,
  `spread = 1/5`, `floor = 1/20`; the two stages minimised over different regions,
  so the magnitudes are not comparable and neither refutes the other.)
  Read through Mantel's theorem the bridge asks a six-vertex graph to contain a
  triangle, and the complex trine realises the extremal triangle-free graph
  `K_{3,3}` exactly, its nine good pairs being precisely the cross-block ones at
  defect exactly zero.  (c) The kernel itself is the binding cost, not the
  solver: `ring` on a rational sum-of-squares identity in twenty-seven variables
  costs `4.8s` at `33` monomials, `24.4s` at `194`, and `149.3s` at `579` with
  `4.3 GB` peak — roughly quadratic in monomial count.  Any certificate must be
  designed to a monomial budget, or discharged reflectively rather than by
  tactic.
* THE ICOSAHEDRAL CEILING IS NEARLY SHARP.  `icosaDesign_discriminantTie_le`
  proves the rational bound `51/25 = 2.04`; the exact maximum of the tie leg over
  the icosahedron's triples is `54 * sqrt 5 / 25 - 14/5 = 2.02990683...`, attained
  (the triangle product has one sign for the dominating triples and the other for
  the rest, which is the realness content in its smallest instance).  The proved
  ceiling is thus within `0.5%` of sharp.  It is also about a hundred times the
  measured leg margin at the recommended target, so it constrains the parameter
  without being the operative bound.
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

theorem hasLegMarginAtLeast_mono {D : WeightedDesign m 3} {margin smallerMargin : ℝ}
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

/-- Lowering the margin weakens the conclusion. -/
theorem spreadFloorCertificateSixThree_mono_margin {spread floor margin smallerMargin : ℚ}
    (hle : smallerMargin ≤ margin)
    (hcertificate : SpreadFloorCertificateSixThree spread floor margin) :
    SpreadFloorCertificateSixThree spread floor smallerMargin := by
  intro D hregion
  have hleReal : (smallerMargin : ℝ) ≤ (margin : ℝ) := by exact_mod_cast hle
  exact hasLegMarginAtLeast_mono hleReal (hcertificate D hregion)

/-- **Certificates transfer to the smaller region.** Raising either parameter
shrinks the region, so a certificate at the smaller parameters — the larger
region — implies the one at the larger parameters. -/
theorem spreadFloorCertificateSixThree_mono_region
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
floored spread region two things change: the ties are excised
(`Gtz.splitTetraDesign_not_hasSpreadAtLeast`) and the region is BOUNDED, by the
floor alone. The bound below is the Archimedean input a Putinar-style argument
consumes, and it degenerates exactly as the floor goes to zero — which is the
proved shadow of the measured quartic degeneration. -/

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

/-- **The floor caps the pairing too**, through the spread bound: the squared
pairing is at most the product of the two leverages, each capped by the floor.
Together with the excess bound this boxes the whole region. -/
theorem atomPairing_sq_le_of_isFlooredSpreadDesign (D : WeightedDesign m 3)
    {spread floor : ℝ} (hspreadNonneg : 0 ≤ spread) (hfloorPos : 0 < floor)
    (hregion : IsFlooredSpreadDesign D spread floor)
    {atomFirst atomSecond : Fin m} (hne : atomFirst ≠ atomSecond) :
    atomPairing D atomFirst atomSecond ^ 2 ≤ (1 / floor) ^ 2 := by
  have hleverageFirst :=
    leverageOf_le_of_hasWeightFloor D hfloorPos hregion.2.2 atomFirst
  have hleverageSecond :=
    leverageOf_le_of_hasWeightFloor D hfloorPos hregion.2.2 atomSecond
  have hleverageFirstNonneg : 0 ≤ leverageOf (D.atom atomFirst) := leverageOf_nonneg _
  have hleverageSecondNonneg : 0 ≤ leverageOf (D.atom atomSecond) := leverageOf_nonneg _
  have hspread := hregion.2.1 atomFirst atomSecond hne
  nlinarith [hspread, hleverageFirst, hleverageSecond, hleverageFirstNonneg,
    hleverageSecondNonneg, hspreadNonneg,
    mul_nonneg hleverageFirstNonneg hleverageSecondNonneg]

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

/-- **The weight product of a distinct triple is at most `1/27`** — three positive
numbers summing to at most one, by arithmetic-geometric mean. This is the
constant that turns a chart margin into a raw margin. -/
theorem weightProduct_le_inv_twentySeven (D : WeightedDesign m 3)
    {atomFirst atomSecond atomThird : Fin m} (hfirstSecond : atomFirst ≠ atomSecond)
    (hfirstThird : atomFirst ≠ atomThird) (hsecondThird : atomSecond ≠ atomThird) :
    D.weight atomFirst * D.weight atomSecond * D.weight atomThird ≤ 1 / 27 := by
  have hsum := weightTripleSum_le_one D hfirstSecond hfirstThird hsecondThird
  have hfirstPos := D.weight_pos atomFirst
  have hsecondPos := D.weight_pos atomSecond
  have hthirdPos := D.weight_pos atomThird
  nlinarith [sq_nonneg (D.weight atomFirst - D.weight atomSecond),
    sq_nonneg (D.weight atomSecond - D.weight atomThird),
    sq_nonneg (D.weight atomFirst - D.weight atomThird),
    mul_pos hfirstPos hsecondPos, mul_pos hsecondPos hthirdPos, mul_pos hfirstPos hthirdPos,
    mul_nonneg hthirdPos.le (sq_nonneg (D.weight atomFirst - D.weight atomSecond)),
    mul_nonneg hfirstPos.le (sq_nonneg (D.weight atomSecond - D.weight atomThird)),
    mul_nonneg hsecondPos.le (sq_nonneg (D.weight atomFirst - D.weight atomThird))]

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

/-- **The chart-side hypothesis.** The certificate an SOS or LP search would
produce, stated on designs so that `Gtz.Quantitative.ProjectionChartLegs` supplies
the translation and no bridge is assumed. See the header for the one thing a
FREE-STANDING chart certificate over all idempotents would additionally need. -/
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

/-! ## The two boundaries of the parameter box

Above weight floor `1/6` the region at size six is empty, so the hypothesis holds
at every margin and says nothing. Below `spread = 4/5`, `floor = 1/6` the region
contains the icosahedral design, whose tie leg is bounded, so no margin above
`51/25` is available. Between them is where a search must live. -/

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
at those extreme parameters and its tie leg is bounded there. This is what makes
the margin a genuinely constrained parameter rather than free notation, and it
calibrates the measured leg margin — about `2.09e-2` at the recommended
`spread = 1/10`, `floor = 1/20` — as roughly a hundredth of the largest margin
that is even conceivable. -/
theorem margin_le_of_spreadFloorCertificateSixThree {spread floor margin : ℚ}
    (hspreadLe : (spread : ℝ) ≤ 4 / 5) (hfloorLe : (floor : ℝ) ≤ 1 / 6)
    (hcertificate : SpreadFloorCertificateSixThree spread floor margin) :
    (margin : ℝ) ≤ 51 / 25 := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, _, htie⟩ :=
    hcertificate icosaDesign
      (isFlooredSpreadDesign_mono hspreadLe hfloorLe icosaDesign_isFlooredSpreadDesign)
  exact htie.trans (icosaDesign_discriminantTie_le hfirstSecond hfirstThird hsecondThird)

end Gtz

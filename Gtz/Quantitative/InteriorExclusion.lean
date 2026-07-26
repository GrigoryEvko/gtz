/-
# Interior exclusions for the A2 stationarity bundle — and the limit of what it can decide

This file extends `Gtz.Quantitative.CriticalQuadric` with the structural exclusions
that the interior residual obligation needs, and with the witness that says how far
that obligation can possibly reach.  Every theorem takes `IsQuadricStationaryData`
as a HYPOTHESIS, exactly as the source file does; the firewall recorded in its
header (a tie is not known to be a critical point, and assuming it is would be
circular) is untouched, and nothing here supplies stationarity data at a design
except the explicit `(4,2)` witness at the end, which is a construction, not a
criticality claim.

## THE HEADLINE — the BUNDLE-ONLY FORMALIZATION is refuted; GTZ is untouched

Read the scope of this precisely, because the overstatement is easy and costly.
What is refuted is one candidate FORMALIZATION of the interior residual
obligation, namely `IsQuadricStationaryData -> value != 0 -> 1 <= value`.  The
obligation itself — "no interior Clarke-critical point of `F` with value below
one" — is NOT refuted, NOT weakened, and NOT decided anywhere in this file, and
neither is `GtzWeighted` at any size.

`exists_isQuadricStationaryData_value_lt_one` exhibits a COMPLETE
`IsQuadricStationaryData` at `(m,k) = (4,2)` with

    value = 2 - sqrt 2 = 0.5857...  <  1 ,

atoms `(sqrt 2, 0)`, `(-1, 1)`, `(1, 1)`, `(0, sqrt 2)`, weights all `1/4`, active
family `{0,1}`, `{0,2}`, `{1,3}`, `{2,3}` with multipliers all `1/4`, and
`Lambda = ((2 - sqrt 2)/2) I`.  All eight fields are discharged in Lean.
[The count "thirty residuals" quoted in earlier prose is EXACT arithmetic done
outside Lean — four Parseval entries, one weight sum, one multiplier sum, four
unit norms, eight eigenvector coordinates, eight atom-stationarity coordinates,
four quadric values — and it is the eight FIELDS, not the thirty residuals, that
the kernel checks.]

Hence `not_forall_one_le_value_of_isQuadricStationaryData`: the implication
"stationarity data with a nonzero value force `1 <= value`" is FALSE, so no
theorem of that shape can ever be proved, here or anywhere.  Every exclusion below
must, and does, carry a structural hypothesis that the witness violates.

The witness is NOT a GTZ counterexample, and the reason is exactly the field the
bundle omits.  `IsQuadricStationaryData` asks that `value` be AN eigenvalue of
each `S_{C_i}`; it does not ask that `value = lambda_min(S_{C_i})`, and it does not
ask that `value = F(D) = max_{|C| = k} lambda_min(S_C)`.  At the witness the two
INACTIVE pairs `{0,3}` and `{1,2}` both have `S_C = 2 I`, so
`dominates_belowOneDesign_orthogonalPair` shows the design satisfies
`GtzWeighted 4 2` with margin — `S_{03} - 1 = 1`, positive definite on the nose.
[`F(D) = 2` exactly, and the four ACTIVE pairs are precisely the MINIMISERS: each
has eigenvalues `2 +- sqrt 2`.  That is EXACT arithmetic over `Q(sqrt 2)` done
outside Lean; what is MECHANIZED is the lower half, `F(D) >= 2`, via
`exists_dominating_belowOneDesign`.]  So the datum is stationary for the max over
the four CHOSEN subsets, which are the ARGMIN family — as far from a critical
point of `F` as a subset family can be.

The missing constraint is named, defined and exploited at the end of this file
rather than left in prose: `IsArgmaxDominated`, `value >= lambda_min(S_C)` for
EVERY `k`-subset.  It IS statable in the repo's existing vocabulary (a unit probe
with small enough Rayleigh quotient — no eigenvalue function, no spectral theory);
what it is not is an EQUATION, which is why no linear-algebra derivation below can
consume it and why it does not enter this lane's Groebner systems.  And
`one_le_value_of_isArgmaxDominated` computes what attaching it is worth: granted
`GtzWeighted m k` it forces `1 <= value`, and contrapositively
`not_gtzWeighted_of_isArgmaxDominated_of_value_lt_one` says a datum satisfying it
below one REFUTES `GtzWeighted m k`.  In other words the argmax-complete interior
obligation is EXACTLY the interior case of GTZ at that size, with the KKT
equations available for free — a genuine convenience, but not a smaller problem.
`Gtz.Quantitative.CriticalQuadric` already discloses the slack in prose and
exercises it at its degenerate `value = 0` witness; the theorem here is that the
slack is fatal to the below-one reading too, at a NONZERO value.

## PROVED here (all unconditional, given the bundle)

* `one_le_leverage_of_isQuadricStationaryData` — every atom of a `value != 0` datum
  has leverage at least one.  Each tight overlap is bounded by Cauchy-Schwarz
  against the unit tight direction, and (C1) sums those bounds to `1 <= |g_c|^2`.
  DISCLOSURE: this is NOT `Gtz.AllHeavy` (`Gtz.Reduction.Reductions`), which is
  STRICT (`1 < leverageOf`).  Strictness would need the multiplier to have rank at
  least two AND no atom parallel to a tight direction, and is not proved.
* `weight_mul_value_le_one_of_isQuadricStationaryData` — `t_c * value <= 1` at every
  atom, the restricted coverage sum being at most the unrestricted (C1) sum; hence
  `value_le_size_of_isQuadricStationaryData`, `value <= m`.
  DISCLOSURE, so these two are not mistaken for below-one exclusions: BOTH are
  VACUOUS in the regime this file is about.  Below one, `t_c * value <= 1` follows
  from `t_c <= 1` and `value < 1` with no stationarity data at all, and `value <= m`
  follows from `value < 1 <= m`.  Their content is entirely at `value >= 1`, where
  the share bound reads `t_c <= 1/value` and is sharp — attained exactly when the
  tight directions are independent (E2 below).  Neither is used downstream, and
  `one_le_leverage` is the only one of the three carrying below-one content.
* **E1**, `value_eq_rank_of_rankOneMultiplier` — a RANK-ONE multiplier forces
  `value = k`, at every rank and every size.  The route is not the informal one:
  `Lambda = scale * u u^T` gives `<u, g_c>^2 = 1` at every atom, but `u` is not a
  tight direction by assumption, so one first proves it IS one.  The barycentre
  identity `Lambda = value * sum_i lambda_i u_i u_i^T` plus the trace and (C1)
  force `sum_i lambda_i <u_i, u>^2 = 1 = sum_i lambda_i`, and Cauchy-Schwarz makes
  every term of the difference nonnegative, so every positively-weighted `u_i` has
  `<u_i, u>^2 = 1` and therefore `u_i = <u_i, u> u` — the equality case, obtained
  by squaring out `u_i - <u_i,u> u` rather than by invoking a Cauchy-Schwarz
  equality lemma.  Then `value = u_i^T S_{C_i} u_i = k`.
  `not_isQuadricStationaryData_of_rankOneMultiplier_of_value_lt_one` is the
  below-one reading.  DISCLOSURE: the hypothesis is the EXPLICIT rank-one form
  `multiplierMatrix = scale • atomMatrix unitDir`.  Positive semidefiniteness and
  `trace Lambda = value`, both shipped in `CriticalQuadric`, make that the general
  shape of a rank-at-most-one multiplier, but the passage from `Matrix.rank <= 1`
  to that form is a spectral fact and is NOT mechanized here.
* **E2, in the corrected form**, `value_eq_size_of_independentTightSupport` —
  linear independence of the tight directions carried by positive multipliers
  forces `t_c * value = 1` at EVERY atom, hence `value = m` and every weight
  `1/m`.  No partition hypothesis is needed, and the exclusion
  `not_isQuadricStationaryData_of_independentTightSupport_of_value_lt_one` follows
  from `m >= 1`.  Read as a fact about the below-one region:
  `not_hasIndependentTightSupport_of_value_lt_one` — below one the tight
  directions are always DEPENDENT.
* **E3 counting**, `size_le_rank_mul_card_activeSubsetImage` — `m <= k * p` where
  `p` is the number of DISTINCT active subsets.  This is sharper than the shipped
  `size_le_rank_mul_card_activeSet_of_isQuadricStationaryData`, which counts active
  INDICES; the difference is exactly the multiplicity packaging, where many indices
  carry one subset.  Consequences: `two_le_card_activeSubsetImage_of_rank_lt_size`
  (`p >= 2` whenever `k < m`, no `value < 1` needed) and
  `disjoint_union_of_card_activeSubsetImage_eq_two` (at `m = k + k`, `p = 2` forces
  the two subsets to be disjoint and to partition the atoms).
* **E3 at (6,3)**, `three_le_card_activeSubsetImage_or_dependentPartition_sixThree`
  — at `value != 0` and `value < 1` the active family either has at least THREE
  distinct triples, or is a two-block PARTITION of the six atoms whose tight
  directions are linearly dependent.
* **The saturated-atom exclusion**, `one_le_value_of_saturatedAtom` — if some atom
  lies in EVERY active subset then its coverage sum IS the unrestricted (C1) sum,
  so `t_c * value = 1` and `value = 1/t_c >= 1`.  Contrapositive
  `exists_activeSubset_not_mem_of_value_lt_one`.  Unlike E1 and E2 the hypothesis is
  purely COMBINATORIAL — it is read off the active family — so it filters patterns
  one by one.  At `(6,3)` this is the step that takes the covering `p >= 3` orbit
  count from 2101 to 2078 (counts computed outside Lean, twice, by canonical forms
  and by Burnside; not asserted here).
* **The block-mass identity**, `activeWeight_blockMass_eq_weight_blockMass` — if
  every active subset either EQUALS a chosen nonempty block or is disjoint from it,
  the Clarke multiplier mass on the block equals the block's Parseval weight mass.
  A necessary condition on the PARTITION branch below; NOT a proof of it.
* **The argmax field and its price**, `IsArgmaxDominated`,
  `one_le_value_of_isArgmaxDominated`,
  `not_gtzWeighted_of_isArgmaxDominated_of_value_lt_one`,
  `not_isArgmaxDominated_belowOneDesign` — see the headline.  The obligation with
  the argmax attached is the interior case of GTZ itself, not a lemma in front of it.

## Corrections to the three hand-derived exclusions this file was asked to mechanize

* E1 stands, and is proved.  It needs the barycentre identity as an input; without
  it the rank-one hypothesis gives only `value <= k`.
* **E2's stated derivation is REFUTED.**  The claim was that independence forces
  `<u_C, g_c> = 0`, contradicting coverage.  It does not: the coefficient of `u_j`
  in the independent combination is `lambda_j <u_j, g_c> (1 - t_c * value)`, and
  the factor `(1 - t_c * value)` CAN vanish — that branch is exactly what happens.
  The correct conclusion is stronger and needs no partition: every weight is
  `1/value`, so `value = m`.  The mechanized statement is the corrected one.
* **E3's stated route is INCOMPLETE, and only half of it is mechanized.**  "Two
  triples cover six atoms only if disjoint, which is a partition, killed by E2" is
  not available: corrected E2 needs INDEPENDENT tight directions, and a two-block
  partition at rank three need not have them.  What is proved here is the honest
  dichotomy above.  Killing the partition branch is the OPEN leaf; see below.

## The OPEN leaf, named

**PARTITION-BELOW-ONE.**  No stationarity datum whose distinct active subsets
partition the atoms has `0 < value < 1`.  NOT PROVED, and NOT assumed anywhere.

A route was reported for it — "`M_q = M P_q` with `P_q = sum_{c in B_q} t_c g_c g_c^T`,
hence `M` and `P_q` commute, hence `value >= rank Lambda`" — and it did not survive
checking.  Contracting atom stationarity through the barycentre identity gives, for
`M := Lambda / value` and `M_q` the restricted sum,

    M_q g_c = (t_c * value) * M g_c    for `c` in the block `B_q`, and only there.

That determines `M_q` on `B_q`; it says nothing about `M_q g_c` for `c` outside
`B_q` once there are three or more blocks, and even with two blocks it yields
`M_0 = M A` with `A = sum_{c in B_0} t_c theta_c g_c g_c^T + sum_{c in B_1} t_c (1 - theta_c)
g_c g_c^T`, `theta_c = t_c * value` — not `M P_0`, which would additionally need
`theta = 1` on `B_0` and `M_0` to annihilate `B_1`.  So `value >= rank Lambda` is
not established, and it is not used.  [The corrected two-block identity is EXACT
arithmetic done outside Lean and is NOT mechanized either; it is recorded only to
say why the reported route was not taken.]

What IS proved about the branch, and is the only progress on it here, is
`activeWeight_blockMass_eq_weight_blockMass`: each block carries Clarke multiplier
mass exactly equal to its Parseval weight mass.  Summing that over the blocks of a
partition just returns `1 = 1`, so it does not close the leaf on its own; it is a
constraint the next attempt starts from rather than re-derives.

## Multiplicity — the simple-eigenvalue question, answered

The bundle does NOT assume simple tight eigenvalues, and nothing here does either.
`IsQuadricStationaryData` indexes the active family by an arbitrary `activeIndex`
with a MAP `activeSubset : activeIndex -> Finset (Fin m)`, so several indices may
carry the same `k`-subset.  A general Overton-Womersley dual block `Omega_C` —
positive semidefinite, unit trace, range inside the tight eigenspace — decomposes
spectrally as `sum_j w_j u_j u_j^T` with `w_j >= 0`, `sum_j w_j = 1` and every `u_j`
a unit eigenvector of `S_C` at `value`; taking the index set to be the pairs
`(C, j)` with multipliers `lambda_C w_j` reproduces every field of the bundle
verbatim, and the multipliers still sum to one.  So the rank-one `tightDir` is
without loss of generality.  [That reduction is a spectral argument stated here in
prose; it is CITED, not mechanized.  What IS mechanized is that the theorems below
never assume `activeSubset` injective —
`size_le_rank_mul_card_activeSubsetImage` counts the image precisely because the map
need not be injective, and `Gtz.value_eq_rank_of_constant_activeSubset` in the source
file is already the multiplicity-aware form of (C3).]

## What this file does NOT do

* It does not decide the `(6,3)` interior.  The residue after the exclusions above
  is the `p >= 3` overlapping families, and the file header of
  `Gtz.Quantitative.CriticalQuadric` states the honest size of that residue.
* It carries no external-tool verdict.  No Groebner emptiness certificate is
  imported, asserted, or relied on; the external systems produced for this lane
  are all positive-dimensional before elimination and none of them came with a
  cofactor certificate of a size `ring` could check.
* It proves nothing about `F(D)` or about `GtzWeighted` at any size, except the
  single positive statement `exists_dominating_belowOneDesign`, which is there to
  keep the witness honest.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.Reduction.LiftingLemma
import Gtz.Quantitative.CriticalQuadric

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## Consequences of the bundle at an arbitrary size -/

section StationarityConsequences

variable {m k : ℕ} {activeIndex : Type*}
variable {D : WeightedDesign m k} {value : ℝ}
  {multiplierMatrix : Matrix (Fin k) (Fin k) ℝ} {activeSet : Finset activeIndex}
  {activeSubset : activeIndex → Finset (Fin m)} {activeWeight : activeIndex → ℝ}
  {tightDir : activeIndex → (Fin k → ℝ)}

/-- **The multiplier's quadratic form at an ARBITRARY probe.**  The determination
`Lambda = value * sum_C lambda_C u_C u_C^T` read as a form.  The shipped
`tightOverlap_sum_eq_one_of_isQuadricStationaryData` is this identity at an ATOM,
combined with the quadric law; the probe-level statement is what the rank-one
argument below needs, since it must evaluate the form at a tight direction rather
than at an atom. -/
theorem multiplierForm_eq_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (probe : Fin k → ℝ) :
    probe ⬝ᵥ (multiplierMatrix *ᵥ probe)
      = value * ∑ activeLabel ∈ activeSet,
          activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probe) ^ 2 := by
  rw [multiplierMatrix_eq_of_isQuadricStationaryData hdata, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun activeLabel _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix, vecMulVec_mulVec_eq,
    dotProduct_smul, smul_eq_mul, dotProduct_comm probe (tightDir activeLabel)]
  ring

/-- **Every atom is heavy.**  (C1) says the tight overlaps at an atom carry total
multiplier mass one; each overlap is at most the leverage, by Cauchy-Schwarz
against a unit tight direction; the multipliers sum to one; so `1 <= |g_c|^2`.

This is WEAKER than `Gtz.AllHeavy`, which demands `1 < leverageOf`.  The strict
form would need the equality case of Cauchy-Schwarz to be excluded at every
positively-weighted index simultaneously, i.e. no tight direction parallel to the
atom, and that is not proved. -/
theorem one_le_leverage_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (atomLabel : Fin m) :
    1 ≤ leverageOf (D.atom atomLabel) := by
  have hone := tightOverlap_sum_eq_one_of_isQuadricStationaryData hdata hvalueNe atomLabel
  have hbound : ∑ activeLabel ∈ activeSet,
        activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ D.atom atomLabel) ^ 2
      ≤ ∑ activeLabel ∈ activeSet,
        activeWeight activeLabel * leverageOf (D.atom atomLabel) := by
    refine Finset.sum_le_sum fun activeLabel hactive => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hdata.activeWeight_nonneg activeLabel hactive)
    have hcauchy := dotProduct_sq_le_mul (tightDir activeLabel) (D.atom atomLabel)
    rw [hdata.tightDir_unit activeLabel hactive, one_mul] at hcauchy
    rw [leverageOf, ← dotProduct_self_eq_sum_sq]
    exact hcauchy
  rw [hone, ← Finset.sum_mul, hdata.activeWeight_sum_one, one_mul] at hbound
  exact hbound

/-- **The share bound.**  The coverage sum is the (C1) sum restricted to the active
subsets containing the atom, and all terms are nonnegative, so
`t_c * value <= 1` at every atom. -/
theorem weight_mul_value_le_one_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (atomLabel : Fin m) :
    D.weight atomLabel * value ≤ 1 := by
  have hcoverage := coverageLaw_of_isQuadricStationaryData hdata atomLabel
  have hone := tightOverlap_sum_eq_one_of_isQuadricStationaryData hdata hvalueNe atomLabel
  have hrestricted : ∑ activeLabel ∈ activeSet,
      (if atomLabel ∈ activeSubset activeLabel
        then activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ D.atom atomLabel) ^ 2 else 0)
      ≤ ∑ activeLabel ∈ activeSet,
        activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ D.atom atomLabel) ^ 2 := by
    refine Finset.sum_le_sum fun activeLabel hactive => ?_
    by_cases hmem : atomLabel ∈ activeSubset activeLabel
    · rw [if_pos hmem]
    · rw [if_neg hmem]
      exact mul_nonneg (hdata.activeWeight_nonneg activeLabel hactive) (sq_nonneg _)
  rw [hcoverage, hone] at hrestricted
  exact hrestricted

/-- **The value is at most the size.**  Sum the share bound against `sum_c t_c = 1`.
The transversal exclusion below shows the bound is ATTAINED exactly when the tight
directions are independent. -/
theorem value_le_size_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) :
    value ≤ (m : ℝ) := by
  have hsum : ∑ atomLabel : Fin m, D.weight atomLabel * value ≤ ∑ _c : Fin m, (1 : ℝ) :=
    Finset.sum_le_sum fun atomLabel _ =>
      weight_mul_value_le_one_of_isQuadricStationaryData hdata hvalueNe atomLabel
  rw [← Finset.sum_mul, D.weight_sum_one, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  exact hsum

/-! ## E1 — a rank-one multiplier forces the value to be the rank -/

/-- The scale of a rank-one multiplier is the value: its trace is `scale` (the
direction being a unit vector), and the trace is `value`. -/
theorem rankOneScale_eq_value_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) {rankOneDir : Fin k → ℝ} {rankOneScale : ℝ}
    (hunitDir : rankOneDir ⬝ᵥ rankOneDir = 1)
    (hrankOne : multiplierMatrix = rankOneScale • atomMatrix rankOneDir) :
    rankOneScale = value := by
  have htrace := trace_multiplierMatrix_of_isQuadricStationaryData hdata
  rw [hrankOne, Matrix.trace_smul, trace_atomMatrix, smul_eq_mul, leverageOf,
    ← dotProduct_self_eq_sum_sq, hunitDir, mul_one] at htrace
  exact htrace

/-- The quadratic form of a scaled rank-one projector. -/
theorem rankOneForm_eq (rankOneDir : Fin k → ℝ) (rankOneScale : ℝ) (probe : Fin k → ℝ) :
    probe ⬝ᵥ ((rankOneScale • atomMatrix rankOneDir) *ᵥ probe)
      = rankOneScale * (rankOneDir ⬝ᵥ probe) ^ 2 := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix, vecMulVec_mulVec_eq,
    dotProduct_smul, smul_eq_mul, dotProduct_comm probe rankOneDir]
  ring

/-- With a rank-one multiplier the tight overlaps collapse onto the rank-one
direction at EVERY probe: the barycentre form and the rank-one form agree, and
`value != 0` cancels. -/
theorem tightOverlap_probe_eq_of_rankOneMultiplier
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0)
    {rankOneDir : Fin k → ℝ} {rankOneScale : ℝ}
    (hunitDir : rankOneDir ⬝ᵥ rankOneDir = 1)
    (hrankOne : multiplierMatrix = rankOneScale • atomMatrix rankOneDir)
    (probe : Fin k → ℝ) :
    ∑ activeLabel ∈ activeSet, activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probe) ^ 2
      = (rankOneDir ⬝ᵥ probe) ^ 2 := by
  have hscale := rankOneScale_eq_value_of_isQuadricStationaryData hdata hunitDir hrankOne
  have hleft := multiplierForm_eq_of_isQuadricStationaryData hdata probe
  rw [hrankOne, rankOneForm_eq, hscale] at hleft
  exact (mul_left_cancel₀ hvalueNe hleft).symm

/-- **A rank-one multiplier has a tight direction on its own line.**  Evaluating the
previous identity at the rank-one direction gives
`sum_i lambda_i <u_i, u>^2 = 1 = sum_i lambda_i`, and every term of the difference
is nonnegative by Cauchy-Schwarz, so it vanishes term by term; at a positively
weighted index the overlap is `+-1`, and squaring out `u_i - <u_i,u> u` shows the
vector itself is a multiple of `u`. -/
theorem exists_tightDir_eq_smul_of_rankOneMultiplier
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0)
    {rankOneDir : Fin k → ℝ} {rankOneScale : ℝ}
    (hunitDir : rankOneDir ⬝ᵥ rankOneDir = 1)
    (hrankOne : multiplierMatrix = rankOneScale • atomMatrix rankOneDir) :
    ∃ activeLabel ∈ activeSet, ∃ overlapScalar : ℝ,
      tightDir activeLabel = overlapScalar • rankOneDir := by
  have hmass := tightOverlap_probe_eq_of_rankOneMultiplier hdata hvalueNe hunitDir hrankOne
    rankOneDir
  rw [hunitDir, one_pow] at hmass
  have hdefect : ∑ activeLabel ∈ activeSet,
      activeWeight activeLabel * (1 - (tightDir activeLabel ⬝ᵥ rankOneDir) ^ 2) = 0 := by
    have hsplit : ∑ activeLabel ∈ activeSet,
          activeWeight activeLabel * (1 - (tightDir activeLabel ⬝ᵥ rankOneDir) ^ 2)
        = (∑ activeLabel ∈ activeSet, activeWeight activeLabel)
          - ∑ activeLabel ∈ activeSet,
              activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ rankOneDir) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun activeLabel _ => by ring
    rw [hsplit, hdata.activeWeight_sum_one, hmass]
    norm_num
  have hnonneg : ∀ activeLabel ∈ activeSet,
      0 ≤ activeWeight activeLabel * (1 - (tightDir activeLabel ⬝ᵥ rankOneDir) ^ 2) := by
    intro activeLabel hactive
    refine mul_nonneg (hdata.activeWeight_nonneg activeLabel hactive) ?_
    have hcauchy := dotProduct_sq_le_mul (tightDir activeLabel) rankOneDir
    rw [hdata.tightDir_unit activeLabel hactive, hunitDir, mul_one] at hcauchy
    linarith
  obtain ⟨positiveLabel, hpositiveMem, hpositive⟩ :=
    exists_pos_activeWeight_of_isQuadricStationaryData hdata
  refine ⟨positiveLabel, hpositiveMem, tightDir positiveLabel ⬝ᵥ rankOneDir, ?_⟩
  have hterm : activeWeight positiveLabel
      * (1 - (tightDir positiveLabel ⬝ᵥ rankOneDir) ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hdefect positiveLabel hpositiveMem
  have hsquare : (tightDir positiveLabel ⬝ᵥ rankOneDir) ^ 2 = 1 := by
    rcases mul_eq_zero.mp hterm with hzero | hgap
    · exact absurd hzero (ne_of_gt hpositive)
    · linarith
  have hdiffZero : (tightDir positiveLabel - (tightDir positiveLabel ⬝ᵥ rankOneDir) • rankOneDir)
      ⬝ᵥ (tightDir positiveLabel - (tightDir positiveLabel ⬝ᵥ rankOneDir) • rankOneDir) = 0 := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hdata.tightDir_unit positiveLabel hpositiveMem, hunitDir,
      dotProduct_comm rankOneDir (tightDir positiveLabel)]
    nlinarith [hsquare]
  have hdiff := eq_zero_of_dotProduct_self_eq_zero hdiffZero
  exact sub_eq_zero.mp hdiff

/-- **E1, THE RANK-ONE EXCLUSION, in its sharp form.**  If the multiplier is a
scalar multiple of a rank-one projector then the value is exactly the rank:

    `Lambda = scale * u u^T`,  `|u| = 1`,  `value != 0`   ==>   `value = k` .

Rank-general and size-general.  With the tight direction on the line of `u`
(previous theorem) and `<u, g_c>^2 = 1` at every atom (the quadric law read
through the rank-one form), the Rayleigh quotient of the active subset is a sum of
`k` ones. -/
theorem value_eq_rank_of_rankOneMultiplier
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0)
    {rankOneDir : Fin k → ℝ} {rankOneScale : ℝ}
    (hunitDir : rankOneDir ⬝ᵥ rankOneDir = 1)
    (hrankOne : multiplierMatrix = rankOneScale • atomMatrix rankOneDir) :
    value = (k : ℝ) := by
  obtain ⟨activeLabel, hmem, overlapScalar, hparallel⟩ :=
    exists_tightDir_eq_smul_of_rankOneMultiplier hdata hvalueNe hunitDir hrankOne
  have hscale := rankOneScale_eq_value_of_isQuadricStationaryData hdata hunitDir hrankOne
  have hatomOverlap : ∀ atomLabel : Fin m, (D.atom atomLabel ⬝ᵥ rankOneDir) ^ 2 = 1 := by
    intro atomLabel
    have hquadric := quadricLaw_of_isQuadricStationaryData hdata atomLabel
    rw [hrankOne, rankOneForm_eq, hscale, dotProduct_comm rankOneDir (D.atom atomLabel)] at hquadric
    refine mul_left_cancel₀ hvalueNe ?_
    rw [mul_one]
    exact hquadric
  have hsquare : overlapScalar ^ 2 = 1 := by
    have hunit := hdata.tightDir_unit activeLabel hmem
    rw [hparallel, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hunitDir] at hunit
    nlinarith [hunit]
  have hdirForm : rankOneDir
      ⬝ᵥ (subsetSum D (activeSubset activeLabel) *ᵥ rankOneDir) = (k : ℝ) := by
    rw [subsetSum_form_eq_sum_sq,
      Finset.sum_congr rfl (fun atomLabel _ => hatomOverlap atomLabel :
        ∀ atomLabel ∈ activeSubset activeLabel, (D.atom atomLabel ⬝ᵥ rankOneDir) ^ 2 = 1),
      Finset.sum_const, hdata.activeSubset_card activeLabel hmem, nsmul_eq_mul, mul_one]
  have hrayleigh : tightDir activeLabel
      ⬝ᵥ (subsetSum D (activeSubset activeLabel) *ᵥ tightDir activeLabel) = value := by
    rw [hdata.tightDir_isEigenvector activeLabel hmem, dotProduct_smul, smul_eq_mul,
      hdata.tightDir_unit activeLabel hmem, mul_one]
  rw [hparallel, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    hdirForm] at hrayleigh
  nlinarith [hrayleigh, hsquare]

/-- **E1 below one.**  No stationarity datum with a nonzero value strictly below one
has a rank-one multiplier, since `value = k` and a nonzero value forces `k >= 1`. -/
theorem not_isQuadricStationaryData_of_rankOneMultiplier_of_value_lt_one
    (hvalueNe : value ≠ 0) (hbelowOne : value < 1)
    {rankOneDir : Fin k → ℝ} {rankOneScale : ℝ}
    (hunitDir : rankOneDir ⬝ᵥ rankOneDir = 1)
    (hrankOne : multiplierMatrix = rankOneScale • atomMatrix rankOneDir) :
    ¬ IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir := by
  intro hdata
  have hrank := value_eq_rank_of_rankOneMultiplier hdata hvalueNe hunitDir hrankOne
  rw [hrank] at hvalueNe hbelowOne
  have hrankNe : k ≠ 0 := fun hzero => hvalueNe (by rw [hzero]; norm_num)
  have hcast : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hrankNe
  exact absurd hbelowOne (not_lt.mpr hcast)

/-! ## E2 — independent tight directions force the value to be the size -/

/-- Atom stationarity's right-hand side resolved through the barycentre identity:
`t_c * Lambda g_c` is itself a combination of the tight directions. -/
theorem weightedMultiplierImage_eq_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (atomLabel : Fin m) :
    D.weight atomLabel • (multiplierMatrix *ᵥ D.atom atomLabel)
      = ∑ activeLabel ∈ activeSet,
          (D.weight atomLabel * value * activeWeight activeLabel
            * (tightDir activeLabel ⬝ᵥ D.atom atomLabel)) • tightDir activeLabel := by
  rw [multiplierMatrix_eq_of_isQuadricStationaryData hdata, Matrix.smul_mulVec,
    Matrix.sum_mulVec, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun activeLabel _ => ?_
  rw [Matrix.smul_mulVec, atomMatrix, vecMulVec_mulVec_eq]
  simp only [smul_smul]
  congr 1
  ring

/-- **The vanishing combination.**  Both sides of atom stationarity are combinations
of the tight directions, so their difference is a vanishing combination whose
`i`-th coefficient is `lambda_i` times

    `(indicator of c in C_i) * <u_i, g_c>  -  t_c * value * <u_i, g_c>` .

This is the equation the independence hypothesis consumes. -/
theorem tightCombination_eq_zero_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (atomLabel : Fin m) :
    ∑ activeLabel ∈ activeSet,
        (activeWeight activeLabel
          * ((if atomLabel ∈ activeSubset activeLabel
              then tightDir activeLabel ⬝ᵥ D.atom atomLabel else 0)
            - D.weight atomLabel * value * (tightDir activeLabel ⬝ᵥ D.atom atomLabel)))
        • tightDir activeLabel
      = 0 := by
  have hatom := hdata.atomStationarity atomLabel
  rw [weightedMultiplierImage_eq_of_isQuadricStationaryData hdata atomLabel] at hatom
  rw [← sub_eq_zero] at hatom
  rw [← hatom, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun activeLabel _ => ?_
  by_cases hmem : atomLabel ∈ activeSubset activeLabel
  · simp only [hmem, if_true]
    rw [← sub_smul]
    congr 1
    ring
  · simp only [hmem, if_false]
    rw [← sub_smul]
    congr 1
    ring

/-- **The tight directions carried by positive multipliers are independent.**

Stated so that the zero-weight indices cost nothing: a combination whose
coefficients are `activeWeight i * coefficient i` can only vanish if each of those
products vanishes.  Ordinary linear independence of the whole active family implies
this, and so does linear independence of the positively-weighted subfamily alone —
the terms with `activeWeight i = 0` drop out of both sides.  Using the product form
rather than plain independence keeps the exclusion below as sharp as the
mathematics allows. -/
def HasIndependentTightSupport {rank : ℕ} {index : Type*} (activeSet : Finset index)
    (activeWeight : index → ℝ) (tightDir : index → (Fin rank → ℝ)) : Prop :=
  ∀ coefficient : index → ℝ,
    (∑ activeLabel ∈ activeSet,
        (activeWeight activeLabel * coefficient activeLabel) • tightDir activeLabel = 0) →
      ∀ activeLabel ∈ activeSet, activeWeight activeLabel * coefficient activeLabel = 0

/-- **Every share is one.**  Independence kills each coefficient of the vanishing
combination; coverage supplies, at each atom, an index whose subset contains the
atom and whose multiplier and overlap are both nonzero; for that index the
surviving factor is `1 - t_c * value`. -/
theorem weight_mul_value_eq_one_of_independentTightSupport
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0)
    (hindependent : HasIndependentTightSupport activeSet activeWeight tightDir)
    (atomLabel : Fin m) :
    D.weight atomLabel * value = 1 := by
  have hcoverage := coverageLaw_of_isQuadricStationaryData hdata atomLabel
  have hcoverageNe : ∑ activeLabel ∈ activeSet,
      (if atomLabel ∈ activeSubset activeLabel
        then activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ D.atom atomLabel) ^ 2
        else 0) ≠ 0 := by
    rw [hcoverage]
    exact mul_ne_zero (ne_of_gt (D.weight_pos atomLabel)) hvalueNe
  obtain ⟨witnessLabel, hwitnessMem, hwitnessNe⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hcoverageNe
  have hwitnessMemSubset : atomLabel ∈ activeSubset witnessLabel := by
    by_contra hout
    rw [if_neg hout] at hwitnessNe
    exact hwitnessNe rfl
  rw [if_pos hwitnessMemSubset] at hwitnessNe
  have hweightNe : activeWeight witnessLabel ≠ 0 := fun hzero => hwitnessNe (by rw [hzero]; ring)
  have hpairingNe : tightDir witnessLabel ⬝ᵥ D.atom atomLabel ≠ 0 := fun hzero =>
    hwitnessNe (by rw [hzero]; ring)
  have hvanish := hindependent
    (fun activeLabel =>
      (if atomLabel ∈ activeSubset activeLabel
        then tightDir activeLabel ⬝ᵥ D.atom atomLabel else 0)
      - D.weight atomLabel * value * (tightDir activeLabel ⬝ᵥ D.atom atomLabel))
    (tightCombination_eq_zero_of_isQuadricStationaryData hdata atomLabel)
    witnessLabel hwitnessMem
  rw [if_pos hwitnessMemSubset] at hvanish
  have hfactored : activeWeight witnessLabel * (tightDir witnessLabel ⬝ᵥ D.atom atomLabel)
      * (1 - D.weight atomLabel * value) = 0 := by
    rw [← hvanish]; ring
  rcases mul_eq_zero.mp hfactored with hleft | hright
  · rcases mul_eq_zero.mp hleft with hweightZero | hpairingZero
    · exact absurd hweightZero hweightNe
    · exact absurd hpairingZero hpairingNe
  · linarith

/-- **E2, THE TRANSVERSAL EXCLUSION, in its corrected form.**  Independent tight
support forces

    `value = m`   and   every weight equal to `1/m` .

No partition hypothesis is involved: the shares are all one, and they sum to
`value` against `sum_c t_c = 1`.  This CORRECTS the derivation the file was asked
to mechanize, which concluded `<u_C, g_c> = 0` from independence; that step is
false, because the factor `(1 - t_c * value)` may vanish instead — and in fact
always does. -/
theorem value_eq_size_of_independentTightSupport
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0)
    (hindependent : HasIndependentTightSupport activeSet activeWeight tightDir) :
    value = (m : ℝ) := by
  have hunitProduct : ∀ atomLabel : Fin m, D.weight atomLabel * value = 1 := fun atomLabel =>
    weight_mul_value_eq_one_of_independentTightSupport hdata hvalueNe hindependent atomLabel
  have hsum : ∑ atomLabel : Fin m, D.weight atomLabel * value = (m : ℝ) := by
    rw [Finset.sum_congr rfl (fun atomLabel _ => hunitProduct atomLabel :
      ∀ atomLabel ∈ (Finset.univ : Finset (Fin m)), D.weight atomLabel * value = 1),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [← Finset.sum_mul, D.weight_sum_one, one_mul] at hsum
  exact hsum

/-- **E2 below one.**  There is no stationarity datum with independent tight support
and a nonzero value strictly below one: the value would be the size, and a design
has at least one atom. -/
theorem not_isQuadricStationaryData_of_independentTightSupport_of_value_lt_one
    (hvalueNe : value ≠ 0) (hbelowOne : value < 1)
    (hindependent : HasIndependentTightSupport activeSet activeWeight tightDir) :
    ¬ IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir := by
  intro hdata
  have hsize := value_eq_size_of_independentTightSupport hdata hvalueNe hindependent
  have hsizeNe : m ≠ 0 := by
    intro hzero
    rw [hzero] at hsize
    exact hvalueNe (by simpa using hsize)
  have hsizeOne : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hsizeNe
  rw [hsize] at hbelowOne
  exact absurd hbelowOne (not_lt.mpr hsizeOne)

/-- **Below one the tight directions are DEPENDENT.**  The contrapositive reading of
the transversal exclusion, and the shape the `(6,3)` residue consumes. -/
theorem not_hasIndependentTightSupport_of_value_lt_one
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (hbelowOne : value < 1) :
    ¬ HasIndependentTightSupport activeSet activeWeight tightDir := fun hindependent =>
  not_isQuadricStationaryData_of_independentTightSupport_of_value_lt_one hvalueNe hbelowOne
    hindependent hdata

/-! ## E3 — counting the DISTINCT active subsets -/

/-- Every subset the active family attains has exactly `k` atoms. -/
theorem card_eq_rank_of_mem_activeSubsetImage
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) {chosenSubset : Finset (Fin m)}
    (hmem : chosenSubset ∈ activeSet.image activeSubset) :
    chosenSubset.card = k := by
  obtain ⟨activeLabel, hactive, hchosen⟩ := Finset.mem_image.mp hmem
  rw [← hchosen]
  exact hdata.activeSubset_card activeLabel hactive

/-- **The size is bounded by rank times the number of DISTINCT active subsets.**

Sharper than the shipped `size_le_rank_mul_card_activeSet_of_isQuadricStationaryData`,
which counts active INDICES: coverage only ever uses the subsets, and several
indices may carry the same one.  The gap between the two counts is exactly the
multiplicity packaging, so it is this version that constrains a pattern. -/
theorem size_le_rank_mul_card_activeSubsetImage
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) :
    m ≤ k * (activeSet.image activeSubset).card := by
  have hcovered : (Finset.univ : Finset (Fin m))
      ⊆ (activeSet.image activeSubset).biUnion (fun chosenSubset => chosenSubset) := by
    intro atomLabel _
    obtain ⟨activeLabel, hactive, hin⟩ :=
      exists_mem_activeSubset_of_isQuadricStationaryData hdata hvalueNe atomLabel
    exact Finset.mem_biUnion.mpr
      ⟨activeSubset activeLabel, Finset.mem_image_of_mem _ hactive, hin⟩
  have hcardUniv := Finset.card_le_card hcovered
  have hcardBound : ((activeSet.image activeSubset).biUnion
      (fun chosenSubset => chosenSubset)).card
      ≤ ∑ chosenSubset ∈ activeSet.image activeSubset, chosenSubset.card :=
    Finset.card_biUnion_le
  have hcardConst : ∑ chosenSubset ∈ activeSet.image activeSubset, chosenSubset.card
      = (activeSet.image activeSubset).card * k := by
    rw [Finset.sum_congr rfl (fun chosenSubset hchosen =>
      card_eq_rank_of_mem_activeSubsetImage hdata hchosen), Finset.sum_const, smul_eq_mul]
  rw [Finset.card_univ, Fintype.card_fin] at hcardUniv
  calc m ≤ ((activeSet.image activeSubset).biUnion (fun chosenSubset => chosenSubset)).card :=
        hcardUniv
    _ ≤ ∑ chosenSubset ∈ activeSet.image activeSubset, chosenSubset.card := hcardBound
    _ = (activeSet.image activeSubset).card * k := hcardConst
    _ = k * (activeSet.image activeSubset).card := Nat.mul_comm _ _

/-- **At least two distinct active subsets whenever the rank is below the size.**
One subset covers `k < m` atoms, and coverage needs all of them.  No hypothesis on
the value beyond `value != 0` — in particular this is not a below-one statement. -/
theorem two_le_card_activeSubsetImage_of_rank_lt_size
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (hrankLt : k < m) :
    2 ≤ (activeSet.image activeSubset).card := by
  by_contra hsmall
  have hcardLe : (activeSet.image activeSubset).card ≤ 1 := by omega
  have hbound := size_le_rank_mul_card_activeSubsetImage hdata hvalueNe
  have hshrunk : k * (activeSet.image activeSubset).card ≤ k * 1 :=
    Nat.mul_le_mul_left k hcardLe
  omega

/-- **Exactly two distinct active subsets at `m = k + k` is a PARTITION.**  Coverage
puts every atom in one of the two, so their union is everything; each has `k`
atoms; inclusion-exclusion then forces the intersection to be empty. -/
theorem disjoint_union_of_card_activeSubsetImage_eq_two
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (hsize : m = k + k)
    {firstSubset secondSubset : Finset (Fin m)}
    (himage : activeSet.image activeSubset = {firstSubset, secondSubset}) :
    Disjoint firstSubset secondSubset ∧ firstSubset ∪ secondSubset = Finset.univ := by
  have hfirstCard : firstSubset.card = k :=
    card_eq_rank_of_mem_activeSubsetImage hdata (by rw [himage]; exact Finset.mem_insert_self _ _)
  have hsecondCard : secondSubset.card = k :=
    card_eq_rank_of_mem_activeSubsetImage hdata
      (by rw [himage]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hcovered : (Finset.univ : Finset (Fin m)) ⊆ firstSubset ∪ secondSubset := by
    intro atomLabel _
    obtain ⟨activeLabel, hactive, hin⟩ :=
      exists_mem_activeSubset_of_isQuadricStationaryData hdata hvalueNe atomLabel
    have hmemImage : activeSubset activeLabel ∈ ({firstSubset, secondSubset} :
        Finset (Finset (Fin m))) := by
      rw [← himage]; exact Finset.mem_image_of_mem _ hactive
    rcases Finset.mem_insert.mp hmemImage with hfirst | hsecond
    · exact Finset.mem_union_left _ (hfirst ▸ hin)
    · exact Finset.mem_union_right _ ((Finset.mem_singleton.mp hsecond) ▸ hin)
  have hunion : firstSubset ∪ secondSubset = Finset.univ :=
    Finset.Subset.antisymm (Finset.subset_univ _) hcovered
  have hunionCard : (firstSubset ∪ secondSubset).card = m := by
    rw [hunion, Finset.card_univ, Fintype.card_fin]
  have hinclusionExclusion := Finset.card_union_add_card_inter firstSubset secondSubset
  rw [hunionCard, hfirstCard, hsecondCard, ← hsize] at hinclusionExclusion
  have hinterEmpty : firstSubset ∩ secondSubset = ∅ :=
    Finset.card_eq_zero.mp (by omega)
  exact ⟨Finset.disjoint_iff_inter_eq_empty.mpr hinterEmpty, hunion⟩

/-! ## The saturated-atom exclusion — the pattern-level filter -/

/-- **A SATURATED atom pins its share.**  If the atom lies in EVERY active subset
then the coverage sum, which is the (C1) sum restricted to the subsets containing
the atom, IS the unrestricted (C1) sum; the latter is one, so `t_c * value = 1`.

Unlike E1 and E2 the hypothesis here is COMBINATORIAL — it reads off the active
family alone, with no condition on the tight directions or the multiplier — so it
is checkable pattern by pattern, and it is the exclusion that the `(6,3)` orbit
census applies after the `p >= 3` cut. -/
theorem weight_mul_value_eq_one_of_saturatedAtom
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) {atomLabel : Fin m}
    (hsaturated : ∀ activeLabel ∈ activeSet, atomLabel ∈ activeSubset activeLabel) :
    D.weight atomLabel * value = 1 := by
  have hcoverage := coverageLaw_of_isQuadricStationaryData hdata atomLabel
  have hone := tightOverlap_sum_eq_one_of_isQuadricStationaryData hdata hvalueNe atomLabel
  have hrestrictedEqFull : ∑ activeLabel ∈ activeSet,
        (if atomLabel ∈ activeSubset activeLabel
          then activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ D.atom atomLabel) ^ 2 else 0)
      = ∑ activeLabel ∈ activeSet,
        activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ D.atom atomLabel) ^ 2 :=
    Finset.sum_congr rfl fun activeLabel hactive => if_pos (hsaturated activeLabel hactive)
  rw [hrestrictedEqFull, hone] at hcoverage
  exact hcoverage.symm

/-- **The value is at least one whenever some atom is saturated.**  Its share is
one and its weight is at most one, so the value is the reciprocal of a number in
`(0, 1]`.  Contrapositive: below one NO atom lies in every active subset — a
purely combinatorial exclusion on the active family. -/
theorem one_le_value_of_saturatedAtom
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) {atomLabel : Fin m}
    (hsaturated : ∀ activeLabel ∈ activeSet, atomLabel ∈ activeSubset activeLabel) :
    1 ≤ value := by
  have hshare := weight_mul_value_eq_one_of_saturatedAtom hdata hvalueNe hsaturated
  have hweightPos := D.weight_pos atomLabel
  have hweightLe : D.weight atomLabel ≤ 1 := by
    rw [← D.weight_sum_one]
    exact Finset.single_le_sum (fun otherAtom _ => (D.weight_pos otherAtom).le)
      (Finset.mem_univ atomLabel)
  have hvaluePos : 0 < value := by
    rcases lt_trichotomy value 0 with hnegative | hzero | hpositive
    · nlinarith
    · rw [hzero, mul_zero] at hshare; norm_num at hshare
    · exact hpositive
  nlinarith [mul_nonneg (sub_nonneg.mpr hweightLe) hvaluePos.le]

/-- **No atom of a below-one datum is saturated.**  The contrapositive reading,
in the shape the `(6,3)` orbit census consumes: every surviving active family
leaves at least one atom out of at least one of its subsets. -/
theorem exists_activeSubset_not_mem_of_value_lt_one
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (hbelowOne : value < 1)
    (atomLabel : Fin m) :
    ∃ activeLabel ∈ activeSet, atomLabel ∉ activeSubset activeLabel := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  exact absurd hbelowOne (not_lt.mpr (one_le_value_of_saturatedAtom hdata hvalueNe hall))

/-! ## The block-mass identity — a proved constraint on the PARTITION branch -/

/-- **A split block carries its own weight.**  Suppose a subset `block` of the
atoms is such that every active subset either EQUALS it or is disjoint from it —
exactly the situation of the partition branch of the `(6,3)` dichotomy below.
Then the Clarke multiplier mass sitting on `block` equals `block`'s Parseval
weight mass:

    `sum_{i : C_i = block} lambda_i  =  sum_{c in block} t_c` .

Summing the coverage law over the atoms of `block` and swapping the two sums, an
active index whose subset is `block` contributes `lambda_i` times the Rayleigh
quotient `u_i^T S_block u_i = value`, and a disjoint one contributes nothing.

This is NOT a proof of the open leaf named in the header; it is a necessary
condition that any partition-pattern datum must satisfy, recorded so the leaf is
attacked with the constraint in hand rather than from scratch. -/
theorem activeWeight_blockMass_eq_weight_blockMass
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) {block : Finset (Fin m)}
    (hblockNonempty : block.Nonempty)
    (hsplit : ∀ activeLabel ∈ activeSet,
      activeSubset activeLabel = block ∨ Disjoint (activeSubset activeLabel) block) :
    ∑ activeLabel ∈ activeSet,
        (if activeSubset activeLabel = block then activeWeight activeLabel else 0)
      = ∑ atomLabel ∈ block, D.weight atomLabel := by
  classical
  have hcoverageSum : ∑ atomLabel ∈ block, ∑ activeLabel ∈ activeSet,
        (if atomLabel ∈ activeSubset activeLabel
          then activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ D.atom atomLabel) ^ 2 else 0)
      = (∑ atomLabel ∈ block, D.weight atomLabel) * value := by
    rw [Finset.sum_congr rfl fun atomLabel _ =>
      coverageLaw_of_isQuadricStationaryData hdata atomLabel, ← Finset.sum_mul]
  rw [Finset.sum_comm] at hcoverageSum
  have hperIndex : ∀ activeLabel ∈ activeSet,
      ∑ atomLabel ∈ block,
          (if atomLabel ∈ activeSubset activeLabel
            then activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ D.atom atomLabel) ^ 2 else 0)
        = (if activeSubset activeLabel = block then activeWeight activeLabel else 0) * value := by
    intro activeLabel hactive
    rcases hsplit activeLabel hactive with hequal | hdisjoint
    · have hrayleigh : ∑ atomLabel ∈ block,
          (tightDir activeLabel ⬝ᵥ D.atom atomLabel) ^ 2 = value := by
        have hform :=
          subsetSum_form_eq_sum_sq D (activeSubset activeLabel) (tightDir activeLabel)
        rw [hdata.tightDir_isEigenvector activeLabel hactive, dotProduct_smul, smul_eq_mul,
          hdata.tightDir_unit activeLabel hactive, mul_one, hequal] at hform
        rw [hform]
        exact Finset.sum_congr rfl fun atomLabel _ => congrArg (· ^ 2) (dotProduct_comm _ _)
      rw [if_pos hequal,
        Finset.sum_congr rfl (fun atomLabel hatom => if_pos (hequal ▸ hatom :
          atomLabel ∈ activeSubset activeLabel)),
        ← Finset.mul_sum, hrayleigh]
    · have houtside : ∀ atomLabel ∈ block, atomLabel ∉ activeSubset activeLabel :=
        fun atomLabel hatom => Finset.disjoint_right.mp hdisjoint hatom
      have hnotEqual : activeSubset activeLabel ≠ block := by
        intro hequal
        obtain ⟨someAtom, hsomeAtom⟩ := hblockNonempty
        exact houtside someAtom hsomeAtom (hequal ▸ hsomeAtom)
      rw [if_neg hnotEqual, zero_mul,
        Finset.sum_congr rfl (fun atomLabel hatom => if_neg (houtside atomLabel hatom)),
        Finset.sum_const_zero]
  rw [Finset.sum_congr rfl hperIndex, ← Finset.sum_mul] at hcoverageSum
  exact mul_right_cancel₀ hvalueNe hcoverageSum

end StationarityConsequences

/-! ## E3 at the campaign size `(6,3)` -/

section SixThree

variable {activeIndex : Type*} {D : WeightedDesign 6 3} {value : ℝ}
  {multiplierMatrix : Matrix (Fin 3) (Fin 3) ℝ} {activeSet : Finset activeIndex}
  {activeSubset : activeIndex → Finset (Fin 6)} {activeWeight : activeIndex → ℝ}
  {tightDir : activeIndex → (Fin 3 → ℝ)}

/-- **E3 AT (6,3), as far as it is proved.**  A stationarity datum with a nonzero
value strictly below one has either at least THREE distinct active triples, or an
active family that is a two-block PARTITION of the six atoms whose tight directions
are linearly dependent.

The first branch is the pigeonhole `6 <= 3 * p`; the second is inclusion-exclusion
plus the transversal exclusion.  What is NOT proved, and is stated as the open leaf
in the header, is that the partition branch is empty — the route reported for it,
through `M_q = M P_q`, does not survive checking, so it is neither used nor
assumed. -/
theorem three_le_card_activeSubsetImage_or_dependentPartition_sixThree
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (hbelowOne : value < 1) :
    3 ≤ (activeSet.image activeSubset).card
      ∨ (¬ HasIndependentTightSupport activeSet activeWeight tightDir
          ∧ ∃ firstSubset secondSubset : Finset (Fin 6),
              activeSet.image activeSubset = {firstSubset, secondSubset}
                ∧ Disjoint firstSubset secondSubset
                ∧ firstSubset ∪ secondSubset = Finset.univ) := by
  by_cases hthree : 3 ≤ (activeSet.image activeSubset).card
  · exact Or.inl hthree
  · refine Or.inr ⟨not_hasIndependentTightSupport_of_value_lt_one hdata hvalueNe hbelowOne, ?_⟩
    have htwo := two_le_card_activeSubsetImage_of_rank_lt_size hdata hvalueNe (by norm_num)
    have hexactly : (activeSet.image activeSubset).card = 2 := by omega
    obtain ⟨firstSubset, secondSubset, _, himage⟩ := Finset.card_eq_two.mp hexactly
    obtain ⟨hdisjoint, hunion⟩ :=
      disjoint_union_of_card_activeSubsetImage_eq_two hdata hvalueNe (by norm_num) himage
    exact ⟨firstSubset, secondSubset, himage, hdisjoint, hunion⟩

end SixThree

/-! ## The below-one witness at `(4,2)`

Four atoms of squared norm two at `0`, `45`, `90` and `135` degrees, weights all a
quarter.  The four `2`-subsets whose atoms meet at `45` degrees are the active
family; each has `S_C` with eigenvalues `2 +- sqrt 2`, and the SMALLER one is the
common value.  The two orthogonal pairs `{0,3}` and `{1,2}` are inactive, and both
have `S_C = 2 I`, which is why `F(D) = 2` and the design is a comfortable instance
of `GtzWeighted 4 2` rather than a counterexample.

Everything is exact in `Q(sqrt 2)`.  The tight directions are the unit bisectors,
whose norms are the nested radicals `sqrt(4 +- 2 sqrt 2)`; those cancel in every
equation of the bundle, because atom stationarity pairs a tight direction against
itself, so all of the arithmetic below happens in `Q(sqrt 2)` after one rewrite of
`(4 +- 2 sqrt 2)^{-1}`. -/

/-- The square root of two, named once so the witness reads. -/
noncomputable def rootTwo : ℝ := Real.sqrt 2

theorem rootTwo_mul_self : rootTwo * rootTwo = 2 :=
  Real.mul_self_sqrt (by norm_num)

theorem rootTwo_pos : 0 < rootTwo :=
  Real.sqrt_pos.mpr (by norm_num)

theorem rootTwo_lt_two : rootTwo < 2 := by
  nlinarith [rootTwo_mul_self, rootTwo_pos]

theorem one_lt_rootTwo : 1 < rootTwo := by
  nlinarith [rootTwo_mul_self, rootTwo_pos]

theorem rootTwo_sq : rootTwo ^ 2 = 2 := by
  rw [pow_two, rootTwo_mul_self]

theorem rootTwo_cube : rootTwo ^ 3 = 2 * rootTwo := by
  rw [pow_succ, rootTwo_sq]

theorem rootTwo_pow_four : rootTwo ^ 4 = 4 := by
  rw [pow_succ, rootTwo_cube, mul_assoc, rootTwo_mul_self]
  norm_num

theorem inv_four_add_two_rootTwo : (4 + 2 * rootTwo)⁻¹ = (4 - 2 * rootTwo) / 8 := by
  have hne : (4 : ℝ) + 2 * rootTwo ≠ 0 := by nlinarith [rootTwo_pos]
  field_simp
  nlinarith [rootTwo_mul_self]

theorem inv_four_sub_two_rootTwo : (4 - 2 * rootTwo)⁻¹ = (4 + 2 * rootTwo) / 8 := by
  have hne : (4 : ℝ) - 2 * rootTwo ≠ 0 := by nlinarith [rootTwo_lt_two]
  field_simp
  nlinarith [rootTwo_mul_self]

/-- The four atoms of the below-one witness. -/
noncomputable def belowOneAtom : Fin 4 → Fin 2 → ℝ :=
  ![![rootTwo, 0], ![-1, 1], ![1, 1], ![0, rootTwo]]

/-- The witness is equally weighted. -/
noncomputable def belowOneWeight : Fin 4 → ℝ := ![1 / 4, 1 / 4, 1 / 4, 1 / 4]

/-- **The below-one witness is a genuine design** — all atoms nonzero, all weights
positive, Parseval exact in `Q(sqrt 2)`. -/
noncomputable def belowOneDesign : WeightedDesign 4 2 where
  atom := belowOneAtom
  weight := belowOneWeight
  weight_pos := by
    intro atomLabel
    fin_cases atomLabel <;> norm_num [belowOneWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_four]
    simp [belowOneWeight]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_four, smul_eq_mul]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [belowOneAtom, belowOneWeight] <;>
      nlinarith [rootTwo_mul_self]

/-- The common value of the witness: the smaller eigenvalue `2 - sqrt 2` of each
active pair, which is below one. -/
noncomputable def belowOneValue : ℝ := 2 - rootTwo

/-- The tight directions before normalisation. -/
noncomputable def belowOneRawTightDir : Fin 4 → Fin 2 → ℝ :=
  ![![1, 1 + rootTwo], ![1, -(1 + rootTwo)], ![1, rootTwo - 1], ![1, 1 - rootTwo]]

/-- The squared norms of the unnormalised tight directions. -/
noncomputable def belowOneTightNormSq : Fin 4 → ℝ :=
  ![4 + 2 * rootTwo, 4 + 2 * rootTwo, 4 - 2 * rootTwo, 4 - 2 * rootTwo]

/-- The active family: the four pairs whose atoms meet at forty-five degrees. -/
def belowOneSubset : Fin 4 → Finset (Fin 4) :=
  ![{0, 1}, {0, 2}, {1, 3}, {2, 3}]

theorem belowOneTightNormSq_pos (tripleIndex : Fin 4) : 0 < belowOneTightNormSq tripleIndex := by
  fin_cases tripleIndex <;> simp [belowOneTightNormSq] <;> nlinarith [rootTwo_lt_two, rootTwo_pos]

theorem belowOneRawTightDir_dot_self (tripleIndex : Fin 4) :
    belowOneRawTightDir tripleIndex ⬝ᵥ belowOneRawTightDir tripleIndex
      = belowOneTightNormSq tripleIndex := by
  fin_cases tripleIndex <;>
    simp [belowOneRawTightDir, belowOneTightNormSq, dotProduct, Fin.sum_univ_two] <;>
    nlinarith [rootTwo_mul_self]

/-- Each unnormalised tight direction is an eigenvector of its pair's atom sum at
the common value. -/
theorem belowOneRawTightDir_isEigenvector (tripleIndex : Fin 4) :
    subsetSum belowOneDesign (belowOneSubset tripleIndex) *ᵥ belowOneRawTightDir tripleIndex
      = belowOneValue • belowOneRawTightDir tripleIndex := by
  funext coordIndex
  rw [subsetSum]
  fin_cases tripleIndex <;> fin_cases coordIndex <;>
    simp [belowOneSubset, belowOneDesign, belowOneAtom, belowOneRawTightDir, belowOneValue,
      atomMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sum_apply,
      Matrix.vecMulVec_apply] <;>
    linarith [rootTwo_sq, rootTwo_cube, rootTwo_pow_four]

/-- The UNIT tight directions, as `IsQuadricStationaryData` requires. -/
noncomputable def belowOneTightDir (tripleIndex : Fin 4) : Fin 2 → ℝ :=
  (Real.sqrt (belowOneTightNormSq tripleIndex))⁻¹ • belowOneRawTightDir tripleIndex

theorem belowOneTightScale_mul_self (tripleIndex : Fin 4) :
    (Real.sqrt (belowOneTightNormSq tripleIndex))⁻¹
        * (Real.sqrt (belowOneTightNormSq tripleIndex))⁻¹
      = (belowOneTightNormSq tripleIndex)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (belowOneTightNormSq_pos tripleIndex).le]

theorem belowOneTightDir_unit (tripleIndex : Fin 4) :
    belowOneTightDir tripleIndex ⬝ᵥ belowOneTightDir tripleIndex = 1 := by
  rw [belowOneTightDir, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    belowOneRawTightDir_dot_self, ← mul_assoc, belowOneTightScale_mul_self,
    inv_mul_cancel₀ (ne_of_gt (belowOneTightNormSq_pos tripleIndex))]

theorem belowOneTightDir_isEigenvector (tripleIndex : Fin 4) :
    subsetSum belowOneDesign (belowOneSubset tripleIndex) *ᵥ belowOneTightDir tripleIndex
      = belowOneValue • belowOneTightDir tripleIndex := by
  rw [belowOneTightDir, Matrix.mulVec_smul, belowOneRawTightDir_isEigenvector, smul_comm]

/-- **The nested radicals cancel.**  Pairing a unit tight direction against a probe
and then scaling by it again produces the inverse SQUARED norm, which is rational
in `sqrt 2`.  This is why no nested radical survives into the stationarity
equations. -/
theorem belowOneTightDir_pairing_smul (tripleIndex : Fin 4) (probe : Fin 2 → ℝ) :
    (belowOneTightDir tripleIndex ⬝ᵥ probe) • belowOneTightDir tripleIndex
      = ((belowOneTightNormSq tripleIndex)⁻¹ * (belowOneRawTightDir tripleIndex ⬝ᵥ probe))
        • belowOneRawTightDir tripleIndex := by
  rw [belowOneTightDir, smul_dotProduct, smul_eq_mul, smul_smul]
  congr 1
  rw [mul_right_comm, belowOneTightScale_mul_self]

/-- The inverse squared norms, written without an inverse. -/
noncomputable def belowOneTightScaleSq : Fin 4 → ℝ :=
  ![(4 - 2 * rootTwo) / 8, (4 - 2 * rootTwo) / 8, (4 + 2 * rootTwo) / 8, (4 + 2 * rootTwo) / 8]

theorem belowOneTightNormSq_inv_eq (tripleIndex : Fin 4) :
    (belowOneTightNormSq tripleIndex)⁻¹ = belowOneTightScaleSq tripleIndex := by
  fin_cases tripleIndex <;>
    simp [belowOneTightNormSq, belowOneTightScaleSq, inv_four_add_two_rootTwo,
      inv_four_sub_two_rootTwo]

/-- The Clarke multipliers of the witness: uniform on the four active pairs. -/
noncomputable def belowOneMultiplier : Fin 4 → ℝ := ![1 / 4, 1 / 4, 1 / 4, 1 / 4]

/-- The Lagrange multiplier of the witness, `((2 - sqrt 2)/2) I` — isotropic,
because every leverage is two. -/
noncomputable def belowOneMultiplierMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  ((2 - rootTwo) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- Each summand of atom stationarity, rewritten onto the unnormalised directions. -/
theorem belowOneAtomStationarity_term (atomLabel tripleIndex : Fin 4) :
    (if atomLabel ∈ belowOneSubset tripleIndex then
        belowOneMultiplier tripleIndex
          * (belowOneTightDir tripleIndex ⬝ᵥ belowOneDesign.atom atomLabel) else 0)
      • belowOneTightDir tripleIndex
      = (if atomLabel ∈ belowOneSubset tripleIndex then
          belowOneMultiplier tripleIndex * belowOneTightScaleSq tripleIndex
            * (belowOneRawTightDir tripleIndex ⬝ᵥ belowOneDesign.atom atomLabel) else 0)
        • belowOneRawTightDir tripleIndex := by
  by_cases hmem : atomLabel ∈ belowOneSubset tripleIndex
  · rw [if_pos hmem, if_pos hmem, mul_smul, belowOneTightDir_pairing_smul,
      belowOneTightNormSq_inv_eq, smul_smul, mul_assoc]
  · rw [if_neg hmem, if_neg hmem, zero_smul, zero_smul]

/-- Every atom of the witness lies on the multiplier's quadric at the value. -/
theorem belowOneQuadric (atomLabel : Fin 4) :
    belowOneDesign.atom atomLabel ⬝ᵥ (belowOneMultiplierMatrix *ᵥ belowOneDesign.atom atomLabel)
      = 2 - rootTwo := by
  fin_cases atomLabel <;>
    simp [belowOneDesign, belowOneAtom, belowOneMultiplierMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;>
    linarith [rootTwo_sq, rootTwo_cube, rootTwo_pow_four]

/-- **THE BELOW-ONE STATIONARITY DATUM.**  All eight fields of the bundle hold at
`(m,k) = (4,2)` with `value = 2 - sqrt 2 < 1`: four active pairs, uniform
multipliers, unit tight eigenvectors, isotropic `Lambda`, exact atom stationarity
and weight stationarity. -/
theorem belowOneDesign_isQuadricStationaryData :
    IsQuadricStationaryData belowOneDesign belowOneValue belowOneMultiplierMatrix
      (Finset.univ : Finset (Fin 4)) belowOneSubset belowOneMultiplier belowOneTightDir where
  activeWeight_nonneg := by
    intro tripleIndex _
    fin_cases tripleIndex <;> norm_num [belowOneMultiplier]
  activeWeight_sum_one := by
    rw [Fin.sum_univ_four]
    simp [belowOneMultiplier]
    norm_num
  activeSubset_card := by
    intro tripleIndex _
    fin_cases tripleIndex <;> decide
  tightDir_unit := fun tripleIndex _ => belowOneTightDir_unit tripleIndex
  tightDir_isEigenvector := fun tripleIndex _ => belowOneTightDir_isEigenvector tripleIndex
  atomStationarity := by
    intro atomLabel
    rw [Finset.sum_congr rfl (fun tripleIndex _ =>
      belowOneAtomStationarity_term atomLabel tripleIndex), Fin.sum_univ_four]
    funext coordIndex
    fin_cases atomLabel <;> fin_cases coordIndex <;>
      simp [belowOneSubset, belowOneDesign, belowOneAtom, belowOneWeight, belowOneRawTightDir,
        belowOneTightScaleSq, belowOneMultiplier, belowOneMultiplierMatrix] <;>
      linarith [rootTwo_sq, rootTwo_cube, rootTwo_pow_four]
  weightStationarity := by
    intro atomFirst atomSecond
    rw [belowOneQuadric atomFirst, belowOneQuadric atomSecond]

theorem belowOneValue_pos : 0 < belowOneValue := by
  rw [belowOneValue]; linarith [rootTwo_lt_two]

theorem belowOneValue_lt_one : belowOneValue < 1 := by
  rw [belowOneValue]; linarith [one_lt_rootTwo]

/-- The two INACTIVE pairs are orthogonal, so their atom sum is `2 I` and the gap is
the identity. -/
theorem subsetSum_belowOneDesign_orthogonalPair :
    subsetSum belowOneDesign ({0, 3} : Finset (Fin 4)) - 1 = 1 := by
  ext rowIndex colIndex
  rw [subsetSum, show ({0, 3} : Finset (Fin 4)) = {(0 : Fin 4), (3 : Fin 4)} from rfl]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [belowOneDesign, belowOneAtom, atomMatrix] <;>
    linarith [rootTwo_sq]

/-- **The witness is NOT a GTZ counterexample.**  Its orthogonal pair dominates, and
strictly: the gap is the identity.  So `F(D) = 2` and the design satisfies the
conclusion of `GtzWeighted 4 2` with margin, while the stationarity datum sits at
`2 - sqrt 2`.  The datum is stationary for the max over the four CHOSEN pairs,
which are the minimisers, not for `F`. -/
theorem dominates_belowOneDesign_orthogonalPair :
    Dominates belowOneDesign ({0, 3} : Finset (Fin 4)) := by
  rw [Dominates, subsetSum_belowOneDesign_orthogonalPair]
  exact Matrix.PosDef.posSemidef Matrix.PosDef.one

theorem exists_dominating_belowOneDesign :
    ∃ C : Finset (Fin 4), C.card = 2 ∧ Dominates belowOneDesign C :=
  ⟨{0, 3}, by decide, dominates_belowOneDesign_orthogonalPair⟩

/-- **Stationarity data with a value strictly between zero and one EXIST.**  The
packaged form of the witness. -/
theorem exists_isQuadricStationaryData_value_lt_one :
    ∃ (D : WeightedDesign 4 2) (value : ℝ) (multiplier : Matrix (Fin 2) (Fin 2) ℝ)
      (activeSubset : Fin 4 → Finset (Fin 4)) (activeWeight : Fin 4 → ℝ)
      (tightDir : Fin 4 → (Fin 2 → ℝ)),
      IsQuadricStationaryData D value multiplier (Finset.univ : Finset (Fin 4)) activeSubset
        activeWeight tightDir ∧ 0 < value ∧ value < 1 :=
  ⟨belowOneDesign, belowOneValue, belowOneMultiplierMatrix, belowOneSubset, belowOneMultiplier,
    belowOneTightDir, belowOneDesign_isQuadricStationaryData, belowOneValue_pos,
    belowOneValue_lt_one⟩

/-- **THE LIMITATIVE THEOREM.**  The stationarity bundle alone does NOT force the
value to be at least one, even at a nonzero value.  So the interior residual
obligation — no interior critical point of `F` with value below one — cannot be
stated as `IsQuadricStationaryData -> 1 <= value`, and every exclusion in this file
must carry, and does carry, a structural hypothesis the witness violates: its
multiplier is isotropic rather than rank one, its four tight directions are
dependent, and its active family has four distinct subsets rather than one or a
partition.

What the bundle is missing is the ARGMAX condition, `value >= lambda_min(S_C)` for
every `k`-subset and not only the active ones — a disjunctive real condition, not
an equation. -/
theorem not_forall_one_le_value_of_isQuadricStationaryData :
    ¬ ∀ (D : WeightedDesign 4 2) (value : ℝ) (multiplier : Matrix (Fin 2) (Fin 2) ℝ)
        (activeSubset : Fin 4 → Finset (Fin 4)) (activeWeight : Fin 4 → ℝ)
        (tightDir : Fin 4 → (Fin 2 → ℝ)),
      IsQuadricStationaryData D value multiplier (Finset.univ : Finset (Fin 4)) activeSubset
          activeWeight tightDir →
        value ≠ 0 → 1 ≤ value := by
  intro hforall
  have hbound := hforall belowOneDesign belowOneValue belowOneMultiplierMatrix belowOneSubset
    belowOneMultiplier belowOneTightDir belowOneDesign_isQuadricStationaryData
    (ne_of_gt belowOneValue_pos)
  exact absurd belowOneValue_lt_one (not_lt.mpr hbound)

/-! ## The ARGMAX field, and what attaching it costs

The witness above says the bundle is too weak.  This section says exactly HOW
weak, by naming the missing field, showing the witness fails it, and computing
what a datum satisfying it would be worth.

`IsQuadricStationaryData` asks that `value` be AN eigenvalue of each ACTIVE
`S_C`.  A genuine Clarke-critical point of `F = max_{|C| = k} lambda_min(S_C)`
satisfies more: no `k`-subset — active or not — has a smaller eigenvalue exceeding
`value`.  That surplus is a real condition, and contrary to what a first reading
of the header might suggest it IS expressible in the repo's existing vocabulary:
`lambda_min(S_C) <= value` says a unit probe achieves Rayleigh quotient at most
`value`, so no eigenvalue function and no spectral theory are needed.  What it is
NOT is a polynomial EQUATION — it is an existential over probes, disjunctive once
expanded — which is why it does not enter the Groebner systems of this lane and
why none of the linear-algebra derivations above can consume it.

The two theorems below are the point.  Attaching the argmax field does not make
the residual obligation a weaker lemma standing in front of GTZ; it makes the
obligation EXACTLY the interior case of GTZ at that size.  A datum satisfying it
below one REFUTES `GtzWeighted m k` outright.  So the interior lane buys the KKT
equations for free, and buys nothing else. -/

/-- **The argmax field the bundle omits.**  No `k`-subset beats `value`:
every `k`-subset admits a unit probe whose Rayleigh quotient against `S_C` is at
most `value`, i.e. `lambda_min(S_C) <= value` at EVERY `k`-subset and not only at
the active ones.  Written with a witnessing probe so that the statement uses only
`subsetSum` and the dot product. -/
def IsArgmaxDominated {m k : ℕ} (D : WeightedDesign m k) (value : ℝ) : Prop :=
  ∀ chosenSubset : Finset (Fin m), chosenSubset.card = k →
    ∃ probe : Fin k → ℝ, probe ⬝ᵥ probe = 1 ∧
      probe ⬝ᵥ (subsetSum D chosenSubset *ᵥ probe) ≤ value

/-- **With the argmax field attached, the obligation IS the interior case of GTZ.**
Granted `GtzWeighted m k`, an argmax-dominated value is at least one: the
dominating subset has `S_C - I` positive semidefinite, so every unit probe has
Rayleigh quotient at least one there, while the argmax field supplies a unit probe
with quotient at most `value`.

This is what the below-one witness costs.  The bundle alone cannot force
`1 <= value` (`not_forall_one_le_value_of_isQuadricStationaryData`); the bundle
PLUS the argmax field forces it, but only because GTZ at that size already does. -/
theorem one_le_value_of_isArgmaxDominated {m k : ℕ} {D : WeightedDesign m k} {value : ℝ}
    (hgtz : GtzWeighted m k) (hargmax : IsArgmaxDominated D value) :
    1 ≤ value := by
  obtain ⟨dominatingSubset, hcard, hdominates⟩ := hgtz D
  obtain ⟨probe, hunitProbe, hquotientLe⟩ := hargmax dominatingSubset hcard
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
  rw [star_trivial] at hnonneg
  have hexpand : probe ⬝ᵥ ((subsetSum D dominatingSubset - 1) *ᵥ probe)
      = probe ⬝ᵥ (subsetSum D dominatingSubset *ᵥ probe) - 1 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hunitProbe]
  rw [hexpand] at hnonneg
  linarith

/-- **An argmax-dominated value below one IS a counterexample.**  The
contrapositive, and the sentence the compactness reduction actually needs: what
the interior obligation forbids is not a technical artefact of the algebra but a
refutation of `GtzWeighted` at that size.  Naming it this way removes the
temptation to treat the interior residual as a smaller problem than GTZ. -/
theorem not_gtzWeighted_of_isArgmaxDominated_of_value_lt_one {m k : ℕ}
    {D : WeightedDesign m k} {value : ℝ}
    (hargmax : IsArgmaxDominated D value) (hbelowOne : value < 1) :
    ¬ GtzWeighted m k := fun hgtz =>
  absurd hbelowOne (not_lt.mpr (one_le_value_of_isArgmaxDominated hgtz hargmax))

/-- **The below-one witness fails the argmax field, at the orthogonal pair.**  Its
subset sum there is twice the identity, so EVERY unit probe has Rayleigh quotient
exactly two, and two is not at most `2 - sqrt 2`.  So the witness is not a
counterexample to the previous theorem — it is the demonstration that the argmax
field is precisely the missing one. -/
theorem not_isArgmaxDominated_belowOneDesign :
    ¬ IsArgmaxDominated belowOneDesign belowOneValue := by
  intro hargmax
  obtain ⟨probe, hunitProbe, hquotientLe⟩ := hargmax ({0, 3} : Finset (Fin 4)) (by decide)
  have hsubsetSum : subsetSum belowOneDesign ({0, 3} : Finset (Fin 4)) = 1 + 1 :=
    sub_eq_iff_eq_add.mp subsetSum_belowOneDesign_orthogonalPair
  rw [hsubsetSum, Matrix.add_mulVec, dotProduct_add, Matrix.one_mulVec, hunitProbe,
    belowOneValue] at hquotientLe
  linarith [rootTwo_pos]

end Gtz

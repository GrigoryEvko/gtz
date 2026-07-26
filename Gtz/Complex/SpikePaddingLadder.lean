/-
# The value half of the one-spike ladder: `alpha_{k+1} <= alpha_k`, and a
# `(5,3)` refutation one atom below the record

`Gtz/Complex/HesseMarginAttained.lean` builds the one-spike padding
CONSTRUCTION — `spikePaddedDesign`, a genuine weighted `(size+1, rank+1)`-design
over ℂ — and names the missing brick in its own header:

> **NOT proved here — the identified next brick.**  The VALUE half of the padding
> ladder ... Only the Finset surgery that extracts the old `rank`-subset from the
> padded `(rank+1)`-subset is missing.  Its consequences, none of which is claimed
> as proved here, would be: `alpha_4 <= alpha_3` (the first rank-four upper bound
> in this repository) and complex weighted `(5,3)` FALSE at margin
> `paddedMarginRankThree = 20/9 - 20 sqrt 3/27`.

This file supplies that brick and cashes both consequences, plus a third the
brick's own induction hands over for free: an upper bound at EVERY rank at once.

## Header: PROVED / CITED / MEASURED

**PROVED here, kernel-checked, zero new axioms, zero `sorry`.**

* `spikePaddedDesign_valueAtMost` — THE BRICK.  Padding a design whose every
  `rank`-subset fails above `bound` produces a design whose every
  `(rank+1)`-subset fails above `bound / (1 - spikeWeight)`.  Two cases, and only
  the second needed surgery: a `(rank+1)`-subset MISSING the spike has every atom
  flat in the last coordinate, so the excess carries `-level` at the corner
  `(last, last)` and dies by `not_posSemidef_of_diag_re_neg` — no null vector, no
  determinant; a subset CONTAINING the spike is tested only on the FLAT
  directions `Fin.snoc x 0`, where the spike contributes exactly nothing and each
  flattened atom contributes its old projection divided by `1 - spikeWeight`, so
  the old subset covers at level `level * (1 - spikeWeight)`.
* `covering_of_posSemidef_atomSum_sub_smul_one` — the converse of the ledger's
  packaging lemma, which the second case needs: positive semidefiniteness of an
  excess is read back as a covering inequality on projections.  Together with
  `posSemidef_atomSum_sub_smul_one` this makes the two readings interchangeable,
  and both directions are now available to the repository.
* `complexRankConstantAtMostAtSize_succ_of_gt` — one rung of the RANK ladder: a
  witness at `(size, rank)` at level `bound > 0` gives one at `(size+1, rank+1)`
  at ANY level strictly above `bound`.  Strictness is not slackness: the padded
  value is exactly `min(1/spikeWeight, bound/(1 - spikeWeight))`, which is
  STRICTLY above `bound` for every admissible spike weight
  (`paddedBound_gt_of_pos`), so the infimum over the family is `bound` and the
  family never attains it.
* `complexRankConstantAtMostAtSize_rank_add` — the ladder iterated: from one
  witness, a witness at every higher rank, at every level strictly above the
  original.  The intermediate levels are bisected, so no geometric bookkeeping
  appears.
* `complexRankConstantAtMost_three_le_rank` — **an upper bound at EVERY rank.**
  The mechanized statement is `forall rank >= 3, forall bound, hesseMargin <
  bound -> ComplexRankConstantAtMost rank bound` — a witness at every level above
  the record, never at the record itself.  That `alpha_rank <= hesseMargin`
  FOLLOWS is a remark about infima, not a theorem in this repository, which
  deliberately never writes `sInf`; quote the epsilon form when citing this.
  `Gtz/Complex/PerRankConstantLedger.lean` records "ranks `>= 4` — PROVED-LOWER
  `1/k` and NOTHING ELSE HERE"; that line is now superseded.
* `not_complexGtzWeighted_of_two_le_rank` — **complex weighted GTZ is FALSE at
  every rank at least two**, with an explicit size at each rank: rank two on the
  `ℂ²` SIC at `m = 4`, rank `3 + e` on the `e`-fold padded Hesse SIC at
  `m = 9 + e`.
* `complexRankConstantAtMostAtSize_five_three` — **weighted `(5,3)` is FALSE over
  ℂ**, at the exact margin `paddedMarginRankThree = 20/9 - 20 sqrt 3/27` the
  repository already owns (`paddedMargin_isRoot`, `paddedMargin_window`), i.e.
  ONE ATOM BELOW the shipped `(6,3)` refutations.  The design is the `ℂ²` SIC
  padded at `spikeWeight = 1/10`; its bound is `(10/9) * alphaRankTwo`, and the
  identification with the recorded constant is `paddedMargin_eq_scaledAlphaRankTwo`.
  Mechanism: `Gtz/Complex/ComplexPadding.lean`'s `paddedDesign` spends two
  antipodal spikes `+- sqrt 10 e_2` at weight `1/20` each on the SAME rank-one
  atom; merging them into one spike of weight `1/10` costs nothing and saves an
  atom.
* `complexRankConstantAtMostAtSize_six_four` — **weighted `(6,4)` is FALSE over
  ℂ**, the first kernel-checked rank-four refutation in this repository, from the
  `ℂ²` SIC padded twice at `spikeWeight = 1/200`.  No `4 x 4` determinant is
  taken: the ladder never sees one.

  **What this is NOT.**  It does not mechanize the value
  `6/7 = exactValueRankFourAtSix` that `Gtz/Complex/SharpConstantLedger.lean`
  records as EXACT ELSEWHERE.  What is unmechanized there is that the recorded
  NAIMARK-DUAL design has value exactly `6/7`, and that remains unmechanized;
  Mathlib still has no `det_fin_four`.  What is proved here is a bound at the
  rational `6/7` for a DIFFERENT design, whose own value is
  `alphaRankTwo * (200/199)^2 = 0.8538162790...`, strictly below.  The rational
  is used as a CAGE, not as an attained value.  Part F sharpens the same rung to
  every level above `alphaRankTwo` and cashes the difference as
  `ladderUndercuts_exactValueRankFourAtSix`.
* `complexRankConstantAtMostAtSize_two_le_rank` — **the same ladder at its SHARP
  level and its SMALLEST size.**  Part E's two small landings quote concrete
  constants because those are the ones the repository owned; neither is what the
  ladder delivers.  Feeding the rank-two witness to
  `complexRankConstantAtMostAtSize_rank_add` gives, for every `extra` at once, a
  `(4 + extra, 2 + extra)`-design at EVERY level strictly above `alphaRankTwo` —
  an `11%` improvement on the quoted `(5,3)` constant and a `1.4%` one on
  `(6,4)`.  Size `rank + 2` is the smallest available: the ledger records that at
  equal weights `m = k + 1` is exactly tight at `1`.
* `not_complexGtzWeighted_of_rank_add_two_le_size` — **complex weighted GTZ is
  FALSE at every rank at least two and every size at least `rank + 2`.**  This
  supersedes the size bounds of the two bullets below it: the Hesse-seeded ladder
  gives size `rank + 6`, and the rank-three and rank-four statements give `5` and
  `6` one rank at a time.
* `ladderUndercuts_exactValueRankFourAtSix` — **`6/7` is not the `(6,4)`
  infimum**, and `ladderUndercuts_paddedMarginRankThree` — `20/9 - 20 sqrt 3/27`
  is not the `(5,3)` infimum.  Each recorded constant is the value of one
  particular design; `ComplexRankConstantAtMostAtSize` quantifies over all of
  them, and the ladder exhibits strictly better ones at both sizes.  The
  ledger's own minimality hedge for `6/7` is EQUAL-WEIGHT ONLY and survives; the
  opening phrase "the exact `(6,4)` value over ℂ" does not, under the
  design-independent reading.
* `complexRankConstantAtMostAtSize_ten_four_of_gt`, and the size ladder from
  `Gtz/Complex/AtomSplitting.lean` instantiated at every rung, so each refutation
  above holds at its own size and at every larger one.  This theorem is the one
  `Gtz/Complex/HesseMarginAttained.lean`'s header points at when it instructs the
  reader to "read the number as `complexRankConstantAtMost_four_of_pos`, which is
  proved here": THAT NAME DOES NOT EXIST — it is declared in no module of this
  repository, and the statement it promised was exactly the brick that file lists
  as missing.  The name to cite is the one above.

**CITED (published, not mechanized anywhere in this repository).**

* Nesterenko, arXiv:2604.24087, Proposition 1: over ℂ at rank two the sharp
  constant is `2 - 2/sqrt 3 = alphaRankTwo`, attained exactly at the `ℂ²` SIC,
  with equality iff `4 | m` and the rows' Hopf images cluster at the vertices of
  a regular tetrahedron.  The whole rank-two half of this file's ladder inherits
  its sharpness from that citation and from nothing proved here.
* Sengupta-Pautov, arXiv:2604.05944: the real rank-two case; both papers state
  the problem OPEN for all `1 < k < n - 1` except `(n,k) = (4,2)`.  So the
  rank-three complex question this workflow owns is open in the literature too.
* CITATION DISAMBIGUATION, because the two are easy to swap and one workflow
  brief already did.  This repository cites TWO Nesterenko papers, and they are
  different results.  **arXiv:2604.24087** is the COMPLEX rank-two sharp constant
  `2 - 2/sqrt 3` — the one this file's ladder rides, cited the same way in
  `Gtz/Core/Basic.lean`, `Gtz/Complex/AtomSplitting.lean`,
  `Gtz/Complex/SharpConstantLedger.lean`, `Gtz/Complex/PerRankConstantLedger.lean`,
  `Gtz/Complex/HesseMarginAttained.lean`, `Gtz/Complex/AttainmentRankThree.lean`
  and `Gtz/Reduction/ExchangeInvariant.lean`.  **arXiv:2604.14050** is the REAL
  rank-two EQUALITY CRITERION (Proposition 1, `l_c = 1/2 + 1/(2 t_c)`, the
  three-cluster characterisation), cited in `Gtz/Design/EqualityLocus.lean` and
  `Gtz/Ties/CorankOneTieCriterion.lean`.  Do NOT "correct" `24087` to `14050`
  here: the complex sharp constant is `24087`.

**MEASURED (floating point, re-verified at 90 digits, NEVER a hypothesis below).**

Every claim in this block was recomputed with `mpmath` at `mp.dps = 90`.  Gram
blocks are built with an explicit conjugation on the RIGHT factor, matching
`complexAtom_apply` exactly; every least eigenvalue is read by the HERMITIAN
solver `eighe`, never by a general `eig`.  Parseval residuals are reported for
every design used, and none exceeds `5e-91`.

* CALIBRATION FIRST, as this ledger's numerics discipline requires.  The Hesse
  point reproduces itself three independent ways: `3(1 - cos 2 pi / 9)` in closed
  form, the least root of `8x^3 - 72x^2 + 162x - 81` by `polyroots`, and the
  maximum over all eighty-four triples of `lambda_min` — all three agreeing to
  `1e-90`, at Parseval residual `2.5e-91`.  The `ℂ²` SIC likewise reproduces
  `2 - 2/sqrt 3` over its six pairs to `2.5e-91`.
* THE PADDED VALUE IS EXACTLY `min(1/spikeWeight, V/(1 - spikeWeight))`, where
  `V` is the sub-design's value.  Checked against the direct subset maximum for
  the `ℂ²` SIC and the Hesse SIC at `spikeWeight = 3/10, 1/10, 1/100, 1/10000`,
  agreeing to `2e-90` every time.  Only `<=` is proved here; the matching `>=`
  would need the sub-design's ATTAINMENT, which exists for the Hesse SIC
  (`hesse_bindingTriple_dominatesAtLevel`) but is not carried through the ladder.
* THE `(5,3)` VALUE.  Direct subset maximum of the padded `ℂ²` SIC at
  `spikeWeight = 1/10`, over all ten triples:
  `0.939221624023053856646336043328983431894218331` (45 digits shown, 90
  computed), matching `20/9 - 20 sqrt 3/27` to `1.2e-91` and annihilating both
  `243 x^2 - 1080 x + 800` and `x^2 - (40/9) x + 800/243` exactly.  Parseval
  residual `1.5e-92`.  Slack below one: `0.0607783760`.
* THE `(6,4)` VALUE, AND WHAT IT SAYS ABOUT `6/7`.  Double padding at
  `spikeWeight = 1/200` measures
  `0.853816279003811490600441846414`, matching `alphaRankTwo * (200/199)^2` to
  `3.7e-91`, below `6/7` with slack `0.0033265781`.  That witness is a genuine
  `ComplexWeightedDesign 6 4` — six atoms, weights `(199/200)^2/4` four times,
  `(199/200)/200`, and `1/200`, all positive and summing to one, at Parseval
  residual `4.9e-91` — so `6/7` is NOT the infimum over weighted
  `(6,4)`-designs.  That consequence is now PROVED, not merely measured:
  `ladderUndercuts_exactValueRankFourAtSix`.  At `spikeWeight = 1/100` the
  same construction measures `0.862462464667634` and is ABOVE `6/7` — so `1/200`
  is not a free choice, and the arithmetic certificate in
  `complexRankConstantAtMostAtSize_six_four` is what pins it.
* THE LADDER NEVER ATTAINS ITS INFIMUM.  Padding the Hesse SIC at
  `spikeWeight = 1e-1 .. 1e-8` measures values exceeding
  `3(1 - cos 2 pi / 9)` by `7.80e-2, 7.09e-3, 7.03e-4, 7.02e-5, 7.02e-6,
  7.02e-7, 7.02e-8, 7.02e-9` — a clean `~ spikeWeight * hesse` descent with no
  member at the limit.  `paddedBound_gt_of_pos` is the proved form of that
  observation.  The excess is `V * w/(1 - w)` for `V = 3(1 - cos 2 pi / 9)`, and
  the second entry carries the `1/(1 - w)` correction like all the others: at
  `w = 1e-2` it is `0.00708956232973`, confirmed both by the closed form and by a
  direct maximum over all `4`-subsets of the padded ten-atom design.

**THE PER-SIZE INFIMUM IS NOT ALWAYS ATTAINED — a correction.**  It is tempting
to say "the per-`m` infimum is attained by compactness of the chart".  It is not:
the space of complex weighted `(m,k)`-designs is NOT compact, because a weight may
run to zero while its atom's norm runs to infinity as `1/sqrt` of it — which is
exactly what the spike does.  The MEASURED rank-three size profile shows the
failure concretely: at `m = 3` the measured infimum `1` and at `m = 5` the
measured infimum `2 - 2/sqrt 3` are both spike LIMITS, approached and not
attained, while `m = 4`, `m = 6,7,8` and `m >= 9` are attained (at `1`,
`3 - sqrt 5` and `3(1 - cos 2 pi / 9)` respectively).  `paddedBound_gt_of_pos`
proves the mechanism at the level of the ladder's own bounds; the per-size
statement itself is MEASURED, not proved, and would need a compactification of
the chart that this repository does not have.

**WHAT THIS FILE DOES NOT DO.**

* It does not improve the rank-three FLOOR.  `alpha_3 >= 1/3` remains the proved
  lower end (`complexRankConstantAtLeast_rankInverse`).
  `Gtz/Complex/AttainmentRankThree.lean` derives `(7 - sqrt 34)/3 ~ 0.3897` on
  paper and ships it as a NAMED CONSTANT with proved arithmetic, explicitly not
  as a proved floor: its steps 5-9 (the trace-of-inverse criterion, the Loewner
  comparison, the two-plane block, the scalar certificate) are unmechanized.
  Nothing here assumes them.  Named unproved hypothesis, verbatim from that
  file's scope note: *at a maximal-volume pick with
  `lambda_min < (7 - sqrt 34)/3`, one of the three exchanges against the covering
  atom already reaches that level.*
* It does not show `3(1 - cos 2 pi / 9)` IS `alpha_3`.  Every statement here is an
  UPPER bound, and upper bounds move the record down, never pin it.
* It does not prove RIGIDITY, and the measured evidence for it is WEAKER than an
  earlier draft of this header claimed.  What two independent implementations of
  perturb-and-reconverge agree on is that every run returning to the record value
  returns to the Hesse GEOMETRY — uniform weights `~ 1/9`, leverages `~ 3`, pair
  overlap moduli `~ 9/4`.  That the returning runs form a SINGLE GAUGE ORBIT is
  not established: the classifier is a rounded fingerprint, and at the optimizer's
  convergence floor (`~ 1e-5`) an independent reimplementation could not
  discriminate orbits at all — its `m = 12` positive control, where atom splitting
  predicts several orbits at one value, returned a single degenerate point and so
  FAILED.  Read the rigidity line as "returns to the Hesse geometry", with orbit
  uniqueness neither confirmed nor refuted.  Nothing about it is in the kernel.
* It does not touch `alpha_2`.  The rank-two constant enters only as the SOURCE
  of the `(5,3)` and `(6,4)` witnesses, and only through its proved window.

**WIRING — AN OPEN BLOCKER, NOT A FOOTNOTE.**  At the time of writing this module
is NOT reachable from the umbrella and NOT covered by the axiom ledger, and
neither are the two Complex modules beneath it.  `Gtz.lean` imports the Complex
directory only as far as `Gtz.Complex.AtomSplitting`; `Gtz.Complex.HesseMarginAttained`,
`Gtz.Complex.AttainmentRankThree` and this file are absent from it, and
`Gtz/Audit.lean` contains no `#print axioms` line for any declaration in any of
the three.  `lakefile.toml` sets `defaultTargets = ["Gtz"]`, so a bare
`lake build` compiles none of them and the repository's own zero-axiom gate does
not see this work.  Each file has been checked in isolation with
`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` and audited by an
independent `#print axioms` probe, but that is a per-stage check, not the
repository gate.  Three consecutive stages have now landed outside both; whoever
owns `Gtz.lean` and `Gtz/Audit.lean` should close this before the ledger absorbs
any of it. -/
import Mathlib
import Gtz.Complex.HesseMarginAttained

namespace Gtz

open Matrix Complex
open scoped ComplexOrder

set_option maxHeartbeats 1000000

/-! # Part A. Reading the padded design

The padding of `Gtz/Complex/HesseMarginAttained.lean` is three `Fin.snoc`s — one
on the atom list, one on the weight list, one inside each atom vector.  This part
unfolds all three once, and computes the only two projections the value argument
ever needs: those of a padded atom against a FLAT direction `Fin.snoc x 0`. -/

section PaddedReadings

variable {size rank : ℕ}

theorem flattenedAtom_castSucc (spikeWeight : ℝ) (vector : Fin rank → ℂ)
    (slot : Fin rank) :
    flattenedAtom spikeWeight vector slot.castSucc
      = vector slot / ((Real.sqrt (1 - spikeWeight) : ℝ) : ℂ) := by
  simp only [flattenedAtom, Fin.snoc_castSucc]

theorem flattenedAtom_last (spikeWeight : ℝ) (vector : Fin rank → ℂ) :
    flattenedAtom spikeWeight vector (Fin.last rank) = 0 := by
  simp only [flattenedAtom, Fin.snoc_last]

theorem spikeAtom_castSucc (spikeWeight : ℝ) (slot : Fin rank) :
    (spikeAtom spikeWeight : Fin (rank + 1) → ℂ) slot.castSucc = 0 := by
  simp only [spikeAtom, Fin.snoc_castSucc]

theorem spikePaddedAtom_castSucc (design : ComplexWeightedDesign size rank)
    (spikeWeight : ℝ) (oldLabel : Fin size) :
    spikePaddedAtom design spikeWeight oldLabel.castSucc
      = flattenedAtom spikeWeight (design.atom oldLabel) := by
  simp only [spikePaddedAtom, Fin.snoc_castSucc]

theorem spikePaddedAtom_last (design : ComplexWeightedDesign size rank)
    (spikeWeight : ℝ) :
    spikePaddedAtom design spikeWeight (Fin.last size) = spikeAtom spikeWeight := by
  simp only [spikePaddedAtom, Fin.snoc_last]

theorem spikePaddedDesign_atom (design : ComplexWeightedDesign size rank)
    {spikeWeight : ℝ} (hlow : 0 < spikeWeight) (hhigh : spikeWeight < 1) :
    (spikePaddedDesign design hlow hhigh).atom = spikePaddedAtom design spikeWeight := rfl

/-- A flat direction has the squared length of the direction it flattens. -/
theorem sumNormSq_snocZero (direction : Fin rank → ℂ) :
    (∑ coord, Complex.normSq ((Fin.snoc direction 0 : Fin (rank + 1) → ℂ) coord))
      = ∑ slot, Complex.normSq (direction slot) := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Complex.normSq_zero, add_zero]

/-- **The spike is invisible on flat directions.**  Its only nonzero coordinate is
the new one, which a flat direction zeroes. -/
theorem starDot_spikeAtom_snocZero (spikeWeight : ℝ) (direction : Fin rank → ℂ) :
    star (spikeAtom spikeWeight) ⬝ᵥ (Fin.snoc direction 0 : Fin (rank + 1) → ℂ) = 0 := by
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, spikeAtom_castSucc, map_zero, zero_mul,
    mul_zero, Finset.sum_const_zero, add_zero]

/-- **A flattened atom projects like its source, rescaled.**  Stated
multiplicatively — the rescaling factor moved to the other side — so no division
and no invertibility hypothesis appears in the statement. -/
theorem starDot_flattenedAtom_snocZero {spikeWeight : ℝ} (hgap : 0 < 1 - spikeWeight)
    (vector direction : Fin rank → ℂ) :
    ((Real.sqrt (1 - spikeWeight) : ℝ) : ℂ)
        * (star (flattenedAtom spikeWeight vector)
            ⬝ᵥ (Fin.snoc direction 0 : Fin (rank + 1) → ℂ))
      = star vector ⬝ᵥ direction := by
  have hgapNe : ((Real.sqrt (1 - spikeWeight) : ℝ) : ℂ) ≠ 0 := by
    simpa using Real.sqrt_ne_zero'.mpr hgap
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, flattenedAtom_castSucc, flattenedAtom_last,
    map_zero, zero_mul, add_zero, map_div₀, Complex.conj_ofReal]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun slot _ => ?_
  field_simp

/-- The same reading in squared-modulus form: the flattened projection carries a
factor `1/(1 - spikeWeight)`, which is the whole content of the padding bound. -/
theorem normSq_starDot_flattenedAtom_snocZero {spikeWeight : ℝ} (hgap : 0 < 1 - spikeWeight)
    (vector direction : Fin rank → ℂ) :
    (1 - spikeWeight)
        * Complex.normSq (star (flattenedAtom spikeWeight vector)
            ⬝ᵥ (Fin.snoc direction 0 : Fin (rank + 1) → ℂ))
      = Complex.normSq (star vector ⬝ᵥ direction) := by
  have hstep := congrArg Complex.normSq
    (starDot_flattenedAtom_snocZero hgap vector direction)
  rwa [Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt hgap.le] at hstep

end PaddedReadings

/- The six unfolding lemmas above are convenient inside this file and nowhere
else: `flattenedAtom_castSucc` puts a division into simp-normal form and
`spikePaddedDesign_atom` rewrites a structure projection of a term carrying proof
arguments, neither of which any importer asked for.  Every use below names them
explicitly in a `rw` or a `simp only`, so the attribute changes no proof here; it
is `local` purely so that wiring this module into the umbrella does not silently
enlarge the global simp set. -/
attribute [local simp] flattenedAtom_castSucc flattenedAtom_last spikeAtom_castSucc
  spikePaddedAtom_castSucc spikePaddedAtom_last spikePaddedDesign_atom

/-! # Part B. Positive semidefiniteness read back as a covering inequality

`Gtz/Complex/PerRankConstantLedger.lean` proves the packaging direction — a
covering inequality on projections BUILDS a Loewner bound.  The padding argument
needs the converse, and this is it.  With both directions available the two
readings are interchangeable, which is what lets the second case of the padding
proof pass an inequality from the padded design back to the original. -/

section CoveringReadback

variable {m k : ℕ}

/-- **The converse of the packaging lemma.**  If a subset's excess is positive
semidefinite at a level, then the squared projections on that subset's atoms cover
the level times the squared length of EVERY direction.  Stated for a bare atom
family, so it applies to a design's atoms and to any reindexing of them. -/
theorem covering_of_posSemidef_atomSum_sub_smul_one (atomOf : Fin m → (Fin k → ℂ))
    (selection : Finset (Fin m)) (level : ℝ)
    (hpsd : ((∑ atomLabel ∈ selection, complexAtom (atomOf atomLabel))
        - ((level : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef)
    (direction : Fin k → ℂ) :
    level * (∑ coord, Complex.normSq (direction coord))
      ≤ ∑ atomLabel ∈ selection, Complex.normSq (star (atomOf atomLabel) ⬝ᵥ direction) := by
  have hquad := hpsd.dotProduct_mulVec_nonneg direction
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum,
    Matrix.smul_mulVec, dotProduct_smul, Matrix.one_mulVec, smul_eq_mul,
    starDot_self_eq_sumNormSq] at hquad
  have hterms : (∑ atomLabel ∈ selection,
        star direction ⬝ᵥ (complexAtom (atomOf atomLabel) *ᵥ direction))
      = (((∑ atomLabel ∈ selection,
          Complex.normSq (star (atomOf atomLabel) ⬝ᵥ direction)) : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun atomLabel _ =>
      quadForm_complexAtom (atomOf atomLabel) direction
  rw [hterms] at hquad
  have hreal : (((∑ atomLabel ∈ selection,
          Complex.normSq (star (atomOf atomLabel) ⬝ᵥ direction)) : ℝ) : ℂ)
        - ((level : ℝ) : ℂ) * (((∑ coord, Complex.normSq (direction coord)) : ℝ) : ℂ)
      = (((∑ atomLabel ∈ selection,
            Complex.normSq (star (atomOf atomLabel) ⬝ᵥ direction))
          - level * (∑ coord, Complex.normSq (direction coord)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hreal, Complex.zero_le_real] at hquad
  linarith

end CoveringReadback

/-! # Part C. The brick: the padded design's value

Two cases, and the whole argument is the case split.  A `(rank+1)`-subset either
misses the spike — then it is flat and dies at the new corner — or contains it,
and then testing only flat directions reduces it to a `rank`-subset of the design
it came from. -/

section PaddedValue

variable {size rank : ℕ}

/-- **A flat subset dies at the new corner.**  If a `(rank+1)`-subset of the padded
index set avoids the spike, every one of its atoms has last coordinate zero, so
the excess has `-level` at the corner `(last, last)` and no positive level
survives.  No null vector and no determinant is needed. -/
theorem not_posSemidef_paddedAtomSum_sub_of_last_notMem
    (design : ComplexWeightedDesign size rank) (spikeWeight : ℝ)
    {subset : Finset (Fin (size + 1))} (hlastOut : Fin.last size ∉ subset)
    {level : ℝ} (hlevelPos : 0 < level) :
    ¬ ((∑ atomLabel ∈ subset, complexAtom (spikePaddedAtom design spikeWeight atomLabel))
        - ((level : ℝ) : ℂ)
          • (1 : Matrix (Fin (rank + 1)) (Fin (rank + 1)) ℂ)).PosSemidef := by
  refine not_posSemidef_of_diag_re_neg (Fin.last rank) ?_
  have hcornerZero : ∀ atomLabel : Fin (size + 1), atomLabel ∈ subset →
      complexAtom (spikePaddedAtom design spikeWeight atomLabel)
        (Fin.last rank) (Fin.last rank) = 0 := by
    refine Fin.lastCases ?_ ?_
    · intro hmember
      exact absurd hmember hlastOut
    · intro oldLabel _
      rw [complexAtom_apply, spikePaddedAtom_castSucc, flattenedAtom_last]
      simp
  have hentry : ((∑ atomLabel ∈ subset,
        complexAtom (spikePaddedAtom design spikeWeight atomLabel))
        - ((level : ℝ) : ℂ) • (1 : Matrix (Fin (rank + 1)) (Fin (rank + 1)) ℂ))
        (Fin.last rank) (Fin.last rank) = -((level : ℝ) : ℂ) := by
    rw [Matrix.sub_apply, Matrix.sum_apply, Finset.sum_eq_zero hcornerZero,
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, zero_sub]
  rw [hentry]
  simpa using hlevelPos

/-- **THE VALUE HALF OF THE PADDING LADDER.**  Padding a design whose every
`rank`-subset fails above `bound` produces a design whose every `(rank+1)`-subset
fails above `bound / (1 - spikeWeight)`.

The bound is not an estimate: the padded design's value is exactly
`min(1/spikeWeight, bound/(1 - spikeWeight))` when `bound` is the sub-design's
value (MEASURED at 90 digits, see the header), and the first branch of the
minimum binds only for spike weights so large that the padded design dominates
anyway.  Only `<=` is proved, which is all an upper bound on a rank constant
needs. -/
theorem spikePaddedDesign_valueAtMost (design : ComplexWeightedDesign size rank)
    {spikeWeight bound : ℝ} (hlow : 0 < spikeWeight) (hhigh : spikeWeight < 1)
    (hboundNonneg : 0 ≤ bound) (hvalue : ComplexDesignValueAtMost design bound) :
    ComplexDesignValueAtMost (spikePaddedDesign design hlow hhigh)
      (bound / (1 - spikeWeight)) := by
  classical
  have hgapPos : (0 : ℝ) < 1 - spikeWeight := by linarith
  intro subset hcard level habove hpsd
  have hlevelPos : 0 < level :=
    lt_of_le_of_lt (div_nonneg hboundNonneg hgapPos.le) habove
  rw [ComplexDominatesAtLevel, spikePaddedDesign_atom] at hpsd
  by_cases hlastMember : Fin.last size ∈ subset
  · -- the spike is present: test the excess on flat directions only
    set trimmedSubset := subset.erase (Fin.last size) with htrim
    have hlastGone : Fin.last size ∉ trimmedSubset := Finset.notMem_erase _ _
    obtain ⟨oldSubset, holdEq, holdCard⟩ := exists_preimage_of_last_notMem hlastGone
    have htrimCard : trimmedSubset.card = rank := by
      rw [htrim, Finset.card_erase_of_mem hlastMember, hcard]
      omega
    refine hvalue oldSubset (by rw [holdCard, htrimCard]) (level * (1 - spikeWeight))
      ((div_lt_iff₀ hgapPos).mp habove) ?_
    refine posSemidef_atomSum_sub_smul_one design oldSubset _ fun direction => ?_
    have hcover := covering_of_posSemidef_atomSum_sub_smul_one
      (spikePaddedAtom design spikeWeight) subset level hpsd
      (Fin.snoc direction 0 : Fin (rank + 1) → ℂ)
    rw [sumNormSq_snocZero, ← Finset.add_sum_erase _ _ hlastMember, ← htrim, holdEq,
      Finset.sum_map] at hcover
    have hspikeTerm : Complex.normSq (star (spikePaddedAtom design spikeWeight
        (Fin.last size)) ⬝ᵥ (Fin.snoc direction 0 : Fin (rank + 1) → ℂ)) = 0 := by
      rw [spikePaddedAtom_last, starDot_spikeAtom_snocZero, Complex.normSq_zero]
    rw [hspikeTerm, zero_add] at hcover
    have hscaled := mul_le_mul_of_nonneg_left hcover hgapPos.le
    have hrightSum : (1 - spikeWeight)
          * (∑ oldLabel ∈ oldSubset, Complex.normSq (star (spikePaddedAtom design spikeWeight
              (Fin.castSuccEmb oldLabel))
            ⬝ᵥ (Fin.snoc direction 0 : Fin (rank + 1) → ℂ)))
        = ∑ oldLabel ∈ oldSubset,
            Complex.normSq (star (design.atom oldLabel) ⬝ᵥ direction) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun oldLabel _ => ?_
      rw [Fin.castSuccEmb_apply, spikePaddedAtom_castSucc]
      exact normSq_starDot_flattenedAtom_snocZero hgapPos (design.atom oldLabel) direction
    rw [hrightSum] at hscaled
    calc level * (1 - spikeWeight) * ∑ coord, Complex.normSq (direction coord)
        = (1 - spikeWeight) * (level * ∑ coord, Complex.normSq (direction coord)) := by ring
      _ ≤ ∑ oldLabel ∈ oldSubset,
            Complex.normSq (star (design.atom oldLabel) ⬝ᵥ direction) := hscaled
  · -- the spike is absent: the whole subset is flat
    exact not_posSemidef_paddedAtomSum_sub_of_last_notMem design spikeWeight
      hlastMember hlevelPos hpsd

end PaddedValue

/-! # Part D. The rank ladder

`Gtz/Complex/AtomSplitting.lean` walks SIZE upward at fixed rank and fixed bound.
This part walks RANK upward, one atom and one dimension at a time, at a bound that
must strictly increase — and the strictness is real, not slack. -/

section RankLadder

/-- One rung, with the spike weight exposed. -/
theorem complexRankConstantAtMostAtSize_padded {size rank : ℕ} {bound : ℝ}
    (hboundNonneg : 0 ≤ bound) {spikeWeight : ℝ} (hlow : 0 < spikeWeight)
    (hhigh : spikeWeight < 1)
    (hwitness : ComplexRankConstantAtMostAtSize size rank bound) :
    ComplexRankConstantAtMostAtSize (size + 1) (rank + 1) (bound / (1 - spikeWeight)) := by
  obtain ⟨design, hvalue⟩ := hwitness
  exact ⟨spikePaddedDesign design hlow hhigh,
    spikePaddedDesign_valueAtMost design hlow hhigh hboundNonneg hvalue⟩

/-- **The padded bound is STRICTLY above the bound it came from**, at every
admissible spike weight.  So the ladder's infimum over spike weights is the
original bound and no member of the family attains it — the mechanism behind the
MEASURED non-attainment of the per-size infimum at `m = 3` and `m = 5`. -/
theorem paddedBound_gt_of_pos {bound spikeWeight : ℝ} (hboundPos : 0 < bound)
    (hlow : 0 < spikeWeight) (hhigh : spikeWeight < 1) :
    bound < bound / (1 - spikeWeight) := by
  have hgapPos : (0 : ℝ) < 1 - spikeWeight := by linarith
  rw [lt_div_iff₀ hgapPos]
  nlinarith

/-- **One rung, at any strictly larger level.**  Choosing the spike weight
`1 - bound/newBound` makes the padded bound exactly `newBound`. -/
theorem complexRankConstantAtMostAtSize_succ_of_gt {size rank : ℕ} {bound newBound : ℝ}
    (hboundPos : 0 < bound) (habove : bound < newBound)
    (hwitness : ComplexRankConstantAtMostAtSize size rank bound) :
    ComplexRankConstantAtMostAtSize (size + 1) (rank + 1) newBound := by
  have hnewPos : 0 < newBound := lt_trans hboundPos habove
  have hboundNe : bound ≠ 0 := ne_of_gt hboundPos
  have hnewNe : newBound ≠ 0 := ne_of_gt hnewPos
  set spikeWeight : ℝ := 1 - bound / newBound with hspike
  have hratioPos : 0 < bound / newBound := div_pos hboundPos hnewPos
  have hratioLtOne : bound / newBound < 1 := (div_lt_one hnewPos).mpr habove
  have hlow : 0 < spikeWeight := by rw [hspike]; linarith
  have hhigh : spikeWeight < 1 := by rw [hspike]; linarith
  have hgap : 1 - spikeWeight = bound / newBound := by rw [hspike]; ring
  have hlands : bound / (1 - spikeWeight) = newBound := by
    rw [hgap]
    field_simp
  have hrung := complexRankConstantAtMostAtSize_padded (bound := bound)
    hboundPos.le hlow hhigh hwitness
  rwa [hlands] at hrung

/-- **The ladder iterated.**  From one witness, a witness at every higher rank and
correspondingly larger size, at every level strictly above the original.  The
intermediate levels are bisected, so the induction never needs a geometric
estimate on the accumulated spike weights. -/
theorem complexRankConstantAtMostAtSize_rank_add {size rank : ℕ} {bound : ℝ}
    (hboundPos : 0 < bound) (hwitness : ComplexRankConstantAtMostAtSize size rank bound)
    (extra : ℕ) {newBound : ℝ} (habove : bound < newBound) :
    ComplexRankConstantAtMostAtSize (size + extra) (rank + extra) newBound := by
  induction extra generalizing newBound with
  | zero =>
      exact ⟨(Classical.choose hwitness),
        complexDesignValueAtMost_mono (le_of_lt habove) (Classical.choose_spec hwitness)⟩
  | succ predecessor inductiveStep =>
      have hmidLow : bound < (bound + newBound) / 2 := by linarith
      have hmidHigh : (bound + newBound) / 2 < newBound := by linarith
      have hmidPos : 0 < (bound + newBound) / 2 := lt_trans hboundPos hmidLow
      have hprevious := inductiveStep hmidLow
      have hstep := complexRankConstantAtMostAtSize_succ_of_gt hmidPos hmidHigh hprevious
      simpa only [Nat.add_succ] using hstep

end RankLadder

/-! # Part E. What the ladder lands

Three instantiations.  The first sharpens the repository's smallest rank-three
refutation by one atom, at a constant the repository already owns.  The second
mechanizes the recorded `(6,4)` value from a design that needs no `4 x 4`
determinant.  The third supplies an upper bound at every rank, superseding the
ledger line "ranks `>= 4` — PROVED-LOWER `1/k` and NOTHING ELSE HERE". -/

section Landings

/-- The `(5,3)` witness's bound IS the constant the repository already records for
its `(6,3)` padded witness: `alphaRankTwo / (1 - 1/10) = 20/9 - 20 sqrt 3/27`. -/
theorem paddedMargin_eq_scaledAlphaRankTwo :
    alphaRankTwo / (1 - 1 / 10) = paddedMarginRankThree := by
  have hsqrtPos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtSq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [alphaRankTwo, paddedMarginRankThree]
  field_simp
  nlinarith [hsqrtSq, hsqrtPos]

theorem alphaRankTwo_nonneg : 0 ≤ alphaRankTwo := by
  linarith [alphaRankTwo_window.1]

theorem paddedMargin_nonneg : 0 ≤ paddedMarginRankThree := by
  linarith [paddedMargin_window.1]

theorem paddedMargin_lt_one : paddedMarginRankThree < 1 := by
  linarith [paddedMargin_window.2]

/-- The `ℂ²` SIC as a size-aware rank-two witness. -/
theorem complexRankConstantAtMostAtSize_four_two :
    ComplexRankConstantAtMostAtSize 4 2 alphaRankTwo :=
  ⟨sicDesign, sicDesign_valueAtMost⟩

/-- **WEIGHTED `(5,3)` IS FALSE OVER ℂ**, at the exact margin
`20/9 - 20 sqrt 3/27 = 0.9392216240...`.  The design is the `ℂ²` SIC padded by a
single spike of weight `1/10`.

This is ONE ATOM BELOW every rank-three refutation the repository had: both the
shared-axis trine of `Gtz/Complex/SharpConstantLedger.lean` and the two-spike
`paddedDesign` of `Gtz/Complex/ComplexPadding.lean` sit at `m = 6`.  The mechanism
is that `paddedDesign` spends its two antipodal spikes `+- sqrt 10 e_2`, at weight
`1/20` each, on the SAME rank-one atom — `complexAtom` is blind to the sign — so
merging them into one spike of weight `1/10` changes no atom sum and saves an
atom.  The margin is unchanged, which is why the constant here is the one the
ledger already carries.

Not the record: the Hesse SIC's `3(1 - cos 2 pi / 9) = 0.7018666706...` is far
below, at `m = 9`.  This is the smallest SIZE at which complex weighted GTZ is
known here to fail at rank three, not the smallest VALUE. -/
theorem complexRankConstantAtMostAtSize_five_three :
    ComplexRankConstantAtMostAtSize 5 3 paddedMarginRankThree := by
  have hrung := complexRankConstantAtMostAtSize_padded (bound := alphaRankTwo)
    alphaRankTwo_nonneg (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (1 : ℝ) / 10 < 1)
    complexRankConstantAtMostAtSize_four_two
  rwa [paddedMargin_eq_scaledAlphaRankTwo] at hrung

theorem complexRankConstantAtMost_three_padded :
    ComplexRankConstantAtMost 3 paddedMarginRankThree :=
  complexRankConstantAtMost_of_atSize complexRankConstantAtMostAtSize_five_three

/-- The `(5,3)` refutation, and every larger size at rank three by atom splitting. -/
theorem complexRankConstantAtMostAtSize_three_padded (size : ℕ) (hsize : 5 ≤ size) :
    ComplexRankConstantAtMostAtSize size 3 paddedMarginRankThree :=
  complexRankConstantAtMostAtSize_of_le (by norm_num) paddedMargin_nonneg hsize
    complexRankConstantAtMostAtSize_five_three

/-- **Complex weighted GTZ fails at rank three from size five on.**  The repository
previously had this from size six (`complexGtzWeighted_six_three_fails`,
`complexGtzWeighted_six_three_fails_via_trine`) and, at the record margin, from
size nine (`not_complexGtzWeighted_three_of_nine_le`). -/
theorem not_complexGtzWeighted_three_of_five_le (size : ℕ) (hsize : 5 ≤ size) :
    ¬ ComplexGtzWeighted size 3 := by
  obtain ⟨design, hvalue⟩ := complexRankConstantAtMostAtSize_three_padded size hsize
  exact not_complexGtzWeighted_of_designValueAtMost paddedMargin_lt_one hvalue

/-- A tight enough rational cage on `alphaRankTwo` for the `(6,4)` certificate:
`2 - 2/sqrt 3 < 847/1000`, on `1153^2 * 3 = 3988227 < 4000000`. -/
theorem alphaRankTwo_lt_847_1000 : alphaRankTwo < 847 / 1000 := by
  have hsqrtPos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtSq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hsqrtUpper : Real.sqrt 3 < 2000 / 1153 := by nlinarith [hsqrtSq, hsqrtPos]
  rw [alphaRankTwo]
  rw [show (2 : ℝ) - 2 / Real.sqrt 3 < 847 / 1000 ↔ 1153 / 1000 < 2 / Real.sqrt 3 by
    constructor <;> intro hyp <;> linarith]
  rw [lt_div_iff₀ hsqrtPos]
  linarith

/-- **WEIGHTED `(6,4)` IS FALSE OVER ℂ, MECHANIZED**, at the level
`6/7 = exactValueRankFourAtSix`.

`Gtz/Complex/SharpConstantLedger.lean` records `6/7` as the exact `(6,4)` value
with the note that it is EXACT ELSEWHERE and "not mechanized here (Mathlib has no
`det_fin_four`)".  The witness used here is a different design — the `ℂ²` SIC
padded TWICE, at spike weight `1/200` each time — and the ladder never forms a
`4 x 4` determinant: positive semidefiniteness is transported by projections
throughout.  Its bound is `alphaRankTwo * (200/199)^2 = 0.8538162790...`, which
is below `6/7 = 0.8571428571...` with slack `0.0033265781`.  The spike weight is
not free: at `1/100` the same construction measures `0.8624624646`, ABOVE `6/7`,
so `alphaRankTwo_lt_847_1000` is doing real work. -/
theorem complexRankConstantAtMostAtSize_six_four :
    ComplexRankConstantAtMostAtSize 6 4 ((exactValueRankFourAtSix : ℚ) : ℝ) := by
  have hlow : (0 : ℝ) < 1 / 200 := by norm_num
  have hhigh : (1 : ℝ) / 200 < 1 := by norm_num
  have hshape : alphaRankTwo / (1 - 1 / 200) / (1 - 1 / 200)
      ≤ ((exactValueRankFourAtSix : ℚ) : ℝ) := by
    have hcast : ((exactValueRankFourAtSix : ℚ) : ℝ) = 6 / 7 := by
      rw [exactValueRankFourAtSix]
      norm_num
    rw [hcast, show ((1 : ℝ) - 1 / 200) = 199 / 200 by norm_num, div_div,
      div_le_iff₀ (by norm_num : (0 : ℝ) < 199 / 200 * (199 / 200))]
    nlinarith [alphaRankTwo_lt_847_1000]
  have hfirst := complexRankConstantAtMostAtSize_padded (bound := alphaRankTwo)
    alphaRankTwo_nonneg hlow hhigh complexRankConstantAtMostAtSize_four_two
  have honceNonneg : (0 : ℝ) ≤ alphaRankTwo / (1 - 1 / 200) :=
    div_nonneg alphaRankTwo_nonneg (by norm_num)
  obtain ⟨design, hvalue⟩ := complexRankConstantAtMostAtSize_padded
    (bound := alphaRankTwo / (1 - 1 / 200)) honceNonneg hlow hhigh hfirst
  exact ⟨design, complexDesignValueAtMost_mono hshape hvalue⟩

theorem not_complexGtzWeighted_four_of_six_le (size : ℕ) (hsize : 6 ≤ size) :
    ¬ ComplexGtzWeighted size 4 := by
  have hvalueNonneg : (0 : ℝ) ≤ ((exactValueRankFourAtSix : ℚ) : ℝ) := by
    rw [exactValueRankFourAtSix]; norm_num
  have hvalueLtOne : ((exactValueRankFourAtSix : ℚ) : ℝ) < 1 := by
    rw [exactValueRankFourAtSix]; norm_num
  obtain ⟨design, hvalue⟩ := complexRankConstantAtMostAtSize_of_le
    (by norm_num) hvalueNonneg hsize complexRankConstantAtMostAtSize_six_four
  exact not_complexGtzWeighted_of_designValueAtMost hvalueLtOne hvalue

/-- **The rank-four ceiling descends to the rank-three record.**  For every level
strictly above `3(1 - cos 2 pi / 9)` there is a complex weighted `(10,4)`-design
no `4`-subset of which survives above it — so `alpha_4 <= alpha_3`'s recorded
value, approached and, along this family, never attained
(`paddedBound_gt_of_pos`).

This is the correct reading of `Gtz/Complex/SharpConstantLedger.lean`'s
`measuredRankFourUncapped = 0.701866670643`, whose recorded attribution — a
rank-four design at `m = 10` with leverage cap `2.69` — cannot produce that
number: the ladder produces it only as a limit of increasing leverage. -/
theorem complexRankConstantAtMostAtSize_ten_four_of_gt {bound : ℝ}
    (habove : hesseMarginRankThree < bound) :
    ComplexRankConstantAtMostAtSize 10 4 bound := by
  have hhessePos : 0 < hesseMarginRankThree := by linarith [hesseMargin_window.1]
  exact complexRankConstantAtMostAtSize_succ_of_gt hhessePos habove
    complexRankConstantAtMostAtSize_nine_hesse

/-- **AN UPPER BOUND AT EVERY RANK.**  For every `rank >= 3` and every level
strictly above `3(1 - cos 2 pi / 9)`, there is a complex weighted design of rank
`rank` — on `rank + 6` atoms, the `(rank - 3)`-fold padded Hesse SIC — no
`rank`-subset of which survives above that level.  Hence
`alpha_rank <= 3(1 - cos 2 pi / 9)` for every `rank >= 3`, in the first-order form
an infimum admits.

`Gtz/Complex/PerRankConstantLedger.lean` records "ranks `>= 4` — PROVED-LOWER
`1/k` and NOTHING ELSE HERE.  No rank-4 or rank-5 design is mechanized anywhere in
this repository."  That line is superseded by this theorem and by
`complexRankConstantAtMostAtSize_six_four`. -/
theorem complexRankConstantAtMostAtSize_three_le_rank (extra : ℕ) {bound : ℝ}
    (habove : hesseMarginRankThree < bound) :
    ComplexRankConstantAtMostAtSize (9 + extra) (3 + extra) bound := by
  have hhessePos : 0 < hesseMarginRankThree := by linarith [hesseMargin_window.1]
  exact complexRankConstantAtMostAtSize_rank_add hhessePos
    complexRankConstantAtMostAtSize_nine_hesse extra habove

theorem complexRankConstantAtMost_three_le_rank (rank : ℕ) (hrank : 3 ≤ rank) {bound : ℝ}
    (habove : hesseMarginRankThree < bound) :
    ComplexRankConstantAtMost rank bound := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hrank
  exact complexRankConstantAtMost_of_atSize
    (complexRankConstantAtMostAtSize_three_le_rank extra habove)

/-- **Complex weighted GTZ is FALSE at every rank at least two**, with an explicit
size at each rank: `m = 4` at rank two (the `ℂ²` SIC), `m = 9 + e` at rank
`3 + e` (the `e`-fold padded Hesse SIC).  Over ℝ the same statement is a theorem only at
`k <= 2` and OPEN for `k >= 3`, so this is the sharpest form of the field
separation the repository can state. -/
theorem not_complexGtzWeighted_of_two_le_rank (rank : ℕ) (hrank : 2 ≤ rank) :
    ∃ size : ℕ, ¬ ComplexGtzWeighted size rank := by
  rcases Nat.lt_or_ge rank 3 with hsmall | hlarge
  · have hrankTwo : rank = 2 := by omega
    subst hrankTwo
    exact ⟨4, complexGtzWeighted_four_fails⟩
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hlarge
    have hhesseLtNine : hesseMarginRankThree < 9 / 10 := by
      linarith [hesseMargin_window.2]
    obtain ⟨design, hvalue⟩ :=
      complexRankConstantAtMostAtSize_three_le_rank (bound := 9 / 10) extra hhesseLtNine
    exact ⟨9 + extra,
      not_complexGtzWeighted_of_designValueAtMost (by norm_num) hvalue⟩

end Landings

/-! # Part F. The sharp forms, and the smallest refutable size

Part E quotes CONCRETE constants at `(5,3)` and `(6,4)` because those are the two
the repository already owned.  Neither is what the ladder delivers.  Feeding the
rank-two witness straight to `complexRankConstantAtMostAtSize_rank_add` gives, at
EVERY rank at once and at the smallest size any equal-weight argument permits,
every level strictly above `alphaRankTwo` — an 11% improvement on the quoted
`(5,3)` constant and a 1.4% one on `(6,4)`.

The strictness is forced, not slack.  MEASURED at 90 digits: the per-size infimum
at both `(5,3)` and `(6,4)` is `alphaRankTwo` itself, reached only as a spike
limit, so `ComplexRankConstantAtMostAtSize 5 3 alphaRankTwo` is expected to be
FALSE while every level above it holds.  `paddedBound_gt_of_pos` is the proved
half of that picture. -/

section MinimalSize

theorem alphaRankTwo_pos : 0 < alphaRankTwo := by
  linarith [alphaRankTwo_window.1]

/-- **THE RANK-TWO LADDER, AT EVERY RANK AND THE SMALLEST SIZE.**  For every
`extra` and every level strictly above `alphaRankTwo = 2 - 2/sqrt 3`, there is a
complex weighted `(4 + extra, 2 + extra)`-design no `(2 + extra)`-subset of which
survives above it: the `ℂ²` SIC padded `extra` times.

Size is `rank + 2` at every rank, which is the smallest size that can possibly
work: `Gtz/Complex/SharpConstantLedger.lean` records that at EQUAL weights
`m = k + 1` is exactly tight at `1` (Naimark dual `(k+1,1)` plus
max-at-least-mean), so `m = k + 2` is the first refutable equal-weight size.  The
weighted `m = k + 1` case is no longer open and no longer a spike limit: it is
PROVED by `Gtz.complexGtzWeighted_corank_one` (`Gtz/Complex/SizeAxis.lean`), and
the value `1` there IS ATTAINED, at every admissible weight vector
(`Gtz.exists_complexDesign_exactlyTied`).  The spike limit sits one cell lower,
at `m = k`, where the frame is unitary and `lambda_min(S_univ) = 1 / max_c t_c`.
Both halves of the sentence this paragraph replaces were false; the older
MEASURED entry "the infimum at size = rank + 1 is 1 and never attained" is
refuted over BOTH fields. -/
theorem complexRankConstantAtMostAtSize_two_le_rank (extra : ℕ) {bound : ℝ}
    (habove : alphaRankTwo < bound) :
    ComplexRankConstantAtMostAtSize (4 + extra) (2 + extra) bound :=
  complexRankConstantAtMostAtSize_rank_add alphaRankTwo_pos
    complexRankConstantAtMostAtSize_four_two extra habove

/-- The `(5,3)` rung in its sharp form: not the single constant
`paddedMarginRankThree`, but every level above `alphaRankTwo`, which is `11%`
lower. -/
theorem complexRankConstantAtMostAtSize_five_three_of_gt {bound : ℝ}
    (habove : alphaRankTwo < bound) :
    ComplexRankConstantAtMostAtSize 5 3 bound :=
  complexRankConstantAtMostAtSize_two_le_rank 1 habove

/-- The `(6,4)` rung in its sharp form: every level above `alphaRankTwo`, which is
below the recorded `6/7` and therefore strictly stronger than
`complexRankConstantAtMostAtSize_six_four`. -/
theorem complexRankConstantAtMostAtSize_six_four_of_gt {bound : ℝ}
    (habove : alphaRankTwo < bound) :
    ComplexRankConstantAtMostAtSize 6 4 bound :=
  complexRankConstantAtMostAtSize_two_le_rank 2 habove

/-- A rational level strictly between `alphaRankTwo` and `6/7`, which is what
turns the sharp `(6,4)` form into a strict-undercut statement. -/
theorem alphaRankTwo_lt_seventeen_twentieths : alphaRankTwo < 17 / 20 := by
  linarith [alphaRankTwo_lt_847_1000]

/-- **`6/7` IS NOT THE `(6,4)` INFIMUM.**  `Gtz/Complex/SharpConstantLedger.lean`
opens its `exactValueRankFourAtSix` docstring with "the exact `(6,4)` value over
ℂ", and its minimality hedge is EQUAL-WEIGHT ONLY.  Under the design-independent
reading the opening phrase does not survive: the ladder exhibits a genuine
`(6,4)`-design strictly below `6/7`.  So `6/7` is the exact value OF THE RECORDED
NAIMARK-DUAL DESIGN, not the infimum over weighted `(6,4)`-designs — which is what
`ComplexRankConstantAtMostAtSize` quantifies.

MEASURED at 90 digits, the ladder's own witness at spike weight `1/200` sits at
`0.85381627900381149060044184641407`, below `6/7 = 0.857142857...` by
`0.0033265781`; the level certified here is the rational `17/20`, comfortably
between the two. -/
theorem ladderUndercuts_exactValueRankFourAtSix :
    ∃ bound : ℝ, bound < ((exactValueRankFourAtSix : ℚ) : ℝ)
      ∧ ComplexRankConstantAtMostAtSize 6 4 bound := by
  have hcast : ((exactValueRankFourAtSix : ℚ) : ℝ) = 6 / 7 := by
    rw [exactValueRankFourAtSix]
    norm_num
  refine ⟨17 / 20, ?_, complexRankConstantAtMostAtSize_six_four_of_gt
    alphaRankTwo_lt_seventeen_twentieths⟩
  rw [hcast]
  norm_num

/-- The same undercut at `(5,3)`: `paddedMarginRankThree` is the value of ONE
five-atom design, not the `(5,3)` infimum. -/
theorem ladderUndercuts_paddedMarginRankThree :
    ∃ bound : ℝ, bound < paddedMarginRankThree
      ∧ ComplexRankConstantAtMostAtSize 5 3 bound :=
  ⟨17 / 20, by linarith [paddedMargin_window.1],
    complexRankConstantAtMostAtSize_five_three_of_gt alphaRankTwo_lt_seventeen_twentieths⟩

/-- **COMPLEX WEIGHTED GTZ IS FALSE AT EVERY RANK AT LEAST TWO AND EVERY SIZE AT
LEAST `rank + 2`.**  This supersedes both of the size bounds this file's Part E
lands: `not_complexGtzWeighted_of_two_le_rank` produces size `rank + 6` (the
Hesse-seeded ladder), and the rank-three and rank-four statements produce `5` and
`6` one rank at a time.  Here every rank gets `rank + 2` at once, and `rank + 2`
is the smallest size an equal-weight argument leaves available. -/
theorem not_complexGtzWeighted_of_rank_add_two_le_size (size rank : ℕ) (hrank : 2 ≤ rank)
    (hsize : rank + 2 ≤ size) : ¬ ComplexGtzWeighted size rank := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hrank
  have hbase : ComplexRankConstantAtMostAtSize (4 + extra) (2 + extra) (9 / 10) :=
    complexRankConstantAtMostAtSize_two_le_rank extra
      (by linarith [alphaRankTwo_window.2])
  have hgrown : ComplexRankConstantAtMostAtSize size (2 + extra) (9 / 10) :=
    complexRankConstantAtMostAtSize_of_le (by omega) (by norm_num) (by omega) hbase
  obtain ⟨design, hvalue⟩ := hgrown
  exact not_complexGtzWeighted_of_designValueAtMost (by norm_num) hvalue

end MinimalSize

/-! # Part G. The ladder, assembled

One statement carrying everything this file proves, with nothing measured or cited
smuggled in. -/

/-- **THE PADDING LADDER, ASSEMBLED.**

* the brick: padding multiplies a design's value bound by `1/(1 - spikeWeight)`
  and nothing else;
* the rung: a witness at `(size, rank)` at a positive level gives one at
  `(size+1, rank+1)` at any strictly larger level, and the increase is genuine —
  the padded bound is strictly above its source at every admissible spike weight;
* `(5,3)` is FALSE over ℂ at `20/9 - 20 sqrt 3/27`, one atom below the shipped
  `(6,3)` refutations;
* `(6,4)` is FALSE over ℂ, the first kernel-checked rank-four refutation in this
  repository, from a design that never needs a `4 x 4` determinant.  The level
  quoted is the recorded rational `6/7`, used here as a CAGE and not as an
  attained value — the witness sits strictly below it (see Part F);
* every rank `>= 3` has an upper bound arbitrarily close to the rank-three record
  `3(1 - cos 2 pi / 9)`;
* complex weighted GTZ is FALSE at every rank `>= 2`.

The proved rank-three window is unmoved: `1/3 <= alpha_3 <= 3(1 - cos 2 pi / 9)`.
This file lowers the CEILING at ranks four and above and shrinks the SIZE at which
rank three is refuted; it does not touch the floor at any rank. -/
theorem complexPaddingLadder :
    (∀ (size rank : ℕ) (design : ComplexWeightedDesign size rank) (spikeWeight bound : ℝ)
        (hlow : 0 < spikeWeight) (hhigh : spikeWeight < 1), 0 ≤ bound →
      ComplexDesignValueAtMost design bound →
      ComplexDesignValueAtMost (spikePaddedDesign design hlow hhigh)
        (bound / (1 - spikeWeight)))
      ∧ (∀ bound spikeWeight : ℝ, 0 < bound → 0 < spikeWeight → spikeWeight < 1 →
          bound < bound / (1 - spikeWeight))
      ∧ ComplexRankConstantAtMostAtSize 5 3 paddedMarginRankThree
      ∧ ComplexRankConstantAtMostAtSize 6 4 ((exactValueRankFourAtSix : ℚ) : ℝ)
      ∧ (∀ (rank : ℕ), 3 ≤ rank → ∀ bound : ℝ, hesseMarginRankThree < bound →
          ComplexRankConstantAtMost rank bound)
      ∧ (∀ rank : ℕ, 2 ≤ rank → ∃ size : ℕ, ¬ ComplexGtzWeighted size rank) :=
  ⟨fun _ _ design _ _ hlow hhigh hboundNonneg hvalue =>
      spikePaddedDesign_valueAtMost design hlow hhigh hboundNonneg hvalue,
    fun _ _ hboundPos hlow hhigh => paddedBound_gt_of_pos hboundPos hlow hhigh,
    complexRankConstantAtMostAtSize_five_three,
    complexRankConstantAtMostAtSize_six_four,
    fun rank hrank _ habove => complexRankConstantAtMost_three_le_rank rank hrank habove,
    not_complexGtzWeighted_of_two_le_rank⟩

/-- **THE LADDER AT ITS SHARP LEVEL AND SMALLEST SIZE.**  What Part F adds to the
statement above, and what the two quoted constants of Part E were hiding:

* every rank `>= 2` is refuted at size exactly `rank + 2` — the smallest size the
  equal-weight tightness of `m = k + 1` leaves available — and at every larger
  size;
* the level is every real strictly above `alphaRankTwo = 2 - 2/sqrt 3`, at
  `(5,3)` and `(6,4)` alike, so the concrete constants `20/9 - 20 sqrt 3/27` and
  `6/7` of Part E overshoot by `11%` and `1.4%`;
* consequently `6/7` is NOT the infimum over weighted `(6,4)`-designs, and
  `20/9 - 20 sqrt 3/27` is not the infimum over weighted `(5,3)`-designs.  Each is
  the value of one particular design.

MEASURED at 90 digits, the strictness is forced rather than slack: the per-size
infimum at `(5,3)` and at `(6,4)` is `alphaRankTwo` itself, reached only as a
spike limit. -/
theorem complexPaddingLadderAtMinimalSize :
    (∀ (extra : ℕ) (bound : ℝ), alphaRankTwo < bound →
        ComplexRankConstantAtMostAtSize (4 + extra) (2 + extra) bound)
      ∧ (∀ (size rank : ℕ), 2 ≤ rank → rank + 2 ≤ size → ¬ ComplexGtzWeighted size rank)
      ∧ (∃ bound : ℝ, bound < ((exactValueRankFourAtSix : ℚ) : ℝ)
          ∧ ComplexRankConstantAtMostAtSize 6 4 bound)
      ∧ (∃ bound : ℝ, bound < paddedMarginRankThree
          ∧ ComplexRankConstantAtMostAtSize 5 3 bound) :=
  ⟨fun extra _ habove => complexRankConstantAtMostAtSize_two_le_rank extra habove,
    not_complexGtzWeighted_of_rank_add_two_le_size,
    ladderUndercuts_exactValueRankFourAtSix,
    ladderUndercuts_paddedMarginRankThree⟩

/-! ## SCOPE NOTE: the three open questions, answered by tag

**Q1 — ATTAINMENT AND SHARPNESS of `alpha_3 = 3(1 - cos 2 pi / 9)`.**
PROVED: the Hesse SIC ATTAINS its margin (`hesseMargin_isGreatest`, in
`Gtz/Complex/HesseMarginAttained.lean`), and the record is realised at every size
`>= 9` (`complexRankConstantAtMostAtSize_three_hesse`).  PROVED HERE: complex
weighted `(m,3)` is false from `m = 5` on — and more generally `(m,k)` is false
for every `k >= 2` from `m = k + 2` on
(`not_complexGtzWeighted_of_rank_add_two_le_size`) — so the interesting range for
the size profile is `m <= 4`, and at rank `k` it is `m <= k + 1`, which the
ledger's equal-weight tightness argument already closes at equal weights.
MEASURED, and the qualifier matters: no design below
the Hesse value was found at any size in `3 .. 16`, at rank three, four or five,
across two independently seeded multi-start searches.  A RESTART COUNT IS NOT A
COVERAGE MEASURE — the Hesse basin has small measure, and one of the two seed
sets failed to enter it at all at `m = 9,10`, reporting the trine level
`3 - sqrt 5` instead.  What both searches agree on is the NEGATIVE (nothing
below), not the per-size minimum.  The profile is `1` at `m = 3,4`,
`2 - 2/sqrt 3` at `m = 5`, `3 - sqrt 5` at `m = 6,7,8`, and the Hesse value from
`m = 9`.  OPEN: whether the Hesse value is the INFIMUM.  Nothing in this file or
any other in this repository bears on that; every rank-three statement here is an
upper bound.  CORRECTED: the per-size infimum is NOT always attained — `m = 3`
and `m = 5` are spike limits, and `paddedBound_gt_of_pos` is the proved form of
why the family that produces them never reaches its own limit.

**Q2 — RIGIDITY at the optimal size.**  OPEN, untouched here, and the evidence
grade is LOWER than an earlier draft of this note recorded.  What survives two
independent implementations of perturb-and-reconverge is the GEOMETRY, not the
orbit count: every run returning to the record value returns to uniform weights
`~ 1/9`, leverages `~ 3`, pair overlap moduli `~ 9/4`.  The stronger reading —
that those runs form a SINGLE gauge orbit — is NOT established.  The classifier is
a fingerprint rounded at a fixed number of digits, and near the optimizer's
convergence floor (`~ 1e-5`) an independent reimplementation could not
discriminate orbits at all: its `m = 12` positive control, where atom splitting
predicts several orbits at one value, returned a single degenerate point, so the
control FAILED and the classifier is unvalidated at that tolerance.  Rigidity is
therefore NEITHER CONFIRMED NOR REFUTED; a reproducible claim needs the
convergence and rounding tolerances stated and a positive control that passes.

The measured Hesse geometry itself is solid and reproduces across
implementations: seventy-two active triples and twelve singular ones (the twelve
lines of the Hesse configuration), one weight, one overlap modulus `9/4`, two
Bargmann real parts `-27/8` and `+27/16` — the second being exactly the cap
`hesseTriple_bargmann_re_le` proves.  CITED: at rank two rigidity is a theorem
(Nesterenko, arXiv:2604.24087, Proposition 1: equality iff `4 | m` and the Hopf
images form a regular tetrahedron).  No rank-three analogue exists in the
literature, over either field.

**Q3 — THE FLOOR.**  UNMOVED.  `alpha_3 >= 1/3` remains the proved lower end.
This file adds nothing to it, and — this is the honest reading of the campaign's
own experiment stage — the constant `(7 - sqrt 34)/3` of
`Gtz/Complex/AttainmentRankThree.lean` is a named constant with proved arithmetic,
not a proved floor.  Its derivation's steps 5-9 are stated in that file's header,
validated numerically off-repo, and NOT mechanized; nothing in this repository
assumes them.  The single named unproved hypothesis remains: *at a maximal-volume
pick with `lambda_min < (7 - sqrt 34)/3`, one of the three exchanges against the
covering atom already reaches that level.*  Two further facts bound the search:
the maximal-volume selection ALONE is capped at exactly `1/k` (that file's exact
rational `(4,3)` witness), so a better floor needs a better SELECTION and not a
better estimate; and the Cauchy-Binet averaged-minor route, which in the
uniform-weight normalisation would give the smallest root of the Laguerre
polynomial `L_3` (`0.4157745568`, root of `x^3 - 9x^2 + 18x - 6`), degrades BELOW
`1/3` in the weighted normalisation this repository uses, because
`e_2(t)` and `e_3(t)` are not bounded below over the weight simplex.  Neither
observation is mechanized; both are recorded so the next attempt does not
re-derive them. -/

end Gtz

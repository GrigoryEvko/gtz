/-
# The bounded-radius exchange route is REFUTED at rank three

`Gtz.Reduction.ExchangeRepair` mechanizes local search on the `k`-subsets: its
`gtzWeighted_of_exchangeImproves` turns "some real-valued score strictly increases at
every non-dominating `k`-subset" into weighted GTZ, and its repair lemmas show that a
subset failing in a direction `w` always admits an outside atom whose insertion repairs
`w` exactly. Its header records the operative hope — that repairing the worst direction
could be assembled into monotone progress inside a BOUNDED exchange radius, with
radius `2` measured to have "ZERO failures over ~53000 random failing subsets".

**That hope is false, and this file kills it.** The measurement was a sampling artifact:
the stuck set is not a thin tie locus but an OPEN subset of the all-heavy Parseval design
manifold, which random sampling of designs simply never enters.

## What is proved

`radiusTwoStuckDesign` is an exact rational all-heavy `(6,3)` design at which the
`3`-subset `{0, 1, 2}` FAILS to dominate, yet no `3`-subset at exchange distance `≤ 2`
has a strictly larger least eigenvalue. Since radius `3 = k` is vacuous
(`exchangeImprovesWithinRadius_iff_unbounded_of_rank_le` — every `k`-subset lies within
distance `k` of every other, so radius-`k` local search IS global search), every
NON-TRIVIAL radius is refuted at rank three:

  * `radiusTwoStuckSubset_isExchangeStuck` — the stuck subset, with the exchange-distance
    predicate spelled out;
  * `not_exchangeImprovesWithinRadius_two_rankThree` and its monotone corollary
    `not_exchangeImprovesWithinRadius_of_le_two_rankThree` — radius `1` and radius `2`
    both fail at `(6,3)`.

Rank three is not an aside: it is the live frontier object of the campaign.

The design still SATISFIES GTZ — `radiusTwoStuckDesign_dominates_axisTriple` exhibits
`{3, 4, 5}` with atom sum `4·I`. What dies is the route, not the conjecture. The
dominating subset sits at exchange distance exactly `3`.

## Why the certificates are exact

Every blocking step is a RAYLEIGH CERTIFICATE at a coordinate vector, evaluated in exact
rational arithmetic — never a numeric eigenvalue bound, and not even a characteristic-
coefficient sign test. For each of the eighteen neighbours some coordinate `p` has
`(S_{C})_{pp} ≤ 512/625`, so `λ_min(S_C) ≤ 512/625` by `lambdaMinMat_le_diagonal`, while
the stuck subset has `S = diag(576/625, 576/625, 729/400)` hence
`576/625 ≤ λ_min` by `le_lambdaMinMat_of_forall`. The certificate margin is exactly
`576/625 − 512/625 = 64/625`, and it is sharp for coordinate vectors: two of the eighteen
(`{0,1,3}` at `p = 1`, `{0,2,4}` at `p = 0`) attain `512/625` exactly, so no coordinate
certificate can do better — but neither is a tie, and the true gap is wider still. The
best neighbour's actual least eigenvalue is `0.70117322194026545646` (at `{1,3,4}` and
`{2,3,4}`, 80-digit `mpmath.eigsy` cross-check, not a logical step), so the real deficit
is `≈ +0.2204` against the stuck subset's `0.9216`.

## The mechanism, and why the ceiling makes radius 2 look safe at rank 3

`rank_lt_trace_subsetSum_of_allHeavy` is the only place all-heaviness is used: it gives
`trace(S_C) > k`, so the TOP eigenvalue of a failing all-heavy `k`-subset exceeds `1` and
the bottom eigenvalue cannot have multiplicity `k`. Combined with the Cauchy interlacing
ceiling `λ_min(S_{C'}) ≤ λ_{r+1}(S_C)` whenever `|C' \ C| ≤ r` (three lines: the span of
the bottom `r+1` eigenvectors meets the orthogonal complement of the `r` incoming atoms,
and a vector there is killed by every incoming term while sitting in the bottom
eigenspace — NOT mechanized here, it needs eigenvalue indexing Mathlib does not package
for this shape), multiplicity blocks radii `1 … k-2` and leaves `k-1 = 2` open at rank
three. That is exactly why radius 2 looked safe.

The witness bypasses the multiplicity mechanism entirely. Its stuck subset is
NEAR-ORTHONORMAL and BARELY HEAVY — spectrum `(576/625, 576/625, 729/400)`, bottom
multiplicity only `2`, leverages `10217/10000, 661/500, 661/500` just above `1` — while
the three outside atoms are scaled coordinate axes. Dropping any atom of a
near-orthonormal triple destroys a whole direction at constant cost, whereas the spread
of the subset Gram is small; so the cost of any bounded exchange dominates the gain. No
degeneracy is used, which is why the stuck set is open rather than measure-zero.

## Measured status (numerics, NOT proof; reproduce before trusting)

Recorded here because the same numbers previously supported the FALSE conjecture, and
the record of how they misled is part of the result. None of this is a theorem.

  * Robustness of this witness: gaussian noise on atoms plus log-normal noise on weights,
    re-whitened to exact Parseval with admissibility re-checked — `400/400` perturbed
    designs still stuck at noise `1e-3` (spectral gap `~0.2`), `269/270` at `1e-2`. An
    independent `(9,3)` witness survives `3000/3000` trials at noise `1e-8 … 1e-3`,
    `99.97%` at `1e-2`, `76.5%` at `3e-2`. The stuck set has POSITIVE MEASURE.
  * The blind spot that produced the false conjecture: at generic failing subsets the
    bottom spectral gap `λ₂ − λ₁` has median `~2.5` and 1st percentile `~0.39`; `0` of
    `10580` sampled failing subsets at `(6,3)` had gap below `1e-3`.  Random sampling
    RARELY — not never — reaches the phenomenon: an independent audit census found `1`
    of `17864` below `1e-3` at `(8,4)`, and found a genuine radius-`2` stuck failing
    subset BY CHANCE at `(8,4)` (design #196, subset `{1,2,4,6}`, `λ_min = 0.9202526`,
    best neighbour `0.9091594` at `{2,4,6,7}`, margin `0.011093` identical at 60 and
    120 digits).  Rate roughly `1e-5` per subset.  That witness ALSO refutes the
    small-spectral-gap story: its bottom gap is `0.2627`, not small, and its leverage
    spread is large.  So there are at least TWO mechanisms — near-identity (below) and
    leverage spread — and only the first is characterized here.
  * Radius sweep on an exact rational family, ranks `2 … 5`, every check exact: stuck at
    every radius `r ≤ k-1`, improving exactly at `r = k`. At rank `2` — where GTZ is a
    PROVEN theorem (Sengupta–Pautov, `Gtz.Reduction.RankTwo`) — the `(5,2)` member has
    all `6` radius-`1` neighbours blocked with deficit `+0.2612`. Bounded-radius exchange
    on `λ_min` was never the mechanism, even where the conjecture is a theorem.
  * Score specificity, stated honestly: on the `(7,3)` sibling witness `λ_min` is stuck
    by `+0.3089` while `−tr(S⁻¹)` improves by `−0.4785` and `log det` improves by
    `−1.9706`. The refutation is specific to `λ_min` — which is exactly what `Dominates`
    needs (`dominates_iff_one_le_leastEigenvalue`). For the other scores the campaign's
    existing kills stand: the barrier potential was measured stuck, and `D`-optimal
    selection fails on `0.33%` of designs.
  * Optimizers named: SLSQP epigraph minimax with analytic Jacobians and Parseval as
    exact equality constraints reaches deficit `+0.6315` at `(6,3)` and `+0.6314` with
    leverage capped at `4`; Nelder–Mead STALLS on this nonsmooth max at `1e-4 … 1e-5`
    returning bit-identical values and must not be used. Cross-checks at 60 and 80
    decimal digits via `mpmath.eigsy`; every logical step re-done over `Fraction`,
    because on the sibling `(7,3)` tie-locus design a 60-digit float call reported one
    neighbour strictly above `μ` where exact Sylvester and exact Descartes both reported
    not-above. Floats decide nothing here.

## What survives in `ExchangeRepair`

`exists_atom_covering_direction`, `atom_mem_failing_lt`, `coveringAtom_notMem_of_failing`,
`swap_repairs_direction` and `exists_swap_repairing_worstDirection` are untouched and
correct — they are statements about ONE direction, and this witness is the explicit
realization of the gap that file's own docstring names ("repairing `w` may open a
different direction"). `ExchangeImproves` as DEFINED there carries no radius bound, and
at `score = λ_min` it is exactly equivalent to `GtzWeighted`
(`exchangeImproves_leastEigenvalue_iff_gtzWeighted`): the reduction is a theorem whose
hypothesis is a restatement of its conclusion. All of the route's content lay in
producing a bounded-radius witness, and every radius below the rank is now refuted.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.MarginContinuity
import Gtz.Reduction.ExchangeRepair
import Gtz.Reduction.LiftingLemma
import Gtz.Reduction.RayleighCertificate
import Gtz.Reduction.Reductions
import Gtz.Ties.SelectionObstruction

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false

namespace Gtz

open Matrix

/-! ## Exchange distance on equal-size subsets

The vocabulary the conjecture is stated in. For subsets of equal cardinality
`(target \ source).card` is half the symmetric difference and is symmetric; the swap of
`Gtz.exists_swap_repairing_worstDirection` has distance exactly `1`. -/

variable {m k : ℕ}

/-- **Exchange distance**: the number of atoms `target` gains relative to `source`.
On equal-cardinality subsets this is `|source Δ target| / 2`, the number of swaps needed
to turn one into the other. -/
def exchangeDistance (source target : Finset (Fin m)) : ℕ :=
  (target \ source).card

/-- A subset is at distance zero from itself. -/
theorem exchangeDistance_self (subset : Finset (Fin m)) :
    exchangeDistance subset subset = 0 := by
  rw [exchangeDistance, Finset.sdiff_self]
  rfl

/-- Distance is bounded by the size of the target, so a `k`-subset is within distance
`k` of every other `k`-subset — this is what makes radius `k` vacuous. -/
theorem exchangeDistance_le_card (source target : Finset (Fin m)) :
    exchangeDistance source target ≤ target.card :=
  Finset.card_le_card Finset.sdiff_subset

/-- **Distance is symmetric at equal cardinality**: both sides equal
`card − |source ∩ target|`. The hypothesis is needed — `(target \ source).card` alone is
not symmetric. -/
theorem exchangeDistance_comm_of_card_eq {source target : Finset (Fin m)}
    (hcard : source.card = target.card) :
    exchangeDistance source target = exchangeDistance target source := by
  have hsourceSplit := Finset.card_sdiff_add_card_inter source target
  have htargetSplit := Finset.card_sdiff_add_card_inter target source
  rw [Finset.inter_comm] at htargetSplit
  rw [exchangeDistance, exchangeDistance]
  omega

/-- At equal cardinality, distance zero means equality. -/
theorem exchangeDistance_eq_zero_iff_of_card_eq {source target : Finset (Fin m)}
    (hcard : source.card = target.card) :
    exchangeDistance source target = 0 ↔ source = target := by
  constructor
  · intro hzero
    rw [exchangeDistance, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hzero
    exact (Finset.eq_of_subset_of_card_le hzero (le_of_eq hcard)).symm
  · rintro rfl
    exact exchangeDistance_self source

/-- **The repair lemma's swap has distance exactly one.** Dropping a member and
inserting a non-member changes the subset by a single atom, which is the whole point of
calling it a swap; `Gtz.card_swap_eq_card` records that the cardinality is unchanged. -/
theorem exchangeDistance_swap_eq_one {selected : Finset (Fin m)}
    {coveringAtom droppedAtom : Fin m} (hnotMem : coveringAtom ∉ selected) :
    exchangeDistance selected (insert coveringAtom (selected.erase droppedAtom)) = 1 := by
  have hgained : insert coveringAtom (selected.erase droppedAtom) \ selected
      = {coveringAtom} := by
    ext element
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨hisCovering | ⟨_, hmemSelected⟩, hnotSelected⟩
      · exact hisCovering
      · exact absurd hmemSelected hnotSelected
    · rintro rfl
      exact ⟨Or.inl rfl, hnotMem⟩
  rw [exchangeDistance, hgained, Finset.card_singleton]

/-! ## The least eigenvalue as a score

`Gtz.lambdaMinMat` (`Gtz.Quantitative.MarginContinuity`) is the campaign's least
eigenvalue, defined as the Rayleigh infimum over nonzero vectors. Two bounds are all the
refutation needs: a Rayleigh lower bound and the coordinate-vector upper bound. -/

/-- **Rayleigh lower bound**: a uniform quadratic-form bound is a lower bound on
`λ_min`. -/
theorem le_lambdaMinMat_of_forall {dim : ℕ} [Nonempty (Fin dim)]
    (target : Matrix (Fin dim) (Fin dim) ℝ) {bound : ℝ}
    (hform : ∀ direction : Fin dim → ℝ,
      bound * (direction ⬝ᵥ direction) ≤ direction ⬝ᵥ (target *ᵥ direction)) :
    bound ≤ lambdaMinMat target := by
  rw [lambdaMinMat, lambdaMinCLM]
  refine le_ciInf fun nonzeroDirection => ?_
  rw [rayleigh_toEuclideanCLM_eq]
  have hnormPos : 0 < ‖(nonzeroDirection : EuclideanSpace ℝ (Fin dim))‖ ^ 2 := by
    have hnonzero := nonzeroDirection.2
    positivity
  rw [le_div_iff₀ hnormPos, euclid_norm_sq_eq_dotProduct]
  exact hform _

/-- **The coordinate certificate**: `λ_min` never exceeds a diagonal entry, because the
coordinate vector is a unit vector whose Rayleigh value is that entry. This is the only
upper bound the refutation uses, and it is exact rational arithmetic at every neighbour. -/
theorem lambdaMinMat_le_diagonal {dim : ℕ} [Nonempty (Fin dim)]
    (target : Matrix (Fin dim) (Fin dim) ℝ) (coordinate : Fin dim) :
    lambdaMinMat target ≤ target coordinate coordinate := by
  have hnonzero : (EuclideanSpace.single coordinate (1 : ℝ)) ≠ 0 := by
    intro hzero
    have hentry : (EuclideanSpace.single coordinate (1 : ℝ)) coordinate
        = (0 : EuclideanSpace ℝ (Fin dim)) coordinate := by rw [hzero]
    simp at hentry
  have hrayleigh := ciInf_le (rayleigh_bddBelow (Matrix.toEuclideanCLM (𝕜 := ℝ) target))
    (⟨EuclideanSpace.single coordinate (1 : ℝ), hnonzero⟩ :
      {x : EuclideanSpace ℝ (Fin dim) // x ≠ 0})
  rw [rayleigh_toEuclideanCLM_eq] at hrayleigh
  have hnormOne : ‖(EuclideanSpace.single coordinate (1 : ℝ))‖ = 1 := by simp
  have hvalue : ((EuclideanSpace.single coordinate (1 : ℝ)) : Fin dim → ℝ)
      ⬝ᵥ (target *ᵥ ((EuclideanSpace.single coordinate (1 : ℝ)) : Fin dim → ℝ))
      = target coordinate coordinate := by
    show (Pi.single coordinate (1 : ℝ))
      ⬝ᵥ (target *ᵥ (Pi.single coordinate (1 : ℝ))) = target coordinate coordinate
    rw [Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col_apply]
  simp only [hnormOne, hvalue, one_pow, div_one] at hrayleigh
  exact hrayleigh

/-- **The least-eigenvalue score** on `k`-subsets: `λ_min(S_C)`. This is the score the
exchange route was ever about, because `Dominates` IS `1 ≤ λ_min(S_C)`. -/
noncomputable def leastEigenvalue [Nonempty (Fin k)] (D : WeightedDesign m k)
    (C : Finset (Fin m)) : ℝ :=
  lambdaMinMat (subsetSum D C)

/-- The coordinate certificate at the score. -/
theorem leastEigenvalue_le_diagonal [Nonempty (Fin k)] (D : WeightedDesign m k)
    (C : Finset (Fin m)) (coordinate : Fin k) :
    leastEigenvalue D C ≤ subsetSum D C coordinate coordinate :=
  lambdaMinMat_le_diagonal (subsetSum D C) coordinate

/-- Domination is exactly `1 ≤` the score — the shipped
`Gtz.dominates_iff_one_le_lambdaMinMat`, restated at the score. -/
theorem dominates_iff_one_le_leastEigenvalue [Nonempty (Fin k)] (D : WeightedDesign m k)
    (C : Finset (Fin m)) : Dominates D C ↔ 1 ≤ leastEigenvalue D C :=
  dominates_iff_one_le_lambdaMinMat D C

/-! ## Bounded-radius exchange

`Gtz.ExchangeImproves` carries no radius bound. The route's actual content was the
bounded version, so it needs its own name. -/

/-- **The bounded-radius exchange hypothesis**: every non-dominating `k`-subset admits a
strictly better `k`-subset WITHIN exchange distance `radius`. This — not the unbounded
`Gtz.ExchangeImproves` — is what a local-search proof of GTZ would have to supply. -/
def ExchangeImprovesWithinRadius (m k radius : ℕ)
    (score : WeightedDesign m k → Finset (Fin m) → ℝ) : Prop :=
  ∀ (D : WeightedDesign m k) (C : Finset (Fin m)), C.card = k → ¬ Dominates D C →
    ∃ improved : Finset (Fin m), improved.card = k ∧
      exchangeDistance C improved ≤ radius ∧ score D C < score D improved

/-- **The bounded-radius hypothesis restricted to ALL-HEAVY designs.**  This is the form
the campaign actually needs: `Gtz.gtzWeightedAll_of_heavy` reduces GTZ to all-heavy
designs, so a local-search proof only ever had to handle those.  It is a WEAKER
hypothesis than `ExchangeImprovesWithinRadius` (fewer designs to serve), hence refuting
it is the STRONGER statement. -/
def ExchangeImprovesWithinRadiusHeavy (m k radius : ℕ)
    (score : WeightedDesign m k → Finset (Fin m) → ℝ) : Prop :=
  ∀ (D : WeightedDesign m k), AllHeavy D → ∀ C : Finset (Fin m), C.card = k →
    ¬ Dominates D C →
    ∃ improved : Finset (Fin m), improved.card = k ∧
      exchangeDistance C improved ≤ radius ∧ score D C < score D improved

/-- **Radius-`radius` stuckness at a subset**: no subset within exchange distance
`radius` scores strictly higher. The exact negation the counterexample below establishes,
at a subset that also fails to dominate. -/
def IsExchangeStuck (radius : ℕ) (score : WeightedDesign m k → Finset (Fin m) → ℝ)
    (D : WeightedDesign m k) (C : Finset (Fin m)) : Prop :=
  ∀ candidate : Finset (Fin m), candidate.card = C.card →
    exchangeDistance C candidate ≤ radius → ¬ (score D C < score D candidate)

/-- Forgetting the radius bound lands in the unbounded hypothesis. -/
theorem exchangeImproves_of_withinRadius {radius : ℕ}
    (score : WeightedDesign m k → Finset (Fin m) → ℝ)
    (himproves : ExchangeImprovesWithinRadius m k radius score) :
    ExchangeImproves m k score := fun D C hcard hnotDominates => by
  obtain ⟨improved, himprovedCard, _, hstrict⟩ := himproves D C hcard hnotDominates
  exact ⟨improved, himprovedCard, hstrict⟩

/-- Widening the radius weakens the hypothesis, so a refutation at radius `wider`
refutes every narrower radius. -/
theorem exchangeImprovesWithinRadius_mono {radius wider : ℕ} (hle : radius ≤ wider)
    (score : WeightedDesign m k → Finset (Fin m) → ℝ)
    (himproves : ExchangeImprovesWithinRadius m k radius score) :
    ExchangeImprovesWithinRadius m k wider score := fun D C hcard hnotDominates => by
  obtain ⟨improved, himprovedCard, hdistance, hstrict⟩ := himproves D C hcard hnotDominates
  exact ⟨improved, himprovedCard, le_trans hdistance hle, hstrict⟩

/-- **Bounded-radius local search closes GTZ** — the composition of the forgetful step
with the shipped `Gtz.gtzWeighted_of_exchangeImproves`. This is the reduction the route
was aiming at; the counterexample below shows its hypothesis is false at every radius
below the rank. -/
theorem gtzWeighted_of_exchangeImprovesWithinRadius {radius : ℕ} (hsizeLe : k ≤ m)
    (score : WeightedDesign m k → Finset (Fin m) → ℝ)
    (himproves : ExchangeImprovesWithinRadius m k radius score) : GtzWeighted m k :=
  gtzWeighted_of_exchangeImproves hsizeLe score
    (exchangeImproves_of_withinRadius score himproves)

/-- **Radius `k` is vacuous.** A `k`-subset is within exchange distance `k` of every
`k`-subset, so radius-`k` local search is global search and the bounded hypothesis
collapses to the unbounded one. Hence `k - 1` is the last radius that says anything, and
that is precisely the radius the counterexample below refutes at `k = 3`. -/
theorem exchangeImprovesWithinRadius_iff_unbounded_of_rank_le {radius : ℕ}
    (hrankLe : k ≤ radius) (score : WeightedDesign m k → Finset (Fin m) → ℝ) :
    ExchangeImprovesWithinRadius m k radius score ↔ ExchangeImproves m k score := by
  constructor
  · exact exchangeImproves_of_withinRadius score
  · intro himproves D C hcard hnotDominates
    obtain ⟨improved, himprovedCard, hstrict⟩ := himproves D C hcard hnotDominates
    refine ⟨improved, himprovedCard, ?_, hstrict⟩
    calc exchangeDistance C improved
        ≤ improved.card := exchangeDistance_le_card C improved
      _ = k := himprovedCard
      _ ≤ radius := hrankLe

/-- **The unbounded hypothesis at `λ_min` is a restatement of GTZ, not a step toward it.**
Domination is `1 ≤ λ_min(S_C)`, so at a non-dominating subset any dominating subset
already scores strictly higher; the converse is the shipped reduction. The whole content
of the route therefore had to come from the radius bound — which the counterexample below
removes. -/
theorem exchangeImproves_leastEigenvalue_iff_gtzWeighted [Nonempty (Fin k)]
    (hsizeLe : k ≤ m) :
    ExchangeImproves m k (leastEigenvalue (m := m) (k := k)) ↔ GtzWeighted m k := by
  constructor
  · exact gtzWeighted_of_exchangeImproves hsizeLe _
  · intro hgtz D C _ hnotDominates
    obtain ⟨dominating, hdominatingCard, hdominates⟩ := hgtz D
    refine ⟨dominating, hdominatingCard, ?_⟩
    have hbelowOne : leastEigenvalue D C < 1 :=
      lt_of_not_ge fun hge => hnotDominates ((dominates_iff_one_le_leastEigenvalue D C).mpr hge)
    have hatLeastOne : 1 ≤ leastEigenvalue D dominating :=
      (dominates_iff_one_le_leastEigenvalue D dominating).mp hdominates
    linarith

/-! ## The trace obstruction, the one place all-heaviness enters

All-heaviness forces the TOP eigenvalue of any `k`-subset above `1`, so the bottom
eigenvalue of a failing all-heavy `k`-subset cannot have full multiplicity `k`. Through
the Cauchy interlacing ceiling `λ_min(S_{C'}) ≤ λ_{r+1}(S_C)` for `|C' \ C| ≤ r` that is
what leaves radius `k - 1` — radius `2` at rank three — as the only radius not blocked
outright by multiplicity, and hence the only one worth refuting by hand. -/

/-- **All-heaviness beats the rank in trace**: the trace of a `k`-subset's atom sum is
the total leverage, and every leverage exceeds one. Consequently the largest eigenvalue
of `S_C` exceeds `1`, so `S_C = μ·I` with `μ < 1` is impossible on an all-heavy design —
bottom multiplicity `k` at a failing subset cannot occur. -/
theorem rank_lt_trace_subsetSum_of_allHeavy {D : WeightedDesign m k} (hheavy : AllHeavy D)
    {C : Finset (Fin m)} (hcard : C.card = k) (hrankPos : 0 < k) :
    (k : ℝ) < Matrix.trace (subsetSum D C) := by
  have hnonempty : C.Nonempty := Finset.card_pos.mp (by omega)
  have htrace : Matrix.trace (subsetSum D C) = ∑ c ∈ C, leverageOf (D.atom c) := by
    rw [subsetSum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun c _ => trace_atomMatrix (D.atom c)
  have hstrict : ∑ _c ∈ C, (1 : ℝ) < ∑ c ∈ C, leverageOf (D.atom c) :=
    Finset.sum_lt_sum_of_nonempty hnonempty fun c _ => hheavy c
  rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one] at hstrict
  rw [htrace]
  exact hstrict

/-! ## Diagonal entries of a subset atom sum -/

/-- A diagonal entry of the atom sum is the total squared coordinate — the quantity every
coordinate certificate below evaluates. -/
theorem subsetSum_diagonal (D : WeightedDesign m k) (C : Finset (Fin m)) (coordinate : Fin k) :
    subsetSum D C coordinate coordinate = ∑ c ∈ C, D.atom c coordinate ^ 2 := by
  rw [subsetSum, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun c _ => by
    rw [atomMatrix, Matrix.vecMulVec_apply, sq]

/-- A sum over an explicit three-element subset unfolds to three terms. -/
theorem sum_over_triple {carrier : Type*} [AddCommMonoid carrier] {size : ℕ}
    (summand : Fin size → carrier) {first second third : Fin size}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    ∑ index ∈ ({first, second, third} : Finset (Fin size)), summand index
      = summand first + summand second + summand third := by
  rw [Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
    Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton, add_assoc]

/-! ## The counterexample design

Six atoms in `ℝ³`. The first three are a near-orthonormal barely-heavy triple; the last
three are the coordinate axes scaled by `2`. Parseval, the weight sum and all-heaviness
are exact rational identities.

  * leverages `10217/10000, 661/500, 661/500, 4, 4, 4` — all above `1`;
  * `S_{0,1,2} = diag(576/625, 576/625, 729/400)`, so the triple `{0,1,2}` FAILS;
  * `S_{3,4,5} = 4·I`, so GTZ holds at this design, at exchange distance `3`. -/

/-- The six atoms. -/
noncomputable def radiusTwoStuckAtom : Fin 6 → Fin 3 → ℝ :=
  ![![16/25, 16/25, -(9/20)],
    ![-(8/25), 16/25, 9/10],
    ![16/25, -(8/25), 9/10],
    ![2, 0, 0],
    ![0, 2, 0],
    ![0, 0, 2]]

/-- The exact rational all-heavy `(6,3)` design at which radius-`2` exchange on `λ_min`
gets stuck at a failing subset. -/
noncomputable def radiusTwoStuckDesign : WeightedDesign 6 3 where
  atom := radiusTwoStuckAtom
  weight := ![10000/83343, 10000/83343, 10000/83343,
              24709/111124, 24709/111124, 10853/55562]
  weight_pos := by intro c; fin_cases c <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_six, smul_eq_mul, radiusTwoStuckAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- The stuck subset: the near-orthonormal barely-heavy triple. -/
def radiusTwoStuckSubset : Finset (Fin 6) := {0, 1, 2}

theorem radiusTwoStuckSubset_card : radiusTwoStuckSubset.card = 3 := by decide

/-- Case analysis on an atom index, producing numerals (unlike `fin_cases`, whose
`Fin.mk` output blocks the vector-literal simp lemmas). -/
theorem fin_six_index_cases (index : Fin 6) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 := by
  revert index
  decide

/-- **The design is all-heavy**: leverages `10217/10000, 661/500, 661/500, 4, 4, 4`. The
first three exceed `1` only barely, which is exactly the near-identity mechanism. -/
theorem radiusTwoStuckDesign_allHeavy : AllHeavy radiusTwoStuckDesign := by
  intro atomIndex
  rcases fin_six_index_cases atomIndex with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [leverageOf, radiusTwoStuckDesign, radiusTwoStuckAtom, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons] <;>
    norm_num

/-- **The stuck subset's quadratic form, exactly.** `S_{0,1,2}` is diagonal with entries
`576/625, 576/625, 729/400`, and `729/400 − 576/625 = 9009/10000`. -/
theorem radiusTwoStuckSubset_form (direction : Fin 3 → ℝ) :
    direction ⬝ᵥ (subsetSum radiusTwoStuckDesign radiusTwoStuckSubset *ᵥ direction)
      = (576/625) * (direction ⬝ᵥ direction) + (9009/10000) * direction 2 ^ 2 := by
  rw [subsetSum_form_eq_sum_sq, radiusTwoStuckSubset,
    sum_over_triple _ (by decide) (by decide) (by decide)]
  simp only [radiusTwoStuckDesign, radiusTwoStuckAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
  ring

/-- **The stuck subset fails to dominate**: at the first coordinate direction the
selected atoms total `576/625 < 1`. -/
theorem radiusTwoStuckDesign_not_dominates :
    ¬ Dominates radiusTwoStuckDesign radiusTwoStuckSubset := by
  rw [radiusTwoStuckSubset]
  refine not_dominates_triple_of_negativeDirection radiusTwoStuckDesign 0 1 2
    (by decide) (by decide) (by decide) ![1, 0, 0] ?_
  simp only [radiusTwoStuckDesign, radiusTwoStuckAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
  norm_num

/-- **GTZ HOLDS at this design.** The three scaled axes give `S_{3,4,5} = 4·I`, whose
least eigenvalue is `4`. The refutation kills the ROUTE, not the conjecture — and the
dominating subset sits at exchange distance exactly `3` from the stuck one, one more than
the radius. -/
theorem radiusTwoStuckDesign_dominates_axisTriple :
    Dominates radiusTwoStuckDesign {3, 4, 5} := by
  rw [dominates_iff_one_le_lambdaMinMat]
  refine le_lambdaMinMat_of_forall _ fun direction => ?_
  rw [subsetSum_form_eq_sum_sq, sum_over_triple _ (by decide) (by decide) (by decide)]
  simp only [radiusTwoStuckDesign, radiusTwoStuckAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
  nlinarith [sq_nonneg (direction 0), sq_nonneg (direction 1), sq_nonneg (direction 2)]

/-- **The stuck subset's score is at least `576/625`**, by the Rayleigh bound: the excess
`9009/10000 · w₂²` is nonnegative. (It is exactly `576/625`, but only the lower bound is
needed.) -/
theorem stuckSubset_le_leastEigenvalue :
    (576/625 : ℝ) ≤ leastEigenvalue radiusTwoStuckDesign radiusTwoStuckSubset := by
  refine le_lambdaMinMat_of_forall _ fun direction => ?_
  rw [radiusTwoStuckSubset_form direction]
  nlinarith [sq_nonneg (direction 2)]

/-! ### The eighteen neighbours, each blocked by an exact coordinate certificate -/

/-- The diagonal entry of an explicit triple's atom sum. -/
theorem radiusTwoStuckDesign_diagonal_triple {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) (coordinate : Fin 3) :
    subsetSum radiusTwoStuckDesign {first, second, third} coordinate coordinate
      = radiusTwoStuckAtom first coordinate ^ 2
        + radiusTwoStuckAtom second coordinate ^ 2
        + radiusTwoStuckAtom third coordinate ^ 2 := by
  rw [subsetSum_diagonal, sum_over_triple _ hfirstSecond hfirstThird hsecondThird]
  rfl

/-- The exact rational evaluation of the atom table shared by all eighteen coordinate
certificates: unfold the vector literals at their numeral indices, then decide the
inequality on rational literals. Named once so the certificate table below reads as a
table. -/
local macro "evalStuckAtomTable" : tactic =>
  `(tactic| (simp only [radiusTwoStuckAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]; norm_num))

/-- The coordinate certificate at an explicit triple, packaged so each of the eighteen
cases below is one exact rational evaluation. -/
theorem radiusTwoStuckDesign_diagonal_le {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) (coordinate : Fin 3)
    (hbound : radiusTwoStuckAtom first coordinate ^ 2
        + radiusTwoStuckAtom second coordinate ^ 2
        + radiusTwoStuckAtom third coordinate ^ 2 ≤ 512/625) :
    leastEigenvalue radiusTwoStuckDesign {first, second, third} ≤ 512/625 := by
  refine le_trans (leastEigenvalue_le_diagonal _ _ coordinate) ?_
  rw [radiusTwoStuckDesign_diagonal_triple hfirstSecond hfirstThird hsecondThird coordinate]
  exact hbound

/-- **Every neighbour within exchange distance two is blocked**, by an explicit
coordinate whose diagonal entry is at most `512/625`. The twenty `3`-subsets split as:
the stuck subset itself (excluded by hypothesis), the axis triple `{3,4,5}` at distance
`3` (excluded by the radius), and these eighteen. Two of them — `{0,1,3}` at coordinate
`1` and `{0,2,4}` at coordinate `0` — attain `512/625` exactly, so the certificate
margin `64/625` is sharp for coordinate vectors. -/
theorem radiusTwoNeighbour_leastEigenvalue_le (candidate : Finset (Fin 6))
    (hcard : candidate.card = 3)
    (hdistance : exchangeDistance radiusTwoStuckSubset candidate ≤ 2)
    (hdistinct : candidate ≠ radiusTwoStuckSubset) :
    leastEigenvalue radiusTwoStuckDesign candidate ≤ 512/625 := by
  -- The certificate applied below, with the three atoms leading so the table reads as one.
  have certifyTriple : ∀ first second third : Fin 6, first ≠ second → first ≠ third →
      second ≠ third → ∀ coordinate : Fin 3,
      radiusTwoStuckAtom first coordinate ^ 2
        + radiusTwoStuckAtom second coordinate ^ 2
        + radiusTwoStuckAtom third coordinate ^ 2 ≤ 512/625 →
      leastEigenvalue radiusTwoStuckDesign {first, second, third} ≤ 512/625 :=
    fun _ _ _ hfs hft hst coordinate => radiusTwoStuckDesign_diagonal_le hfs hft hst coordinate
  rcases finset_card_three_cases candidate hcard with
    heq | heq | heq | heq | heq | heq | heq | heq | heq | heq |
    heq | heq | heq | heq | heq | heq | heq | heq | heq | heq
  · exact absurd heq hdistinct
  · exact heq ▸ certifyTriple 0 1 3 (by decide) (by decide) (by decide) 1 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 0 1 4 (by decide) (by decide) (by decide) 0 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 0 1 5 (by decide) (by decide) (by decide) 0 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 0 2 3 (by decide) (by decide) (by decide) 1 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 0 2 4 (by decide) (by decide) (by decide) 0 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 0 2 5 (by decide) (by decide) (by decide) 1 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 0 3 4 (by decide) (by decide) (by decide) 2 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 0 3 5 (by decide) (by decide) (by decide) 1 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 0 4 5 (by decide) (by decide) (by decide) 0 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 1 2 3 (by decide) (by decide) (by decide) 1 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 1 2 4 (by decide) (by decide) (by decide) 0 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 1 2 5 (by decide) (by decide) (by decide) 0 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 1 3 4 (by decide) (by decide) (by decide) 2 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 1 3 5 (by decide) (by decide) (by decide) 1 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 1 4 5 (by decide) (by decide) (by decide) 0 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 2 3 4 (by decide) (by decide) (by decide) 2 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 2 3 5 (by decide) (by decide) (by decide) 1 (by evalStuckAtomTable)
  · exact heq ▸ certifyTriple 2 4 5 (by decide) (by decide) (by decide) 0 (by evalStuckAtomTable)
  · exact absurd (heq ▸ hdistance) (by decide)

/-! ### The refutation -/

/-- **The stuck subset is radius-`2` stuck.** No `3`-subset within exchange distance `2`
has a strictly larger least eigenvalue: the stuck subset scores at least `576/625` and
every neighbour scores at most `512/625`. -/
theorem radiusTwoStuckSubset_isExchangeStuck :
    IsExchangeStuck 2 leastEigenvalue radiusTwoStuckDesign radiusTwoStuckSubset := by
  intro candidate hcard hdistance hstrict
  rcases eq_or_ne candidate radiusTwoStuckSubset with rfl | hdistinct
  · exact lt_irrefl _ hstrict
  · have hcandidateCard : candidate.card = 3 := by
      rw [hcard, radiusTwoStuckSubset_card]
    have hblocked := radiusTwoNeighbour_leastEigenvalue_le candidate hcandidateCard
      hdistance hdistinct
    have hstuck := stuckSubset_le_leastEigenvalue
    linarith

/-- **THE RADIUS-TWO EXCHANGE CONJECTURE IS FALSE AT RANK THREE.**

`radiusTwoStuckDesign` is an exact rational all-heavy `(6,3)` design; its `3`-subset
`{0,1,2}` fails to dominate (`radiusTwoStuckDesign_not_dominates`), and no `3`-subset at
exchange distance at most `2` scores strictly higher on the least eigenvalue
(`radiusTwoStuckSubset_isExchangeStuck`). Since domination IS `1 ≤ λ_min`, this is the
score the route needed and no other.

Radius `3 = k` is vacuous (`exchangeImprovesWithinRadius_iff_unbounded_of_rank_le`), so
this closes every non-trivial radius at the campaign's frontier rank. GTZ itself is
untouched: `radiusTwoStuckDesign_dominates_axisTriple` exhibits a dominating subset — at
exchange distance `3`. -/
theorem not_exchangeImprovesWithinRadius_two_rankThree :
    ¬ ExchangeImprovesWithinRadius 6 3 2 leastEigenvalue := by
  intro himproves
  obtain ⟨improved, himprovedCard, hdistance, hstrict⟩ :=
    himproves radiusTwoStuckDesign radiusTwoStuckSubset radiusTwoStuckSubset_card
      radiusTwoStuckDesign_not_dominates
  exact radiusTwoStuckSubset_isExchangeStuck improved
    (by rw [himprovedCard, radiusTwoStuckSubset_card]) hdistance hstrict

/-- **Every bounded radius below the rank fails at rank three**, by monotonicity in the
radius: radius `1` and radius `2` are both refuted, and radius `3 = k` is global search.
There is no bounded radius at which local search on `λ_min` proves GTZ at rank three. -/
theorem not_exchangeImprovesWithinRadius_of_le_two_rankThree {radius : ℕ}
    (hradius : radius ≤ 2) : ¬ ExchangeImprovesWithinRadius 6 3 radius leastEigenvalue :=
  fun himproves => not_exchangeImprovesWithinRadius_two_rankThree
    (exchangeImprovesWithinRadius_mono hradius leastEigenvalue himproves)

/-- **THE REFUTATION IN THE FORM THE CAMPAIGN NEEDS.**  The witness design is all-heavy
(`radiusTwoStuckDesign_allHeavy`), so the very same stuck subset refutes the ALL-HEAVY
bounded-radius hypothesis — the weaker hypothesis, hence the stronger refutation.  Since
`Gtz.gtzWeightedAll_of_heavy` reduces GTZ to all-heavy designs, this is the statement
that closes the route: no radius-`2` local search on `λ_min` proves GTZ at rank three,
not even after the all-heavy reduction. -/
theorem not_exchangeImprovesWithinRadiusHeavy_two_rankThree :
    ¬ ExchangeImprovesWithinRadiusHeavy 6 3 2 leastEigenvalue := by
  intro himproves
  obtain ⟨improved, himprovedCard, hdistance, hstrict⟩ :=
    himproves radiusTwoStuckDesign radiusTwoStuckDesign_allHeavy radiusTwoStuckSubset
      radiusTwoStuckSubset_card radiusTwoStuckDesign_not_dominates
  exact radiusTwoStuckSubset_isExchangeStuck improved
    (by rw [himprovedCard, radiusTwoStuckSubset_card]) hdistance hstrict

/-- The all-heavy refutation propagates down to every radius at or below two, exactly as
the unrestricted one does. -/
theorem not_exchangeImprovesWithinRadiusHeavy_of_le_two_rankThree {radius : ℕ}
    (hle : radius ≤ 2) :
    ¬ ExchangeImprovesWithinRadiusHeavy 6 3 radius leastEigenvalue := by
  intro himproves
  refine not_exchangeImprovesWithinRadiusHeavy_two_rankThree ?_
  intro D hheavy C hcard hnotDominates
  obtain ⟨improved, himprovedCard, hdistance, hstrict⟩ := himproves D hheavy C hcard hnotDominates
  exact ⟨improved, himprovedCard, le_trans hdistance hle, hstrict⟩

end Gtz

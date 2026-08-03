/-
# Bounded-radius exchange: the honest ledger for three candidate scores

`Gtz.Reduction.ExchangeRepair` reduces weighted GTZ to `DoesExchangeImprove m k score`:
any real-valued score on `k`-subsets that strictly increases at every non-dominating
`k`-subset closes the conjecture at that size, because a finite argmax cannot be
improved.  Its repair lemmas show that a subset failing in a direction `w` always admits
an OUTSIDE atom whose insertion repairs `w` exactly, and its header records the operative
hope: that repairing the worst direction assembles into monotone progress inside a
BOUNDED exchange radius, radius `2` having been measured to show "ZERO failures over
~53000 random failing subsets".

This file settles that route for the three scores anyone would try, and the answer is
negative in every case where the statement has content.  **It settles nothing about GTZ.**
Every design exhibited here SATISFIES GTZ; what fails is the local-search rule.

## The ledger

**Score 1 — the least eigenvalue** `λ_min(S_C)`, the score `Dominates` literally is
(`dominates_iff_one_le_leastEigenvalue`).

  * unrestricted `DoesExchangeImprove`: **TAUTOLOGICAL.**
    `doesExchangeImprove_leastEigenvalue_iff_gtzWeighted` and, for every score meeting the
    specification, `doesExchangeImprove_iff_gtzWeighted_ofSpec`: the hypothesis is
    LOGICALLY EQUIVALENT to `GtzWeighted m k`.  Proving it IS proving GTZ.  Both are
    instances of one lemma, `doesExchangeImprove_iff_gtzWeighted_ofThreshold` — any score
    with a domination threshold is tautological, which is exactly why the shadow
    determinant (Score 3, threshold-free) is the only one whose UNBOUNDED refutation
    carries information.
  * radius `1` and radius `2` at `(6,3)`: **REFUTED**
    (`not_exchangeImprovesWithinRadius_of_le_two_rankThree`), and refuted in the
    all-heavy form the campaign's reduction actually needs
    (`not_exchangeImprovesWithinRadiusHeavy_of_le_two_rankThree`).
  * radius `1` and radius `2` at `(7,3)`: **REFUTED** for EVERY score satisfying
    `IsLeastEigenvalueScore` (`not_exchangeImprovesWithinRadius_two_sevenThree`), hence
    for the shipped `Gtz.leastEigenvalue` itself
    (`not_exchangeImprovesWithinRadius_two_leastEigenvalue`), the specification being
    inhabited (`isLeastEigenvalueScore_leastEigenvalue`) and categorical
    (`eq_of_isLeastEigenvalueScore`).
  * radius `≥ 3` at rank three: **CONTENT-FREE, NOT REFUTED.**
    `doesExchangeImproveWithinRadius_iff_unbounded_of_rank_le` collapses it to the
    unrestricted hypothesis, which is GTZ, which is OPEN.  "No radius survives with
    content" is the accurate statement; "every radius is refuted" would be false.

**Score 2 — the clipped trace** `Σ_i min(λ_i(S_C), 1)`, the total domination mass.

  * unrestricted: **TAUTOLOGICAL** (`doesExchangeImprove_clippedTrace_iff_gtzWeighted`),
    by the same threshold lemma at threshold `k`
    (`dominates_iff_clippedTrace_eq_rank`).
  * radius `1` and radius `2` at `(7,3)`: **REFUTED**, unrestricted
    (`not_exchangeImprovesWithinRadius_clippedTrace_two`) and all-heavy
    (`not_exchangeImprovesWithinRadiusHeavy_clippedTrace_two`).
  * radius `≥ 3` at rank three: content-free, as above.

**Score 3 — the shadow determinant** `det P_T`, the volume-sampling / maximal-volume
objective on the design's projection form (`Gtz.LinAlg.ProjectionForm`).

  * **REFUTED OUTRIGHT**, with no radius bound at all
    (`not_exchangeImproves_shadowDeterminant`), and on the all-heavy stratum
    (`not_exchangeImprovesHeavy_shadowDeterminant`), and as a size-indexed family
    (`not_exchangeImproves_shadowDeterminant_family`), because a non-dominating
    `3`-subset is its GLOBAL argmax at an explicit `(7,3)` design.  This is strictly
    stronger than the bounded refutations above and it is NOT a restatement of GTZ:
    the score has no domination threshold, and the witness design satisfies GTZ
    (`shadowArgmaxDesign_hasDominatingSubset` exhibits `{0,1,6}`; an exhaustive
    exact-minor scan outside Lean counts ten dominating triples of thirty-five, which
    is MEASURED, not proved here).
  * What survives: `shadowDeterminant_eq_weightProduct_mul_detSq` (the square-root-free
    evaluation `det P_T = (∏_{c∈T} t_c) · det(g_c)_{c∈T}²`),
    `sum_shadowDeterminant_eq_one`, `exists_shadowDeterminant_ge_inv_binomial` (the
    Pythagoras pigeonhole `∃T, det P_T ≥ 1/C(m,k)`) and
    `shadowDeterminant_pos_of_dominates`.

## Residual — what is NOT decided here

`GtzWeighted 6 3`, `GtzWeighted 7 3`, `GtzWeightedHeavy 6 3`, `GtzWeightedHeavy 7 3` and
`GtzWeightedAll 3` are untouched; so is `DoesExchangeImprove m k score` at any
threshold-shaped score, which is those conjectures verbatim.  Nothing here bears on rank
`≥ 4`, and nothing bears on sizes other than the two witnessed ones: the witnesses are
`(6,3)` and `(7,3)`, and no padding lemma is mechanized.

The smallest remaining obstruction, stated precisely.  `Gtz.rank_three_of_heavy_residuals`
consumes exactly `GtzWeightedHeavy 6 3` and `GtzWeightedHeavy 7 3`, so a bounded-radius
local search closes rank three iff it supplies BOTH.  What is left open is therefore

    DoesExchangeImproveWithinRadiusHeavy 6 3 2 score  ∧  DoesExchangeImproveWithinRadiusHeavy 7 3 2 score

for a score that is NEITHER threshold-shaped NOR the shadow determinant.  For the least
eigenvalue BOTH conjuncts are refuted below; for the clipped trace the size-seven
conjunct is refuted, which already breaks the conjunction — its size-six conjunct is NOT
decided here.  A threshold-shaped score cannot help even if its bounded form survived at
some other size, because its unbounded form is already GTZ
(`doesExchangeImprove_iff_gtzWeighted_ofThreshold`); the shadow determinant cannot help at
size seven at all.  No score outside those two families is exhibited anywhere in this
campaign; this file does not rule one out, and does not claim to.

## Certificates are exact; the float record, honestly

Every certificate below is exact rational or integer arithmetic.  Two shapes carry all
of it: a Rayleigh/Loewner lower bound at the stalled subset, and a strictly-negative
rational quantity (a coordinate diagonal, a shifted determinant, or a quadratic form at
an integer direction) at every neighbour.  No eigenvalue is ever computed, and no
floating-point number enters any proof.

  * WITHDRAWN as a float artifact: the value `0.9872086614491439` quoted for a stalled
    subset's least eigenvalue in an earlier report is double-precision noise; the exact
    value is the least root of `15625x³ − 80000x² + 114575x − 50176`, whose 80-digit
    expansion begins `0.98720866144914428615`.  No statement in this file depends on it.
  * MEASURED-ONLY, reproduced by three independent agents and by nothing here: radius-1
    stall rates near `5·10⁻⁴` and radius-2 stall rates near `4·10⁻⁷` per failing subset
    for `λ_min`, near `1·10⁻⁶` for the clipped trace, and a `4 %` argmax-failure rate
    for the shadow determinant on all-heavy `(7,3)` designs.  These are float samples.
    They are the reason the `ExchangeRepair` header's "ZERO failures over ~53000 random
    failing subsets" was never evidence of absence — at a rate of `4·10⁻⁷` a 53000-sample
    scan expects `0.02` hits — and that header is now falsified by the theorems below,
    for the least eigenvalue and for the clipped trace.
  * MEASURED-ONLY, not mechanized: the extremal fibre does NOT break any of the three
    scores.  At the regular simplex every `k`-subset dominates and the clipped trace is
    exactly `k`; along the split-tetrahedron weight fibre the shadow-determinant argmax
    always dominates, because a triple repeating a direction has determinant zero.  The
    refutations live at generic designs.  (Constancy of `subsetSum` along that fibre is
    a DEFINITIONAL triviality — `Gtz.subsetSum` is weight-free — and is not evidence of
    anything.)
  * MEASURED-ONLY, not mechanized: the `(7,3)` least-eigenvalue witness is not known to
    be independent of the `(6,3)` one.  Splitting one atom of `radiusTwoStuckDesign` into
    two half-weight copies numerically produces a `(7,3)` radius-two stall with a larger
    deficit, so the `(7,3)` statement is plausibly a corollary of the `(6,3)` one plus a
    padding lemma.  That lemma is NOT mechanized and the two witnesses are independent
    designs here.

## Literature (cited, not proved here)

The conjecture is Goreinov–Tyrtyshnikov–Zamarashkin, LAA **261** (1997) 1–21, eq. (2.6).
Rank two is a theorem (Sengupta–Pautov, arXiv:2604.05944; the `n = 4` case Nesterenko,
arXiv:2303.07492; the equality criterion arXiv:2604.14050).  Over `ℂ` the statement is
FALSE at rank two with sharp constant `2 − 2/√3` (arXiv:2604.24087), so no field-agnostic
argument can decide the real case.  Tight configurations for general rank come from
scaled star spaces of series-parallel graphs (arXiv:2511.02387).

Score 3 is the classical maximal-volume objective: `det P_T = det(V_T)²` on the scaled
frame (`Gtz.det_projectionBlock_eq_sq_volume`), so its argmax IS the maxvol rule of
Goreinov–Tyrtyshnikov.  The classical dominant-submatrix bound is
`σ_min² ≥ 1/(k(m−k) + 1)`; `Gtz.Reduction.MaximalVolume` mechanizes the dictionary, the
maximality identity, the solve-matrix bound, and the exact deficit
`k(m−k)+1 = m + (k−1)(m−k−1)` (`gtzDenominator_add_deficit_eq_classical`) — `13` against
the required `7` at `(7,3)` — while its own header records that two steps of the classical
argument (the Frobenius count and `MᵀM ⪯ 1`) are NOT proved there, so the bound itself is
CITED, not mechanized.  The refutation below is sharper than that deficit either way: not
only is the classical bound too weak at `(7,3)`, the classical RULE fails there.  The
identity
`Σ_{|T|=k} det P_T = 1` is Cauchy–Binet, equivalently the generalized Pythagorean theorem
(Conant–Beyer, Amer. Math. Monthly **81** (1974)), and is the normalization of Lyons'
determinantal measure (arXiv:math/0204325).  The restricted-invertibility line
(Spielman–Srivastava arXiv:0911.1114, Marcus–Spielman–Srivastava arXiv:1712.07766,
Naor–Youssef arXiv:1601.00948) is identically void at `k = rank`, which is the GTZ regime.

## What survives in `ExchangeRepair`

`exists_atom_covering_direction`, `atom_mem_failing_lt`, `coveringAtom_notMem_of_failing`,
`swap_repairs_direction` and `exists_swap_repairing_worstDirection` are untouched and
correct — they are statements about ONE direction, and the witnesses below are the
explicit realization of the gap that file's own docstring names ("repairing `w` may open
a different direction").
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Quantitative.MarginContinuity
import Gtz.Reduction.ExchangeRepair
import Gtz.Reduction.LiftingLemma
import Gtz.Reduction.RayleighCertificate
import Gtz.Reduction.Reductions
import Gtz.Ties.SelectionObstruction

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Pointwise

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

/-- **Exchange distance and retained overlap are the same constraint.** A radius bound
`exchangeDistance C improved ≤ radius` says exactly that `improved` retains all but
`radius` of `C`'s elements. The two spellings appear in the literature and in the
campaign's own notes interchangeably; this is the one lemma that lets a neighbourhood
enumeration written in the overlap form discharge a hypothesis written in the distance
form. -/
theorem exchangeDistance_le_iff_le_card_inter_add {source target : Finset (Fin m)}
    {size radius : ℕ} (htargetCard : target.card = size) :
    exchangeDistance source target ≤ radius ↔ size ≤ (source ∩ target).card + radius := by
  have hsplit := Finset.card_sdiff_add_card_inter target source
  rw [Finset.inter_comm] at hsplit
  rw [exchangeDistance]
  omega

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

/-- **The Rayleigh upper bound at an arbitrary direction.** `λ_min` is the infimum of the
Rayleigh quotient, so it is dominated by the quotient at every nonzero direction, and the
zero direction is the trivial case. This is the half of the dictionary that
`le_lambdaMinMat_of_forall` does not give. -/
theorem lambdaMinMat_mul_dotProduct_self_le {dim : ℕ} [Nonempty (Fin dim)]
    (target : Matrix (Fin dim) (Fin dim) ℝ) (direction : Fin dim → ℝ) :
    lambdaMinMat target * (direction ⬝ᵥ direction)
      ≤ direction ⬝ᵥ (target *ᵥ direction) := by
  rcases eq_or_ne direction 0 with rfl | hnonzero
  · simp
  · have hlift : (WithLp.toLp 2 direction : EuclideanSpace ℝ (Fin dim)) ≠ 0 := by
      simpa using hnonzero
    have hrayleigh := ciInf_le (rayleigh_bddBelow (Matrix.toEuclideanCLM (𝕜 := ℝ) target))
      (⟨WithLp.toLp 2 direction, hlift⟩ : {x : EuclideanSpace ℝ (Fin dim) // x ≠ 0})
    rw [rayleigh_toEuclideanCLM_eq] at hrayleigh
    have hpositiveLength : (0 : ℝ)
        < ‖(WithLp.toLp 2 direction : EuclideanSpace ℝ (Fin dim))‖ ^ 2 := by
      have hne : (WithLp.toLp 2 direction : EuclideanSpace ℝ (Fin dim)) ≠ 0 := hlift
      positivity
    rw [le_div_iff₀ hpositiveLength, euclid_norm_sq_eq_dotProduct] at hrayleigh
    rw [lambdaMinMat, lambdaMinCLM]
    simpa using hrayleigh

/-- **The level test against `lambdaMinMat`, in plain dot-product form.** Both directions
of the Rayleigh dictionary at an arbitrary level, which is what turns the shipped
`Gtz.leastEigenvalue` into an instance of the least-eigenvalue SPECIFICATION below. -/
theorem le_lambdaMinMat_iff_forall_dotProduct {dim : ℕ} [Nonempty (Fin dim)]
    (target : Matrix (Fin dim) (Fin dim) ℝ) (level : ℝ) :
    level ≤ lambdaMinMat target ↔ ∀ direction : Fin dim → ℝ,
      level * (direction ⬝ᵥ direction) ≤ direction ⬝ᵥ (target *ᵥ direction) := by
  refine ⟨fun hlevel direction => ?_, le_lambdaMinMat_of_forall target⟩
  calc level * (direction ⬝ᵥ direction)
      ≤ lambdaMinMat target * (direction ⬝ᵥ direction) :=
        mul_le_mul_of_nonneg_right hlevel (dotProduct_self_nonneg direction)
    _ ≤ direction ⬝ᵥ (target *ᵥ direction) :=
        lambdaMinMat_mul_dotProduct_self_le target direction

/-! ## Bounded-radius exchange

`Gtz.DoesExchangeImprove` carries no radius bound. The route's actual content was the
bounded version, so it needs its own name. -/

/-- **The bounded-radius exchange hypothesis**: every non-dominating `k`-subset admits a
strictly better `k`-subset WITHIN exchange distance `radius`. This — not the unbounded
`Gtz.DoesExchangeImprove` — is what a local-search proof of GTZ would have to supply. -/
def DoesExchangeImproveWithinRadius (m k radius : ℕ)
    (score : WeightedDesign m k → Finset (Fin m) → ℝ) : Prop :=
  ∀ (D : WeightedDesign m k) (C : Finset (Fin m)), C.card = k → ¬ Dominates D C →
    ∃ improved : Finset (Fin m), improved.card = k ∧
      exchangeDistance C improved ≤ radius ∧ score D C < score D improved

/-- **The bounded-radius hypothesis restricted to ALL-HEAVY designs.**  This is the form
the campaign actually needs: `Gtz.gtzWeightedAll_of_heavy` reduces GTZ to all-heavy
designs, so a local-search proof only ever had to handle those.  It is a WEAKER
hypothesis than `DoesExchangeImproveWithinRadius` (fewer designs to serve), hence refuting
it is the STRONGER statement. -/
def DoesExchangeImproveWithinRadiusHeavy (m k radius : ℕ)
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
theorem doesExchangeImprove_of_withinRadius {radius : ℕ}
    (score : WeightedDesign m k → Finset (Fin m) → ℝ)
    (himproves : DoesExchangeImproveWithinRadius m k radius score) :
    DoesExchangeImprove m k score := fun D C hcard hnotDominates => by
  obtain ⟨improved, himprovedCard, _, hstrict⟩ := himproves D C hcard hnotDominates
  exact ⟨improved, himprovedCard, hstrict⟩

/-- Widening the radius weakens the hypothesis, so a refutation at radius `wider`
refutes every narrower radius. -/
theorem doesExchangeImproveWithinRadius_mono {radius wider : ℕ} (hle : radius ≤ wider)
    (score : WeightedDesign m k → Finset (Fin m) → ℝ)
    (himproves : DoesExchangeImproveWithinRadius m k radius score) :
    DoesExchangeImproveWithinRadius m k wider score := fun D C hcard hnotDominates => by
  obtain ⟨improved, himprovedCard, hdistance, hstrict⟩ := himproves D C hcard hnotDominates
  exact ⟨improved, himprovedCard, le_trans hdistance hle, hstrict⟩

/-- **Bounded-radius local search closes GTZ** — the composition of the forgetful step
with the shipped `Gtz.gtzWeighted_of_exchangeImproves`. This is the reduction the route
was aiming at; the counterexample below shows its hypothesis is false at every radius
below the rank. -/
theorem gtzWeighted_of_exchangeImprovesWithinRadius {radius : ℕ} (hsizeLe : k ≤ m)
    (score : WeightedDesign m k → Finset (Fin m) → ℝ)
    (himproves : DoesExchangeImproveWithinRadius m k radius score) : GtzWeighted m k :=
  gtzWeighted_of_exchangeImproves hsizeLe score
    (doesExchangeImprove_of_withinRadius score himproves)

/-- **Radius `k` is vacuous.** A `k`-subset is within exchange distance `k` of every
`k`-subset, so radius-`k` local search is global search and the bounded hypothesis
collapses to the unbounded one. Hence `k - 1` is the last radius that says anything, and
that is precisely the radius the counterexample below refutes at `k = 3`. -/
theorem doesExchangeImproveWithinRadius_iff_unbounded_of_rank_le {radius : ℕ}
    (hrankLe : k ≤ radius) (score : WeightedDesign m k → Finset (Fin m) → ℝ) :
    DoesExchangeImproveWithinRadius m k radius score ↔ DoesExchangeImprove m k score := by
  constructor
  · exact doesExchangeImprove_of_withinRadius score
  · intro himproves D C hcard hnotDominates
    obtain ⟨improved, himprovedCard, hstrict⟩ := himproves D C hcard hnotDominates
    refine ⟨improved, himprovedCard, ?_, hstrict⟩
    calc exchangeDistance C improved
        ≤ improved.card := exchangeDistance_le_card C improved
      _ = k := himprovedCard
      _ ≤ radius := hrankLe

/-! ### Threshold scores make the unbounded hypothesis a tautology

A score is THRESHOLD-SHAPED when some real level separates the dominating subsets from
the failing ones. For such a score the unbounded exchange hypothesis is not a lever on
GTZ — it is GTZ. Both scores the campaign proposed (the least eigenvalue at threshold
`1`, the clipped trace at threshold `k`) are threshold-shaped, so all of their content
sits in the radius bound. The shadow determinant is NOT threshold-shaped, which is
exactly why its unbounded refutation below carries information. -/

/-- **A threshold score cannot be a lever.** If some level separates dominating from
failing subsets then `DoesExchangeImprove` at that score is LOGICALLY EQUIVALENT to
`GtzWeighted`: forward is the shipped reduction, backward hands back the dominating
subset, which scores at the threshold while the failing one scores below it. -/
theorem doesExchangeImprove_iff_gtzWeighted_ofThreshold (hsizeLe : k ≤ m)
    (score : WeightedDesign m k → Finset (Fin m) → ℝ) (threshold : ℝ)
    (hdominating : ∀ (D : WeightedDesign m k) (C : Finset (Fin m)),
      Dominates D C → threshold ≤ score D C)
    (hfailing : ∀ (D : WeightedDesign m k) (C : Finset (Fin m)),
      ¬ Dominates D C → score D C < threshold) :
    DoesExchangeImprove m k score ↔ GtzWeighted m k := by
  refine ⟨gtzWeighted_of_exchangeImproves hsizeLe score, fun hgtz D C _hcard hfails => ?_⟩
  obtain ⟨dominator, hdominatorCard, hdominates⟩ := hgtz D
  exact ⟨dominator, hdominatorCard,
    lt_of_lt_of_le (hfailing D C hfails) (hdominating D dominator hdominates)⟩

/-- **The unbounded hypothesis at `λ_min` is a restatement of GTZ, not a step toward it.**
Domination IS `1 ≤ λ_min(S_C)`, so the least eigenvalue is threshold-shaped at level one
and `doesExchangeImprove_iff_gtzWeighted_ofThreshold` applies verbatim. The whole content of
the route therefore had to come from the radius bound — which the counterexamples below
remove. -/
theorem doesExchangeImprove_leastEigenvalue_iff_gtzWeighted [Nonempty (Fin k)]
    (hsizeLe : k ≤ m) :
    DoesExchangeImprove m k (leastEigenvalue (m := m) (k := k)) ↔ GtzWeighted m k :=
  doesExchangeImprove_iff_gtzWeighted_ofThreshold hsizeLe _ 1
    (fun D C hdominates => (dominates_iff_one_le_leastEigenvalue D C).mp hdominates)
    (fun D C hfails => lt_of_not_ge fun hge =>
      hfails ((dominates_iff_one_le_leastEigenvalue D C).mpr hge))

/-! ## The all-heavy exchange hypothesis

The campaign's frontier is `GtzWeightedHeavy` (`rank_three_of_heavy_residuals`),
so the honest target for a local-search score is the hypothesis restricted to
all-heavy designs.  It is strictly weaker than `DoesExchangeImprove`, hence
refuting it is strictly stronger. -/

/-- **The exchange hypothesis, restricted to all-heavy designs.**  Weaker than
`DoesExchangeImprove`, and still enough to close the campaign's frontier. -/
def DoesExchangeImproveHeavy (m k : ℕ)
    (score : WeightedDesign m k → Finset (Fin m) → ℝ) : Prop :=
  ∀ (D : WeightedDesign m k), AllHeavy D → ∀ C : Finset (Fin m), C.card = k →
    ¬ Dominates D C →
      ∃ improved : Finset (Fin m), improved.card = k ∧ score D C < score D improved

/-- The unrestricted hypothesis implies the all-heavy one. -/
theorem doesExchangeImproveHeavy_of_doesExchangeImprove
    (score : WeightedDesign m k → Finset (Fin m) → ℝ)
    (himproves : DoesExchangeImprove m k score) : DoesExchangeImproveHeavy m k score :=
  fun D _ C hcard hfails => himproves D C hcard hfails

/-- **Local search closes the all-heavy frontier.**  Same finite-argmax argument
as `gtzWeighted_of_exchangeImproves`, run inside the all-heavy stratum: the
maximizing subset is taken for the given heavy design, and a strict improvement
at it contradicts maximality. -/
theorem gtzWeightedHeavy_of_exchangeImprovesHeavy (hsizeLe : k ≤ m)
    (score : WeightedDesign m k → Finset (Fin m) → ℝ)
    (himproves : DoesExchangeImproveHeavy m k score) : GtzWeightedHeavy m k := by
  intro D hheavy
  have hfamilyNonempty :
      (Finset.univ.powersetCard k : Finset (Finset (Fin m))).Nonempty :=
    Finset.powersetCard_nonempty.mpr (by simpa using hsizeLe)
  obtain ⟨best, hbestMem, hbestMax⟩ :=
    Finset.exists_max_image _ (fun C => score D C) hfamilyNonempty
  have hbestCard : best.card = k := (Finset.mem_powersetCard.mp hbestMem).2
  refine ⟨best, hbestCard, ?_⟩
  by_contra hnotDominates
  obtain ⟨improved, himprovedCard, hstrict⟩ :=
    himproves D hheavy best hbestCard hnotDominates
  have himprovedMem :
      improved ∈ (Finset.univ.powersetCard k : Finset (Finset (Fin m))) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, himprovedCard⟩
  exact absurd (hbestMax improved himprovedMem) (not_le.mpr hstrict)

/-- The bounded all-heavy hypothesis forgets its radius into the unbounded all-heavy
one. -/
theorem doesExchangeImproveHeavy_of_withinRadiusHeavy {radius : ℕ}
    (score : WeightedDesign m k → Finset (Fin m) → ℝ)
    (himproves : DoesExchangeImproveWithinRadiusHeavy m k radius score) :
    DoesExchangeImproveHeavy m k score := fun D hheavy C hcard hfails => by
  obtain ⟨improved, himprovedCard, _, hstrict⟩ := himproves D hheavy C hcard hfails
  exact ⟨improved, himprovedCard, hstrict⟩

/-- **The bounded all-heavy hypothesis closes the campaign's actual frontier.** Composing
the forgetful step with `gtzWeightedHeavy_of_exchangeImprovesHeavy` — and
`Gtz.gtzWeightedAll_of_heavy_bounded` then reduces GTZ at the rank to finitely many
all-heavy sizes. This is the reduction the refutations below block. -/
theorem gtzWeightedHeavy_of_exchangeImprovesWithinRadiusHeavy (hsizeLe : k ≤ m)
    {radius : ℕ} (score : WeightedDesign m k → Finset (Fin m) → ℝ)
    (himproves : DoesExchangeImproveWithinRadiusHeavy m k radius score) :
    GtzWeightedHeavy m k :=
  gtzWeightedHeavy_of_exchangeImprovesHeavy hsizeLe score
    (doesExchangeImproveHeavy_of_withinRadiusHeavy score himproves)

/-- The unrestricted bounded hypothesis implies the all-heavy bounded one, so an
all-heavy refutation is the stronger statement. -/
theorem doesExchangeImproveWithinRadiusHeavy_of_withinRadius {radius : ℕ}
    (score : WeightedDesign m k → Finset (Fin m) → ℝ)
    (himproves : DoesExchangeImproveWithinRadius m k radius score) :
    DoesExchangeImproveWithinRadiusHeavy m k radius score :=
  fun D _ C hcard hfails => himproves D C hcard hfails

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

/-! ## The least-eigenvalue specification, stated without eigenvalues -/

/-! ## The least eigenvalue, without eigenvalues -/

/-- `lambda_min (S_C) >= level`, stated as a Loewner inequality so that no spectral
theory is needed anywhere below. -/
def HasLeastEigenvalueAtLeast (D : WeightedDesign m k) (C : Finset (Fin m)) (level : ℝ) : Prop :=
  (subsetSum D C - level • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef

/-- The selected atom sum is positive semidefinite: it is a sum of atoms. -/
theorem posSemidef_subsetSum (D : WeightedDesign m k) (C : Finset (Fin m)) :
    (subsetSum D C).PosSemidef :=
  Matrix.posSemidef_sum C fun c _ => posSemidef_atomMatrix (D.atom c)

/-- The level-shifted gap is symmetric. -/
theorem transpose_subsetSum_sub_smul (D : WeightedDesign m k) (C : Finset (Fin m))
    (level : ℝ) :
    (subsetSum D C - level • (1 : Matrix (Fin k) (Fin k) ℝ))ᵀ
      = subsetSum D C - level • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
    transpose_eq_of_isHermitian (posSemidef_subsetSum D C).1]

/-- **The level-shifted gap quadratic form**: `xᵀ(S_C − level·I)x = Σ_{c∈C}(g_c·x)² −
level·|x|²`.  This is `dominationGap_form` with the unit level replaced by a parameter,
and it is the only computation the certificates below ever need. -/
theorem shiftedGap_form (D : WeightedDesign m k) (C : Finset (Fin m)) (level : ℝ)
    (direction : Fin k → ℝ) :
    direction ⬝ᵥ ((subsetSum D C - level • (1 : Matrix (Fin k) (Fin k) ℝ)) *ᵥ direction)
      = (∑ c ∈ C, (D.atom c ⬝ᵥ direction) ^ 2) - level * (direction ⬝ᵥ direction) := by
  rw [Matrix.sub_mulVec, dotProduct_sub, subsetSum_form_eq_sum_sq,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

/-- **The level test, as a Rayleigh inequality.**  `lambda_min(S_C) >= level` says
exactly that the selected atoms cover `level` times the squared length of every
direction. -/
theorem hasLeastEigenvalueAtLeast_iff (D : WeightedDesign m k) (C : Finset (Fin m))
    (level : ℝ) :
    HasLeastEigenvalueAtLeast D C level
      ↔ ∀ direction : Fin k → ℝ,
          level * (direction ⬝ᵥ direction) ≤ ∑ c ∈ C, (D.atom c ⬝ᵥ direction) ^ 2 := by
  rw [HasLeastEigenvalueAtLeast, Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro hpsd direction
    have hform := hpsd.2 direction
    rw [star_trivial, shiftedGap_form] at hform
    linarith
  · refine fun hcovers =>
      ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_smul D C level), fun direction => ?_⟩
    rw [star_trivial, shiftedGap_form]
    linarith [hcovers direction]

/-- Lowering the level is free. -/
theorem hasLeastEigenvalueAtLeast_mono (D : WeightedDesign m k) (C : Finset (Fin m))
    {lower upper : ℝ} (hle : lower ≤ upper) (hupper : HasLeastEigenvalueAtLeast D C upper) :
    HasLeastEigenvalueAtLeast D C lower := by
  rw [hasLeastEigenvalueAtLeast_iff] at hupper ⊢
  intro direction
  have hscaled : lower * (direction ⬝ᵥ direction) ≤ upper * (direction ⬝ᵥ direction) :=
    mul_le_mul_of_nonneg_right hle (dotProduct_self_nonneg direction)
  linarith [hupper direction]

/-- Domination is the level test at one. -/
theorem dominates_iff_leastEigenvalueAtLeast_one (D : WeightedDesign m k)
    (C : Finset (Fin m)) : Dominates D C ↔ HasLeastEigenvalueAtLeast D C 1 := by
  rw [Dominates, HasLeastEigenvalueAtLeast, one_smul]

/-- **The refuting certificate**: one direction where the selected atoms fall short of
`level` times its squared length. -/
theorem not_leastEigenvalueAtLeast_of_witness (D : WeightedDesign m k) (C : Finset (Fin m))
    (level : ℝ) (direction : Fin k → ℝ)
    (hshort : (∑ c ∈ C, (D.atom c ⬝ᵥ direction) ^ 2) < level * (direction ⬝ᵥ direction)) :
    ¬ HasLeastEigenvalueAtLeast D C level := by
  rw [hasLeastEigenvalueAtLeast_iff]
  exact fun hcovers => absurd (hcovers direction) (not_le.mpr hshort)

/-- **The refuting certificate, uniform over an ambient set**: if a single direction is
covered by at most `bound` by every atom of `ambient`, then EVERY three-element subset of
`ambient` misses `level` as soon as `3·bound < level·|direction|²`.  One direction refutes
a whole family of subsets at once. -/
theorem not_leastEigenvalueAtLeast_of_subsetBound (D : WeightedDesign m k)
    {selected ambient : Finset (Fin m)} (level bound : ℝ) (direction : Fin k → ℝ)
    (hsubset : selected ⊆ ambient) (hcard : selected.card = 3)
    (hbound : ∀ c ∈ ambient, (D.atom c ⬝ᵥ direction) ^ 2 ≤ bound)
    (hstrict : 3 * bound < level * (direction ⬝ᵥ direction)) :
    ¬ HasLeastEigenvalueAtLeast D selected level := by
  refine not_leastEigenvalueAtLeast_of_witness D selected level direction ?_
  have htotal : ∑ c ∈ selected, (D.atom c ⬝ᵥ direction) ^ 2 ≤ 3 * bound := by
    calc ∑ c ∈ selected, (D.atom c ⬝ᵥ direction) ^ 2 ≤ ∑ _c ∈ selected, bound :=
          Finset.sum_le_sum fun c hc => hbound c (hsubset hc)
      _ = 3 * bound := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; norm_num
  linarith

/-! ## The real-valued score and its specification -/

/-- The levels a subset's Gram dominates. -/
def dominatedLevels (D : WeightedDesign m k) (C : Finset (Fin m)) : Set ℝ :=
  {level : ℝ | HasLeastEigenvalueAtLeast D C level}

/-- **The specification of a least-eigenvalue score.**  A real-valued score IS the least
eigenvalue exactly when it is the greatest dominated level, and this determines it
uniquely.  Stating the refutation against the specification rather than against one
encoding makes it apply to every implementation. -/
def IsLeastEigenvalueScore (score : WeightedDesign m k → Finset (Fin m) → ℝ) : Prop :=
  ∀ (D : WeightedDesign m k) (C : Finset (Fin m)) (level : ℝ),
    level ≤ score D C ↔ HasLeastEigenvalueAtLeast D C level

/-- The canonical least-eigenvalue score. -/
noncomputable def leastEigenvalueScore (D : WeightedDesign m k) (C : Finset (Fin m)) : ℝ :=
  sSup (dominatedLevels D C)

/-- Level zero is always dominated: the selected atom sum is positive semidefinite. -/
theorem zero_mem_dominatedLevels (D : WeightedDesign m k) (C : Finset (Fin m)) :
    (0 : ℝ) ∈ dominatedLevels D C := by
  show HasLeastEigenvalueAtLeast D C 0
  rw [HasLeastEigenvalueAtLeast, zero_smul, sub_zero]
  exact posSemidef_subsetSum D C

/-- The dominated levels are bounded above once the rank is positive: the all-ones
direction has positive squared length and caps every dominated level. -/
theorem bddAbove_dominatedLevels (D : WeightedDesign m k) (C : Finset (Fin m))
    (hrank : 0 < k) : BddAbove (dominatedLevels D C) := by
  have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
  have hnorm : (fun _ : Fin k => (1 : ℝ)) ⬝ᵥ (fun _ : Fin k => (1 : ℝ)) = (k : ℝ) := by
    simp [dotProduct]
  refine ⟨(∑ c ∈ C, (D.atom c ⬝ᵥ fun _ : Fin k => (1 : ℝ)) ^ 2) / (k : ℝ),
    fun level hlevel => ?_⟩
  have hcovers := (hasLeastEigenvalueAtLeast_iff D C level).mp hlevel (fun _ => (1 : ℝ))
  rw [hnorm] at hcovers
  exact (le_div_iff₀ hrankReal).mpr hcovers

/-- The supremum of the dominated levels is itself dominated: at each fixed direction the
Rayleigh inequality is a bound on the level, and the supremum inherits it. -/
theorem hasLeastEigenvalueAtLeast_sSup (D : WeightedDesign m k) (C : Finset (Fin m)) :
    HasLeastEigenvalueAtLeast D C (leastEigenvalueScore D C) := by
  rw [leastEigenvalueScore, hasLeastEigenvalueAtLeast_iff]
  intro direction
  rcases eq_or_lt_of_le (dotProduct_self_nonneg direction) with hzero | hpos
  · have hvanishes : direction = 0 := eq_zero_of_dotProduct_self_eq_zero hzero.symm
    subst hvanishes
    simp
  · have hcap : sSup (dominatedLevels D C)
        ≤ (∑ c ∈ C, (D.atom c ⬝ᵥ direction) ^ 2) / (direction ⬝ᵥ direction) := by
      refine csSup_le ⟨0, zero_mem_dominatedLevels D C⟩ fun level hlevel => ?_
      exact (le_div_iff₀ hpos).mpr ((hasLeastEigenvalueAtLeast_iff D C level).mp hlevel direction)
    calc sSup (dominatedLevels D C) * (direction ⬝ᵥ direction)
        ≤ ((∑ c ∈ C, (D.atom c ⬝ᵥ direction) ^ 2) / (direction ⬝ᵥ direction))
            * (direction ⬝ᵥ direction) := mul_le_mul_of_nonneg_right hcap hpos.le
      _ = ∑ c ∈ C, (D.atom c ⬝ᵥ direction) ^ 2 := div_mul_cancel₀ _ hpos.ne'

/-- **The specification is inhabited** at every positive rank, so the refutation below is
not a statement about an empty class of scores. -/
theorem isLeastEigenvalueScore_leastEigenvalueScore (hrank : 0 < k) :
    IsLeastEigenvalueScore (leastEigenvalueScore (m := m) (k := k)) := by
  refine fun D C level => ⟨fun hle => ?_, fun hlevel => ?_⟩
  · exact hasLeastEigenvalueAtLeast_mono D C hle (hasLeastEigenvalueAtLeast_sSup D C)
  · exact le_csSup (bddAbove_dominatedLevels D C hrank) hlevel


/-- **The specification is categorical.** Two scores meeting it agree everywhere: each
dominates the other's value by instantiating the specification at that value. So
"the least-eigenvalue score" is a definite description, and a refutation stated against
the specification is a refutation of the unique score it describes — not of a larger
class. -/
theorem eq_of_isLeastEigenvalueScore
    {scoreOne scoreTwo : WeightedDesign m k → Finset (Fin m) → ℝ}
    (hone : IsLeastEigenvalueScore scoreOne) (htwo : IsLeastEigenvalueScore scoreTwo) :
    scoreOne = scoreTwo := by
  funext D C
  exact le_antisymm ((htwo D C (scoreOne D C)).mpr ((hone D C (scoreOne D C)).mp le_rfl))
    ((hone D C (scoreTwo D C)).mpr ((htwo D C (scoreTwo D C)).mp le_rfl))

/-- **The shipped score meets the specification.** `Gtz.leastEigenvalue` is
`lambdaMinMat ∘ subsetSum`, and the Rayleigh dictionary at an arbitrary level says
exactly that its level sets are the dominated levels. Without this bridge the refutation
below would be a statement about an abstract specification rather than about the score
the rest of the campaign computes with. -/
theorem isLeastEigenvalueScore_leastEigenvalue [Nonempty (Fin k)] :
    IsLeastEigenvalueScore (leastEigenvalue (m := m) (k := k)) := by
  intro D C level
  rw [leastEigenvalue, le_lambdaMinMat_iff_forall_dotProduct, hasLeastEigenvalueAtLeast_iff]
  refine forall_congr' fun direction => ?_
  rw [subsetSum_form_eq_sum_sq]

/-- **The unbounded hypothesis at any least-eigenvalue score is GTZ itself**, by the
threshold lemma at level one. -/
theorem doesExchangeImprove_iff_gtzWeighted_ofSpec (hsizeLe : k ≤ m)
    (score : WeightedDesign m k → Finset (Fin m) → ℝ)
    (hscore : IsLeastEigenvalueScore score) :
    DoesExchangeImprove m k score ↔ GtzWeighted m k :=
  doesExchangeImprove_iff_gtzWeighted_ofThreshold hsizeLe score 1
    (fun D C hdominates => (hscore D C 1).mpr
      ((dominates_iff_leastEigenvalueAtLeast_one D C).mp hdominates))
    (fun D C hfails => lt_of_not_ge fun hge => hfails
      ((dominates_iff_leastEigenvalueAtLeast_one D C).mpr ((hscore D C 1).mp hge)))

/-! ## The clipped trace -/

/-! ## The spectral kit: eigenvalue bounds without touching a diagonalization -/

/-- A Loewner shift of a Hermitian matrix is Hermitian. -/
theorem isHermitian_sub_smul_one {form : Matrix (Fin k) (Fin k) ℝ}
    (hHermitian : form.IsHermitian) (level : ℝ) :
    (form - level • (1 : Matrix (Fin k) (Fin k) ℝ)).IsHermitian :=
  hHermitian.sub (Matrix.isHermitian_one.smul (star_trivial level))

/-- **The easy half of the Loewner/spectrum dictionary**: if `A - level*I` is positive
semidefinite then every eigenvalue of `A` is at least `level`.  Read off the
eigenvector itself — the shifted matrix sends it to `(lambda - level)` times itself,
and the quadratic form there is nonnegative while the eigenvector has positive
length. -/
theorem eigenvalue_ge_of_posSemidef_sub_smul_one {form : Matrix (Fin k) (Fin k) ℝ}
    (hHermitian : form.IsHermitian) (level : ℝ)
    (hShiftPsd : (form - level • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef)
    (eigenIndex : Fin k) : level ≤ hHermitian.eigenvalues eigenIndex := by
  set eigenVector : Fin k → ℝ := ⇑(hHermitian.eigenvectorBasis eigenIndex) with heigenVector
  have hNonzero : eigenVector ≠ 0 :=
    (WithLp.ofLp_eq_zero (p := 2)).ne.2 (hHermitian.eigenvectorBasis.orthonormal.ne_zero eigenIndex)
  have hAction : form *ᵥ eigenVector = (hHermitian.eigenvalues eigenIndex) • eigenVector :=
    hHermitian.mulVec_eigenvectorBasis eigenIndex
  have hShiftAction : (form - level • (1 : Matrix (Fin k) (Fin k) ℝ)) *ᵥ eigenVector
      = (hHermitian.eigenvalues eigenIndex - level) • eigenVector := by
    rw [Matrix.sub_mulVec, hAction, Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul]
  have hQuadratic := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hShiftPsd).2 eigenVector
  rw [star_trivial, hShiftAction, dotProduct_smul, smul_eq_mul] at hQuadratic
  have hLengthPos : 0 < eigenVector ⬝ᵥ eigenVector := dotProduct_self_pos hNonzero
  nlinarith [hQuadratic, hLengthPos]

/-- **The other half**: an eigenvalue floor gives back the Loewner shift.  The
spectrum of `A - level*I` is the spectrum of `A` translated by `-level`
(`spectrum.sub_singleton_eq`), so each eigenvalue of the shift is some
`lambda_i - level >= 0`, and Mathlib's eigenvalue criterion for positive
semidefiniteness closes it. -/
theorem posSemidef_sub_smul_one_of_eigenvalue_ge {form : Matrix (Fin k) (Fin k) ℝ}
    (hHermitian : form.IsHermitian) (level : ℝ)
    (hFloor : ∀ eigenIndex, level ≤ hHermitian.eigenvalues eigenIndex) :
    (form - level • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef := by
  have hShiftHermitian := isHermitian_sub_smul_one hHermitian level
  refine hShiftHermitian.posSemidef_iff_eigenvalues_nonneg.mpr ?_
  intro shiftIndex
  have hScalar : (level : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ)
      = algebraMap ℝ (Matrix (Fin k) (Fin k) ℝ) level :=
    (Algebra.algebraMap_eq_smul_one level).symm
  have hMember : hShiftHermitian.eigenvalues shiftIndex
      ∈ Set.range hHermitian.eigenvalues - ({level} : Set ℝ) := by
    rw [← hHermitian.spectrum_real_eq_range_eigenvalues, spectrum.sub_singleton_eq, ← hScalar]
    exact hShiftHermitian.eigenvalues_mem_spectrum_real shiftIndex
  obtain ⟨originalValue, hOriginal, shiftAmount, hShiftAmount, hDecompose⟩ := hMember
  obtain ⟨originalIndex, hOriginalIndex⟩ := hOriginal
  simp only [Set.mem_singleton_iff] at hShiftAmount
  subst hShiftAmount
  simp only [Pi.zero_apply]
  linarith [hFloor originalIndex, hOriginalIndex ▸ hDecompose]

/-- `Matrix.scalar` is the scalar multiple of the identity. -/
theorem scalar_eq_smul_one (level : ℝ) :
    Matrix.scalar (Fin k) level = level • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  rw [Matrix.smul_one_eq_diagonal]
  rfl

/-- **The characteristic-polynomial dictionary**: the shifted determinant is the
product of the shifted eigenvalues.  Mathlib's `charpoly_eq` factors the
characteristic polynomial over the (real) eigenvalues, and `eval_charpoly` evaluates
it as a determinant. -/
theorem prod_level_sub_eigenvalues {form : Matrix (Fin k) (Fin k) ℝ}
    (hHermitian : form.IsHermitian) (level : ℝ) :
    ∏ eigenIndex, (level - hHermitian.eigenvalues eigenIndex)
      = (level • (1 : Matrix (Fin k) (Fin k) ℝ) - form).det := by
  rw [← scalar_eq_smul_one, ← Matrix.eval_charpoly, hHermitian.charpoly_eq]
  simp [Polynomial.eval_prod]

/-! ## The clipped trace -/

/-- The subset atom sum is Hermitian — `posSemidef_subsetSum` above, forgotten to
symmetry.  Every eigenvalue statement below is stated against this proof term. -/
theorem subsetSum_isHermitian (design : WeightedDesign m k) (selected : Finset (Fin m)) :
    (subsetSum design selected).IsHermitian :=
  (posSemidef_subsetSum design selected).isHermitian

/-- **The candidate score**: the trace of the subset Gram with every eigenvalue
clipped at one.  It measures how much of the identity the selected atoms actually
cover, discarding the excess an over-heavy direction contributes. -/
noncomputable def clippedTrace (design : WeightedDesign m k) (selected : Finset (Fin m)) : ℝ :=
  ∑ eigenIndex, min ((subsetSum_isHermitian design selected).eigenvalues eigenIndex) 1

/-- The clipped trace never exceeds the rank. -/
theorem clippedTrace_le_rank (design : WeightedDesign m k) (selected : Finset (Fin m)) :
    clippedTrace design selected ≤ (k : ℝ) := by
  rw [clippedTrace]
  calc ∑ eigenIndex, min ((subsetSum_isHermitian design selected).eigenvalues eigenIndex) 1
      ≤ ∑ _eigenIndex : Fin k, (1 : ℝ) :=
        Finset.sum_le_sum fun eigenIndex _ => min_le_right _ _
    _ = (k : ℝ) := by simp

/-- A dominating subset scores exactly the rank. -/
theorem clippedTrace_eq_rank_of_dominates (design : WeightedDesign m k)
    (selected : Finset (Fin m)) (hDominates : Dominates design selected) :
    clippedTrace design selected = (k : ℝ) := by
  have hFloor : ∀ eigenIndex, (1 : ℝ)
      ≤ (subsetSum_isHermitian design selected).eigenvalues eigenIndex := by
    refine fun eigenIndex =>
      eigenvalue_ge_of_posSemidef_sub_smul_one (subsetSum_isHermitian design selected) 1 ?_ eigenIndex
    rwa [one_smul]
  rw [clippedTrace, Finset.sum_congr rfl fun eigenIndex _ => min_eq_right (hFloor eigenIndex)]
  simp

/-- Conversely a subset scoring the rank dominates: the clipped eigenvalues are each
at most one and total the rank, so each is exactly one. -/
theorem dominates_of_clippedTrace_eq_rank (design : WeightedDesign m k)
    (selected : Finset (Fin m)) (hFull : clippedTrace design selected = (k : ℝ)) :
    Dominates design selected := by
  set eigenvalue := (subsetSum_isHermitian design selected).eigenvalues with heigenvalue
  have hDeficitZero : ∑ eigenIndex, (1 - min (eigenvalue eigenIndex) 1) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [← clippedTrace, hFull]
    ring
  have hEachZero : ∀ eigenIndex, 1 - min (eigenvalue eigenIndex) 1 = 0 := by
    intro eigenIndex
    refine (Finset.sum_eq_zero_iff_of_nonneg fun other _ => ?_).mp hDeficitZero eigenIndex
      (Finset.mem_univ eigenIndex)
    linarith [min_le_right (eigenvalue other) 1]
  have hFloor : ∀ eigenIndex, (1 : ℝ) ≤ eigenvalue eigenIndex := by
    intro eigenIndex
    linarith [hEachZero eigenIndex, min_le_left (eigenvalue eigenIndex) 1]
  have hShift := posSemidef_sub_smul_one_of_eigenvalue_ge
    (subsetSum_isHermitian design selected) 1 hFloor
  rwa [one_smul] at hShift

/-- **Domination is exactly a full clipped trace.** -/
theorem dominates_iff_clippedTrace_eq_rank (design : WeightedDesign m k)
    (selected : Finset (Fin m)) :
    Dominates design selected ↔ clippedTrace design selected = (k : ℝ) :=
  ⟨clippedTrace_eq_rank_of_dominates design selected,
    dominates_of_clippedTrace_eq_rank design selected⟩

/-- A failing subset scores strictly below the rank. -/
theorem clippedTrace_lt_rank_of_not_dominates (design : WeightedDesign m k)
    (selected : Finset (Fin m)) (hFails : ¬ Dominates design selected) :
    clippedTrace design selected < (k : ℝ) :=
  lt_of_le_of_ne (clippedTrace_le_rank design selected) fun hEq =>
    hFails (dominates_of_clippedTrace_eq_rank design selected hEq)

/-! ### The unrestricted hypothesis at the clipped trace is GTZ itself -/

/-- **The clipped trace is threshold-shaped at the rank**, so its unbounded exchange
hypothesis is LOGICALLY EQUIVALENT to weighted GTZ at that size. Proving it IS proving
the conjecture; every version of the hypothesis with content bounds the exchange
radius, and that version is refuted below. -/
theorem doesExchangeImprove_clippedTrace_iff_gtzWeighted (hSizeLe : k ≤ m) :
    DoesExchangeImprove m k clippedTrace ↔ GtzWeighted m k :=
  doesExchangeImprove_iff_gtzWeighted_ofThreshold hSizeLe clippedTrace (k : ℝ)
    (fun design selected hDominates =>
      le_of_eq (clippedTrace_eq_rank_of_dominates design selected hDominates).symm)
    (fun design selected hFails => clippedTrace_lt_rank_of_not_dominates design selected hFails)

/-! ## Rank-three certificates: rational determinants decide the score -/

/-- The real-arithmetic core of the lower bound.  A positive triple product
`(1-a)(1-b)(1-c) > 0` allows an even number of the three to exceed one, and a sum
above three rules out zero of them; so exactly one sits below one, and the floor
`level` on all three caps the loss at `1 - level`. -/
theorem two_add_level_le_clipped_sum {firstValue secondValue thirdValue level : ℝ}
    (hLevelLe : level ≤ 1) (hFirstGe : level ≤ firstValue) (hSecondGe : level ≤ secondValue)
    (hThirdGe : level ≤ thirdValue)
    (hProductPos : 0 < (1 - firstValue) * (1 - secondValue) * (1 - thirdValue))
    (hSumGt : 3 < firstValue + secondValue + thirdValue) :
    2 + level ≤ min firstValue 1 + min secondValue 1 + min thirdValue 1 := by
  rcases le_or_gt 1 firstValue with hFirst | hFirst
  · rw [min_eq_right hFirst]
    rcases le_or_gt 1 secondValue with hSecond | hSecond
    · rw [min_eq_right hSecond]
      rcases le_or_gt 1 thirdValue with hThird | hThird
      · rw [min_eq_right hThird]; linarith
      · rw [min_eq_left hThird.le]; linarith
    · rw [min_eq_left hSecond.le]
      rcases le_or_gt 1 thirdValue with hThird | hThird
      · rw [min_eq_right hThird]; linarith
      · exfalso
        have hTailPos : 0 < (1 - secondValue) * (1 - thirdValue) :=
          mul_pos (by linarith) (by linarith)
        nlinarith [hProductPos, hTailPos]
  · rw [min_eq_left hFirst.le]
    rcases le_or_gt 1 secondValue with hSecond | hSecond
    · rw [min_eq_right hSecond]
      rcases le_or_gt 1 thirdValue with hThird | hThird
      · rw [min_eq_right hThird]; linarith
      · exfalso
        have hHeadPos : 0 < (1 - firstValue) * (1 - thirdValue) :=
          mul_pos (by linarith) (by linarith)
        nlinarith [hProductPos, hHeadPos]
    · rw [min_eq_left hSecond.le]
      rcases le_or_gt 1 thirdValue with hThird | hThird
      · exfalso
        have hHeadPos : 0 < (1 - firstValue) * (1 - secondValue) :=
          mul_pos (by linarith) (by linarith)
        nlinarith [hProductPos, hHeadPos]
      · exfalso; linarith

/-- **The lower bound at rank three.**  A positive-definite floor at `level`, a
positive `det (I - S_C)`, and a trace above three together force the clipped trace
above `2 + level` — with no eigenvalue ever computed. -/
theorem clippedTrace_ge_of_certificates (design : WeightedDesign m 3) (selected : Finset (Fin m))
    (level : ℝ) (hLevelLe : level ≤ 1)
    (hFloorPsd : (subsetSum design selected
      - level • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef)
    (hShiftedDetPos : 0 < ((1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - subsetSum design selected).det)
    (hTraceGt : 3 < Matrix.trace (subsetSum design selected)) :
    2 + level ≤ clippedTrace design selected := by
  set eigenvalue := (subsetSum_isHermitian design selected).eigenvalues with heigenvalue
  have hFloor : ∀ eigenIndex, level ≤ eigenvalue eigenIndex := fun eigenIndex =>
    eigenvalue_ge_of_posSemidef_sub_smul_one (subsetSum_isHermitian design selected)
      level hFloorPsd eigenIndex
  have hProduct : (1 - eigenvalue 0) * (1 - eigenvalue 1) * (1 - eigenvalue 2)
      = ((1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - subsetSum design selected).det := by
    rw [← Fin.prod_univ_three fun eigenIndex => (1 : ℝ) - eigenvalue eigenIndex]
    exact prod_level_sub_eigenvalues (subsetSum_isHermitian design selected) 1
  have hTraceSum : eigenvalue 0 + eigenvalue 1 + eigenvalue 2
      = Matrix.trace (subsetSum design selected) := by
    rw [(subsetSum_isHermitian design selected).trace_eq_sum_eigenvalues, Fin.sum_univ_three]
    simp [heigenvalue]
  rw [clippedTrace, Fin.sum_univ_three]
  exact two_add_level_le_clipped_sum hLevelLe (hFloor 0) (hFloor 1) (hFloor 2)
    (by rw [hProduct]; exact hShiftedDetPos) (by rw [hTraceSum]; exact hTraceGt)

/-- **The upper bound at rank three.**  A positive `det (u*I - S_T)` with `u <= 3/4`
puts some eigenvalue below `u`; clipping the other two at one gives
`clippedTrace < 2 + u <= 11/4`. -/
theorem clippedTrace_lt_of_det_pos (design : WeightedDesign m 3) (selected : Finset (Fin m))
    (level : ℝ) (hLevelLe : level ≤ 3 / 4)
    (hShiftedDetPos : 0 < (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - subsetSum design selected).det) :
    clippedTrace design selected < 11 / 4 := by
  rw [clippedTrace, Fin.sum_univ_three]
  set eigenvalue := (subsetSum_isHermitian design selected).eigenvalues with heigenvalue
  have hProduct : (level - eigenvalue 0) * (level - eigenvalue 1) * (level - eigenvalue 2)
      = (level • (1 : Matrix (Fin 3) (Fin 3) ℝ) - subsetSum design selected).det := by
    rw [← Fin.prod_univ_three fun eigenIndex => level - eigenvalue eigenIndex]
    exact prod_level_sub_eigenvalues (subsetSum_isHermitian design selected) level
  have hSomeBelow : eigenvalue 0 < level ∨ eigenvalue 1 < level ∨ eigenvalue 2 < level := by
    by_contra hNoneBelow
    push Not at hNoneBelow
    obtain ⟨hFirstGe, hSecondGe, hThirdGe⟩ := hNoneBelow
    have hHeadNonneg : 0 ≤ (level - eigenvalue 0) * (level - eigenvalue 1) := by nlinarith
    have hTripleNonpos :
        (level - eigenvalue 0) * (level - eigenvalue 1) * (level - eigenvalue 2) ≤ 0 := by
      nlinarith
    rw [hProduct] at hTripleNonpos
    linarith
  have hCapFirst := min_le_right (eigenvalue 0) 1
  have hCapSecond := min_le_right (eigenvalue 1) 1
  have hCapThird := min_le_right (eigenvalue 2) 1
  have hFloorFirst := min_le_left (eigenvalue 0) 1
  have hFloorSecond := min_le_left (eigenvalue 1) 1
  have hFloorThird := min_le_left (eigenvalue 2) 1
  rcases hSomeBelow with hLow | hLow | hLow <;> linarith

/-- The entries of a subset atom sum. -/
theorem subsetSum_apply (design : WeightedDesign m k) (selected : Finset (Fin m))
    (rowIndex colIndex : Fin k) :
    subsetSum design selected rowIndex colIndex
      = ∑ atomIndex ∈ selected, design.atom atomIndex rowIndex * design.atom atomIndex colIndex := by
  simp [subsetSum, Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply]

/-! ## The shadow determinant -/

/-! ## The shadow determinant -/

/-- **The shadow determinant** of a subset: the principal minor of the design's
projection form along that subset.  Indexed exactly as in
`sum_det_projectionMinors_rank`, so the volume-sampling identity applies to it
verbatim. -/
noncomputable def shadowDeterminant (D : WeightedDesign m k) (selected : Finset (Fin m)) : ℝ :=
  ((projectionOfDesign D).submatrix (Subtype.val : { c // c ∈ selected } → Fin m)
    (Subtype.val : { c // c ∈ selected } → Fin m)).det

/-- The shadow determinants of the `k`-subsets form a probability measure:
they sum to one.  This is `sum_det_projectionMinors_rank` under the new name. -/
theorem sum_shadowDeterminant_eq_one (D : WeightedDesign m k) :
    ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k, shadowDeterminant D selected
      = 1 :=
  sum_det_projectionMinors_rank D

/-! ### Evaluating the shadow determinant along a pick -/

/-- The index equivalence carried by an injective enumeration of a subset. -/
noncomputable def enumerationEquiv {selected : Finset (Fin m)} (pick : Fin k → Fin m)
    (hinj : Function.Injective pick) (himage : Finset.image pick Finset.univ = selected) :
    Fin k ≃ { c // c ∈ selected } :=
  Equiv.ofBijective
    (fun index => ⟨pick index, by
      rw [← himage]
      exact Finset.mem_image_of_mem pick (Finset.mem_univ index)⟩)
    ⟨fun leftIndex rightIndex hpair => hinj (congrArg Subtype.val hpair), by
      rintro ⟨element, hmem⟩
      rw [← himage] at hmem
      obtain ⟨index, -, hindex⟩ := Finset.mem_image.mp hmem
      exact ⟨index, Subtype.ext hindex⟩⟩

/-- The shadow determinant is the principal minor read along any injective
enumeration of the subset — the subtype indexing and the `Fin k` indexing agree,
because a determinant is invariant under simultaneous reindexing. -/
theorem shadowDeterminant_eq_det_submatrix (D : WeightedDesign m k)
    {selected : Finset (Fin m)} (pick : Fin k → Fin m) (hinj : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = selected) :
    shadowDeterminant D selected = ((projectionOfDesign D).submatrix pick pick).det := by
  rw [shadowDeterminant,
    ← Matrix.det_submatrix_equiv_self (enumerationEquiv pick hinj himage)
      ((projectionOfDesign D).submatrix (Subtype.val : { c // c ∈ selected } → Fin m)
        (Subtype.val : { c // c ∈ selected } → Fin m)),
    Matrix.submatrix_submatrix]
  rfl

/-- The selected rows of the scaled frame factor through the positive diagonal of
square-rooted weights. -/
theorem submatrix_scaledAtomRows_eq (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) :
    (scaledAtomRows D).submatrix pick id
      = sqrtWeightDiagonal D pick * selectedAtomRows D pick := by
  ext selectedIndex coord
  simp only [Matrix.submatrix_apply, id_eq, sqrtWeightDiagonal, Matrix.diagonal_mul,
    scaledAtomRows, selectedAtomRows, Matrix.of_apply]

/-- **The evaluation formula.**  At selection size exactly the rank the shadow
determinant is the product of the selected weights times the squared determinant
of the selected atoms — an entirely square-root-free, eigenvalue-free expression.
Every numerical claim about this score reduces to this identity. -/
theorem shadowDeterminant_eq_weightProduct_mul_detSq (D : WeightedDesign m k)
    {selected : Finset (Fin m)} (pick : Fin k → Fin m) (hinj : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = selected) :
    shadowDeterminant D selected
      = (∏ selectedIndex, D.weight (pick selectedIndex))
        * (selectedAtomRows D pick).det ^ 2 := by
  rw [shadowDeterminant_eq_det_submatrix D pick hinj himage, projectionOfDesign,
    submatrix_mul_transpose_eq (scaledAtomRows D) pick, Matrix.det_mul, Matrix.det_transpose,
    ← pow_two, submatrix_scaledAtomRows_eq, Matrix.det_mul, mul_pow, sqrtWeightDiagonal,
    Matrix.det_diagonal, ← Finset.prod_pow]
  congr 1
  exact Finset.prod_congr rfl fun selectedIndex _ =>
    Real.sq_sqrt (D.weight_pos (pick selectedIndex)).le

/-- Every subset is enumerated by its own order embedding. -/
theorem image_orderEmbOfFin {selected : Finset (Fin m)} (hcard : selected.card = k) :
    Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected := by
  apply Finset.coe_injective
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]

/-- The evaluation formula, indexed by the subset itself. -/
theorem shadowDeterminant_eq_orderEmb (D : WeightedDesign m k)
    {selected : Finset (Fin m)} (hcard : selected.card = k) :
    shadowDeterminant D selected
      = (∏ selectedIndex, D.weight (selected.orderEmbOfFin hcard selectedIndex))
        * (selectedAtomRows D (selected.orderEmbOfFin hcard)).det ^ 2 :=
  shadowDeterminant_eq_weightProduct_mul_detSq D _
    (selected.orderEmbOfFin hcard).injective (image_orderEmbOfFin hcard)

/-- **The shadow determinant of a `k`-subset is nonnegative** — a product of
positive weights times a square. -/
theorem shadowDeterminant_nonneg (D : WeightedDesign m k) {selected : Finset (Fin m)}
    (hcard : selected.card = k) : 0 ≤ shadowDeterminant D selected := by
  rw [shadowDeterminant_eq_orderEmb D hcard]
  exact mul_nonneg
    (Finset.prod_nonneg fun selectedIndex _ =>
      (D.weight_pos (selected.orderEmbOfFin hcard selectedIndex)).le)
    (sq_nonneg _)

/-- **A dominating subset is never a shadow-determinant zero.**  Domination makes
the selected Gram positive definite (it dominates the identity), hence of positive
determinant, and the shadow determinant is that determinant times the positive
weight product.  The score therefore does detect domination qualitatively; what
this file refutes is that its ARGMAX detects it. -/
theorem shadowDeterminant_pos_of_dominates (D : WeightedDesign m k)
    {selected : Finset (Fin m)} (hcard : selected.card = k)
    (hdominates : Dominates D selected) : 0 < shadowDeterminant D selected := by
  have hgram : (selectedAtomRows D (selected.orderEmbOfFin hcard))ᵀ
      * selectedAtomRows D (selected.orderEmbOfFin hcard) = subsetSum D selected := by
    rw [transpose_mul_selectedAtomRows D _ (selected.orderEmbOfFin hcard).injective,
      image_orderEmbOfFin hcard]
  have hposDef : (subsetSum D selected).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_of_transpose_eq ?_, ?_⟩
    · rw [← hgram, Matrix.transpose_mul, Matrix.transpose_transpose]
    · intro direction hnonzero
      have hgap := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 direction
      rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec] at hgap
      rw [star_trivial]
      linarith [dotProduct_self_pos hnonzero]
  have hdetPos : 0 < (selectedAtomRows D (selected.orderEmbOfFin hcard)).det
      * (selectedAtomRows D (selected.orderEmbOfFin hcard)).det := by
    have hdet := hposDef.det_pos
    rwa [← hgram, Matrix.det_mul, Matrix.det_transpose] at hdet
  rw [shadowDeterminant_eq_orderEmb D hcard]
  refine mul_pos (Finset.prod_pos fun selectedIndex _ =>
    D.weight_pos (selected.orderEmbOfFin hcard selectedIndex)) ?_
  rwa [pow_two]

/-! ### The Pythagoras pigeonhole -/

/-- **Volume sampling forces a shadow determinant above the uniform level.**
The `C(m,k)` shadow determinants are nonnegative and sum to one, so some
`k`-subset scores at least `1 / C(m,k)`.  This is the whole unconditional
strength of the identity `Σ_{|T| = k} det P_T = 1`; the measured obstruction to
turning it into a domination certificate is that the level at which a shadow
determinant forces domination sits a factor `C(m,k)/m` higher. -/
theorem exists_shadowDeterminant_ge_inv_binomial (D : WeightedDesign m k) :
    ∃ selected : Finset (Fin m), selected.card = k ∧
      ((m.choose k : ℝ))⁻¹ ≤ shadowDeterminant D selected := by
  by_contra hnone
  push Not at hnone
  have hrank : k ≤ m := rank_le_of_design D
  have hfamilyNonempty :
      ((Finset.univ : Finset (Fin m)).powersetCard k).Nonempty :=
    Finset.powersetCard_nonempty.mpr (by simpa using hrank)
  have hbinomialPos : (0 : ℝ) < (m.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hrank
  have hstrict :
      ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k, shadowDeterminant D selected
        < ∑ _selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
            ((m.choose k : ℝ))⁻¹ :=
    Finset.sum_lt_sum_of_nonempty hfamilyNonempty fun selected hmem =>
      hnone selected (Finset.mem_powersetCard.mp hmem).2
  rw [sum_shadowDeterminant_eq_one D, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_inv_cancel₀ hbinomialPos.ne'] at hstrict
  exact lt_irrefl 1 hstrict

/-! ### An upper bound, for orientation -/

/-- No single shadow determinant exceeds one: the others are nonnegative and the
whole family sums to one. -/
theorem shadowDeterminant_le_one (D : WeightedDesign m k) {selected : Finset (Fin m)}
    (hcard : selected.card = k) : shadowDeterminant D selected ≤ 1 := by
  rw [← sum_shadowDeterminant_eq_one D]
  refine Finset.single_le_sum
    (f := fun other => shadowDeterminant D other) (fun other hmem => ?_)
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩)
  exact shadowDeterminant_nonneg D (Finset.mem_powersetCard.mp hmem).2

/-! # Witness A — the least eigenvalue at size six -/

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
    Matrix.tail_cons]
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
    Matrix.tail_cons]
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

Radius `3 = k` is vacuous (`doesExchangeImproveWithinRadius_iff_unbounded_of_rank_le`), so
this closes every non-trivial radius at the campaign's frontier rank. GTZ itself is
untouched: `radiusTwoStuckDesign_dominates_axisTriple` exhibits a dominating subset — at
exchange distance `3`. -/
theorem not_exchangeImprovesWithinRadius_two_rankThree :
    ¬ DoesExchangeImproveWithinRadius 6 3 2 leastEigenvalue := by
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
    (hradius : radius ≤ 2) : ¬ DoesExchangeImproveWithinRadius 6 3 radius leastEigenvalue :=
  fun himproves => not_exchangeImprovesWithinRadius_two_rankThree
    (doesExchangeImproveWithinRadius_mono hradius leastEigenvalue himproves)

/-- **THE REFUTATION IN THE FORM THE CAMPAIGN NEEDS.**  The witness design is all-heavy
(`radiusTwoStuckDesign_allHeavy`), so the very same stuck subset refutes the ALL-HEAVY
bounded-radius hypothesis — the weaker hypothesis, hence the stronger refutation.  Since
`Gtz.gtzWeightedAll_of_heavy` reduces GTZ to all-heavy designs, this is the statement
that closes the route: no radius-`2` local search on `λ_min` proves GTZ at rank three,
not even after the all-heavy reduction. -/
theorem not_exchangeImprovesWithinRadiusHeavy_two_rankThree :
    ¬ DoesExchangeImproveWithinRadiusHeavy 6 3 2 leastEigenvalue := by
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
    ¬ DoesExchangeImproveWithinRadiusHeavy 6 3 radius leastEigenvalue := by
  intro himproves
  refine not_exchangeImprovesWithinRadiusHeavy_two_rankThree ?_
  intro D hheavy C hcard hnotDominates
  obtain ⟨improved, himprovedCard, hdistance, hstrict⟩ := himproves D hheavy C hcard hnotDominates
  exact ⟨improved, himprovedCard, le_trans hdistance hle, hstrict⟩

/-! # Witness B — the least eigenvalue at size seven -/

/-! ## The stalled design -/

/-- The seven atoms, `g_c = (3/5)·n_c` for integral `n_c` of sup-norm at most two. -/
noncomputable def sevenThreeStallAtom : Fin 7 → (Fin 3 → ℝ) :=
  ![![0, -3/5, -6/5], ![6/5, -6/5, -3/5], ![3/5, 6/5, -6/5], ![6/5, 3/5, 0],
    ![-6/5, -3/5, -6/5], ![3/5, -3/5, 3/5], ![-6/5, -6/5, -6/5]]

/-- The unique weights making the atoms a Parseval design of total mass one. -/
noncomputable def sevenThreeStallWeight : Fin 7 → ℝ :=
  ![8/207, 181/621, 181/621, 8/207, 55/207, 40/621, 2/207]

@[simp] theorem sevenThreeStallAtom_zero : sevenThreeStallAtom 0 = ![0, -3/5, -6/5] := rfl
@[simp] theorem sevenThreeStallAtom_one : sevenThreeStallAtom 1 = ![6/5, -6/5, -3/5] := rfl
@[simp] theorem sevenThreeStallAtom_two : sevenThreeStallAtom 2 = ![3/5, 6/5, -6/5] := rfl
@[simp] theorem sevenThreeStallAtom_three : sevenThreeStallAtom 3 = ![6/5, 3/5, 0] := rfl
@[simp] theorem sevenThreeStallAtom_four : sevenThreeStallAtom 4 = ![-6/5, -3/5, -6/5] := rfl
@[simp] theorem sevenThreeStallAtom_five : sevenThreeStallAtom 5 = ![3/5, -3/5, 3/5] := rfl
@[simp] theorem sevenThreeStallAtom_six : sevenThreeStallAtom 6 = ![-6/5, -6/5, -6/5] := rfl

@[simp] theorem sevenThreeStallWeight_zero : sevenThreeStallWeight 0 = 8/207 := rfl
@[simp] theorem sevenThreeStallWeight_one : sevenThreeStallWeight 1 = 181/621 := rfl
@[simp] theorem sevenThreeStallWeight_two : sevenThreeStallWeight 2 = 181/621 := rfl
@[simp] theorem sevenThreeStallWeight_three : sevenThreeStallWeight 3 = 8/207 := rfl
@[simp] theorem sevenThreeStallWeight_four : sevenThreeStallWeight 4 = 55/207 := rfl
@[simp] theorem sevenThreeStallWeight_five : sevenThreeStallWeight 5 = 40/621 := rfl
@[simp] theorem sevenThreeStallWeight_six : sevenThreeStallWeight 6 = 2/207 := rfl

/-- **The witness design.**  Every entry is rational and Parseval is an exact identity. -/
noncomputable def sevenThreeStallDesign : WeightedDesign 7 3 where
  atom := sevenThreeStallAtom
  weight := sevenThreeStallWeight
  weight_pos := by
    intro atomIndex
    fin_cases atomIndex <;> norm_num [sevenThreeStallWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_seven]
    simp only [sevenThreeStallWeight_zero, sevenThreeStallWeight_one, sevenThreeStallWeight_two, sevenThreeStallWeight_three,
      sevenThreeStallWeight_four, sevenThreeStallWeight_five, sevenThreeStallWeight_six]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      smul_eq_mul, Fin.sum_univ_seven, sevenThreeStallAtom_zero, sevenThreeStallAtom_one, sevenThreeStallAtom_two,
      sevenThreeStallAtom_three, sevenThreeStallAtom_four, sevenThreeStallAtom_five, sevenThreeStallAtom_six, sevenThreeStallWeight_zero,
      sevenThreeStallWeight_one, sevenThreeStallWeight_two, sevenThreeStallWeight_three, sevenThreeStallWeight_four,
      sevenThreeStallWeight_five, sevenThreeStallWeight_six]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp only [Matrix.one_apply_eq] <;>
      norm_num

@[simp] theorem sevenThreeStallDesign_atom : sevenThreeStallDesign.atom = sevenThreeStallAtom := rfl
@[simp] theorem sevenThreeStallDesign_weight : sevenThreeStallDesign.weight = sevenThreeStallWeight := rfl

/-- **The design is strictly all-heavy**: the smallest leverage is `27/25`.  So the
counterexample is not a light-atom degeneracy — `dominating_of_light_atom` does not touch
it, and it lives inside the campaign's sharpened frontier `GtzWeightedHeavy`. -/
theorem allHeavy_sevenThreeStallDesign : AllHeavy sevenThreeStallDesign := by
  intro atomIndex
  have hmem : atomIndex ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by
    revert atomIndex
    decide
  fin_cases hmem <;>
    norm_num [leverageOf, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]

/-- The stalled triple. -/
def sevenThreeStallTriple : Finset (Fin 7) := {0, 3, 5}

theorem card_sevenThreeStallTriple : sevenThreeStallTriple.card = 3 := by decide

/-! ## The stalled triple fails, but only just -/

/-- **The stalled triple does not dominate.**  Its Gram is `(9/25)·!![5,1,1; 1,3,1; 1,1,5]`,
whose least eigenvalue is `(9/50)(9 − √17) < 1`; the direction `(0, 2, −1)` exhibits a gap
of `−8/25`. -/
theorem not_dominates_sevenThreeStallTriple : ¬ Dominates sevenThreeStallDesign sevenThreeStallTriple := by
  rw [dominates_iff_leastEigenvalueAtLeast_one]
  refine not_leastEigenvalueAtLeast_of_witness sevenThreeStallDesign sevenThreeStallTriple 1 ![0, 2, -1] ?_
  simp only [sevenThreeStallTriple, sevenThreeStallDesign_atom]
  rw [sum_over_triple _ (by decide) (by decide) (by decide)]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

/-- **The stalled triple reaches level `4/5`**, by the sum-of-squares identity

    29375·(Σ_{c∈C}(g_c·x)² − (4/5)|x|²)
      = 47(25x₀ + 9x₁ + 9x₂)² + 2(47x₁ + 72x₂)² + 15200·x₂².

`4/5` is the rational separator every certificate below undercuts. -/
theorem hasLeastEigenvalueAtLeast_sevenThreeStallTriple :
    HasLeastEigenvalueAtLeast sevenThreeStallDesign sevenThreeStallTriple (4/5) := by
  rw [hasLeastEigenvalueAtLeast_iff]
  intro direction
  simp only [sevenThreeStallTriple, sevenThreeStallDesign_atom]
  rw [sum_over_triple _ (by decide) (by decide) (by decide)]
  simp only [sevenThreeStallAtom_zero, sevenThreeStallAtom_three, sevenThreeStallAtom_five, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  nlinarith [sq_nonneg (25 * direction 0 + 9 * direction 1 + 9 * direction 2),
    sq_nonneg (47 * direction 1 + 72 * direction 2), sq_nonneg (direction 2)]

/-! ## Every triple meeting the stalled one falls below `4/5`

Four ambient sets carry a direction that every one of their atoms under-covers, which
refutes all their three-element subsets at once; five further triples take an individual
direction. -/

theorem bound_sevenThreeFamilyOne :
    ∀ c ∈ ({0, 1, 3, 4, 6} : Finset (Fin 7)),
      (sevenThreeStallDesign.atom c ⬝ᵥ ![0, 1, -1]) ^ 2 ≤ 9/25 := by
  intro c hc
  fin_cases hc <;>
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

theorem bound_sevenThreeFamilyTwo :
    ∀ c ∈ ({2, 3, 4, 5, 6} : Finset (Fin 7)),
      (sevenThreeStallDesign.atom c ⬝ᵥ ![3, -3, -2]) ^ 2 ≤ 144/25 := by
  intro c hc
  fin_cases hc <;>
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

theorem bound_sevenThreeFamilyThree :
    ∀ c ∈ ({0, 1, 4, 5, 6} : Finset (Fin 7)),
      (sevenThreeStallDesign.atom c ⬝ᵥ ![2, 3, -3]) ^ 2 ≤ 144/25 := by
  intro c hc
  fin_cases hc <;>
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

theorem bound_sevenThreeFamilyFour :
    ∀ c ∈ ({0, 2, 3, 4, 6} : Finset (Fin 7)),
      (sevenThreeStallDesign.atom c ⬝ᵥ ![1, -1, 0]) ^ 2 ≤ 9/25 := by
  intro c hc
  fin_cases hc <;>
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

theorem not_leastEigenvalueAtLeast_sevenThreeFamilyOne {selected : Finset (Fin 7)}
    (hsubset : selected ⊆ ({0, 1, 3, 4, 6} : Finset (Fin 7))) (hcard : selected.card = 3) :
    ¬ HasLeastEigenvalueAtLeast sevenThreeStallDesign selected (4/5) := by
  refine not_leastEigenvalueAtLeast_of_subsetBound sevenThreeStallDesign (4/5) (9/25) ![0, 1, -1]
    hsubset hcard bound_sevenThreeFamilyOne ?_
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

theorem not_leastEigenvalueAtLeast_sevenThreeFamilyTwo {selected : Finset (Fin 7)}
    (hsubset : selected ⊆ ({2, 3, 4, 5, 6} : Finset (Fin 7))) (hcard : selected.card = 3) :
    ¬ HasLeastEigenvalueAtLeast sevenThreeStallDesign selected (4/5) := by
  refine not_leastEigenvalueAtLeast_of_subsetBound sevenThreeStallDesign (4/5) (144/25) ![3, -3, -2]
    hsubset hcard bound_sevenThreeFamilyTwo ?_
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

theorem not_leastEigenvalueAtLeast_sevenThreeFamilyThree {selected : Finset (Fin 7)}
    (hsubset : selected ⊆ ({0, 1, 4, 5, 6} : Finset (Fin 7))) (hcard : selected.card = 3) :
    ¬ HasLeastEigenvalueAtLeast sevenThreeStallDesign selected (4/5) := by
  refine not_leastEigenvalueAtLeast_of_subsetBound sevenThreeStallDesign (4/5) (144/25) ![2, 3, -3]
    hsubset hcard bound_sevenThreeFamilyThree ?_
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

theorem not_leastEigenvalueAtLeast_sevenThreeFamilyFour {selected : Finset (Fin 7)}
    (hsubset : selected ⊆ ({0, 2, 3, 4, 6} : Finset (Fin 7))) (hcard : selected.card = 3) :
    ¬ HasLeastEigenvalueAtLeast sevenThreeStallDesign selected (4/5) := by
  refine not_leastEigenvalueAtLeast_of_subsetBound sevenThreeStallDesign (4/5) (9/25) ![1, -1, 0]
    hsubset hcard bound_sevenThreeFamilyFour ?_
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

theorem not_leastEigenvalueAtLeast_sevenThreeOneTwoFive :
    ¬ HasLeastEigenvalueAtLeast sevenThreeStallDesign {1, 2, 5} (4/5) := by
  refine not_leastEigenvalueAtLeast_of_witness sevenThreeStallDesign _ _ ![1, 1, 1] ?_
  simp only [sevenThreeStallDesign_atom]
  rw [sum_over_triple _ (by decide) (by decide) (by decide)]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

theorem not_leastEigenvalueAtLeast_sevenThreeZeroOneTwo :
    ¬ HasLeastEigenvalueAtLeast sevenThreeStallDesign {0, 1, 2} (4/5) := by
  refine not_leastEigenvalueAtLeast_of_witness sevenThreeStallDesign _ _ ![3, 1, 2] ?_
  simp only [sevenThreeStallDesign_atom]
  rw [sum_over_triple _ (by decide) (by decide) (by decide)]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

theorem not_leastEigenvalueAtLeast_sevenThreeZeroTwoFive :
    ¬ HasLeastEigenvalueAtLeast sevenThreeStallDesign {0, 2, 5} (4/5) := by
  refine not_leastEigenvalueAtLeast_of_witness sevenThreeStallDesign _ _ ![1, 0, 0] ?_
  simp only [sevenThreeStallDesign_atom]
  rw [sum_over_triple _ (by decide) (by decide) (by decide)]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

theorem not_leastEigenvalueAtLeast_sevenThreeOneTwoThree :
    ¬ HasLeastEigenvalueAtLeast sevenThreeStallDesign {1, 2, 3} (4/5) := by
  refine not_leastEigenvalueAtLeast_of_witness sevenThreeStallDesign _ _ ![2, 1, 3] ?_
  simp only [sevenThreeStallDesign_atom]
  rw [sum_over_triple _ (by decide) (by decide) (by decide)]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

theorem not_leastEigenvalueAtLeast_sevenThreeOneThreeFive :
    ¬ HasLeastEigenvalueAtLeast sevenThreeStallDesign {1, 3, 5} (4/5) := by
  refine not_leastEigenvalueAtLeast_of_witness sevenThreeStallDesign _ _ ![0, 0, 1] ?_
  simp only [sevenThreeStallDesign_atom]
  rw [sum_over_triple _ (by decide) (by decide) (by decide)]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

set_option maxRecDepth 8000 in
/-- **The whole radius-two neighbourhood falls below the separator.**  Which certificate
applies to which triple is a decidable fact about `Finset (Fin 7)`: every three-element
subset that meets `{0,3,5}` and differs from it lies inside one of four ambient sets or is
one of five named triples. -/
theorem not_leastEigenvalueAtLeast_of_meetsSevenThreeStall (selected : Finset (Fin 7))
    (hcard : selected.card = 3) (hmeets : 1 ≤ (sevenThreeStallTriple ∩ selected).card)
    (hdistinct : selected ≠ sevenThreeStallTriple) :
    ¬ HasLeastEigenvalueAtLeast sevenThreeStallDesign selected (4/5) := by
  have hcover : selected ⊆ ({0, 1, 3, 4, 6} : Finset (Fin 7))
      ∨ selected ⊆ ({2, 3, 4, 5, 6} : Finset (Fin 7))
      ∨ selected ⊆ ({0, 1, 4, 5, 6} : Finset (Fin 7))
      ∨ selected ⊆ ({0, 2, 3, 4, 6} : Finset (Fin 7))
      ∨ selected = ({1, 2, 5} : Finset (Fin 7)) ∨ selected = ({0, 1, 2} : Finset (Fin 7))
      ∨ selected = ({0, 2, 5} : Finset (Fin 7)) ∨ selected = ({1, 2, 3} : Finset (Fin 7))
      ∨ selected = ({1, 3, 5} : Finset (Fin 7)) := by
    revert hcard hmeets hdistinct
    revert selected
    decide
  rcases hcover with hsub | hsub | hsub | hsub | rfl | rfl | rfl | rfl | rfl
  · exact not_leastEigenvalueAtLeast_sevenThreeFamilyOne hsub hcard
  · exact not_leastEigenvalueAtLeast_sevenThreeFamilyTwo hsub hcard
  · exact not_leastEigenvalueAtLeast_sevenThreeFamilyThree hsub hcard
  · exact not_leastEigenvalueAtLeast_sevenThreeFamilyFour hsub hcard
  · exact not_leastEigenvalueAtLeast_sevenThreeOneTwoFive
  · exact not_leastEigenvalueAtLeast_sevenThreeZeroOneTwo
  · exact not_leastEigenvalueAtLeast_sevenThreeZeroTwoFive
  · exact not_leastEigenvalueAtLeast_sevenThreeOneTwoThree
  · exact not_leastEigenvalueAtLeast_sevenThreeOneThreeFive

/-- **GTZ holds at the witness.**  The atoms `g_1, g_2, g_4` are pairwise orthogonal of
common squared length `81/25`, so the triple's Gram is exactly `(81/25)·I` and its gap is
`(56/25)·I`.  It is DISJOINT from the stalled triple — which is not an accident but the
mechanism: a dominator sits at level one, strictly above a failing subset, so a stall of
radius `r` forces every dominator past exchange distance `r`. -/
theorem dominates_sevenThreeDominatingTriple : Dominates sevenThreeStallDesign {1, 2, 4} := by
  rw [dominates_iff_leastEigenvalueAtLeast_one, hasLeastEigenvalueAtLeast_iff]
  intro direction
  simp only [sevenThreeStallDesign_atom]
  rw [sum_over_triple _ (by decide) (by decide) (by decide)]
  simp only [sevenThreeStallAtom_one, sevenThreeStallAtom_two, sevenThreeStallAtom_four, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  nlinarith [sq_nonneg (direction 0), sq_nonneg (direction 1), sq_nonneg (direction 2)]

/-- The second dominator, `{1,2,6}`: its gap `(1/25)·!![56,18,0; 18,83,18; 0,18,56]` is the
sum of squares `1081(28x₀+9x₁)² + (1081x₁+252x₂)² + 784000x₂²` over `25·15134`.  It too is
disjoint from the stalled triple. -/
theorem dominates_sevenThreeSecondDominatingTriple : Dominates sevenThreeStallDesign {1, 2, 6} := by
  rw [dominates_iff_leastEigenvalueAtLeast_one, hasLeastEigenvalueAtLeast_iff]
  intro direction
  simp only [sevenThreeStallDesign_atom]
  rw [sum_over_triple _ (by decide) (by decide) (by decide)]
  simp only [sevenThreeStallAtom_one, sevenThreeStallAtom_two, sevenThreeStallAtom_six, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  nlinarith [sq_nonneg (28 * direction 0 + 9 * direction 1),
    sq_nonneg (1081 * direction 1 + 252 * direction 2), sq_nonneg (direction 2)]

/-- **Both dominators sit outside the stalled triple**, which is exactly what makes the
radius-two neighbourhood a dead end. -/
theorem disjoint_sevenThreeStallTriple_dominators :
    Disjoint sevenThreeStallTriple ({1, 2, 4} : Finset (Fin 7))
      ∧ Disjoint sevenThreeStallTriple ({1, 2, 6} : Finset (Fin 7)) := by
  constructor <;> decide

/-! ### The refutation at the least eigenvalue, size seven -/

/-- **The stalled triple is radius-two stuck for every least-eigenvalue score.** It
reaches the rational level `4/5`; every `3`-subset within exchange distance two —
equivalently, every one sharing an atom with it — falls strictly below `4/5`. -/
theorem sevenThreeStallTriple_isExchangeStuck
    (score : WeightedDesign 7 3 → Finset (Fin 7) → ℝ)
    (hscore : IsLeastEigenvalueScore score) :
    IsExchangeStuck 2 score sevenThreeStallDesign sevenThreeStallTriple := by
  intro candidate hcard hdistance hstrict
  rcases eq_or_ne candidate sevenThreeStallTriple with rfl | hdistinct
  · exact lt_irrefl _ hstrict
  · have hcandidateCard : candidate.card = 3 := by
      rw [hcard, card_sevenThreeStallTriple]
    have hstallLevel : (4/5 : ℝ) ≤ score sevenThreeStallDesign sevenThreeStallTriple :=
      (hscore sevenThreeStallDesign sevenThreeStallTriple (4/5)).mpr
        hasLeastEigenvalueAtLeast_sevenThreeStallTriple
    have hoverlap := (exchangeDistance_le_iff_le_card_inter_add
      (size := 3) (radius := 2) hcandidateCard).mp hdistance
    have hmeets : 1 ≤ (sevenThreeStallTriple ∩ candidate).card := by omega
    have hcandidateBelow : ¬ ((4/5 : ℝ) ≤ score sevenThreeStallDesign candidate) := fun hge =>
      not_leastEigenvalueAtLeast_of_meetsSevenThreeStall candidate hcandidateCard hmeets
        hdistinct ((hscore sevenThreeStallDesign candidate (4/5)).mp hge)
    push Not at hcandidateBelow
    linarith

/-- **THE REFUTATION AT THE LEAST EIGENVALUE, SIZE SEVEN.**

`sevenThreeStallDesign` is a genuine, strictly all-heavy weighted `(7,3)`-design. Its
triple `{0,3,5}` fails to dominate yet reaches level `4/5`, while every triple meeting it
falls strictly below `4/5`. Any score obeying the least-eigenvalue specification therefore
has no strictly larger value inside the radius-two neighbourhood.

This is not evidence against GTZ: the same design satisfies it —
`dominates_sevenThreeDominatingTriple` and `dominates_sevenThreeSecondDominatingTriple`
exhibit `{1,2,4}` and `{1,2,6}`. Both are DISJOINT from `{0,3,5}`, which is forced: a
dominator sits at level `1`, strictly above a failing subset, so a radius-`r` stall pushes
every dominator beyond exchange distance `r`. -/
theorem not_exchangeImprovesWithinRadius_two_sevenThree
    (score : WeightedDesign 7 3 → Finset (Fin 7) → ℝ)
    (hscore : IsLeastEigenvalueScore score) :
    ¬ DoesExchangeImproveWithinRadius 7 3 2 score := by
  intro himproves
  obtain ⟨improved, hcardImproved, hdistance, hstrict⟩ :=
    himproves sevenThreeStallDesign sevenThreeStallTriple card_sevenThreeStallTriple
      not_dominates_sevenThreeStallTriple
  exact sevenThreeStallTriple_isExchangeStuck score hscore improved
    (by rw [hcardImproved, card_sevenThreeStallTriple]) hdistance hstrict

/-- **The all-heavy form**, which is the one the campaign's reduction to all-heavy designs
would have consumed. -/
theorem not_exchangeImprovesWithinRadiusHeavy_two_sevenThree
    (score : WeightedDesign 7 3 → Finset (Fin 7) → ℝ)
    (hscore : IsLeastEigenvalueScore score) :
    ¬ DoesExchangeImproveWithinRadiusHeavy 7 3 2 score := by
  intro himproves
  obtain ⟨improved, hcardImproved, hdistance, hstrict⟩ :=
    himproves sevenThreeStallDesign allHeavy_sevenThreeStallDesign sevenThreeStallTriple
      card_sevenThreeStallTriple not_dominates_sevenThreeStallTriple
  exact sevenThreeStallTriple_isExchangeStuck score hscore improved
    (by rw [hcardImproved, card_sevenThreeStallTriple]) hdistance hstrict

/-- **Every radius below the rank is dead at size seven too**, by monotonicity. -/
theorem not_exchangeImprovesWithinRadius_of_le_two_sevenThree {radius : ℕ}
    (hradius : radius ≤ 2) (score : WeightedDesign 7 3 → Finset (Fin 7) → ℝ)
    (hscore : IsLeastEigenvalueScore score) :
    ¬ DoesExchangeImproveWithinRadius 7 3 radius score := fun htight =>
  not_exchangeImprovesWithinRadius_two_sevenThree score hscore
    (doesExchangeImproveWithinRadius_mono hradius score htight)

/-- **The canonical `sSup` score is refuted**, so the statement is not about an empty
class of scores. -/
theorem not_exchangeImprovesWithinRadius_two_leastEigenvalueScore :
    ¬ DoesExchangeImproveWithinRadius 7 3 2 (leastEigenvalueScore (m := 7) (k := 3)) :=
  not_exchangeImprovesWithinRadius_two_sevenThree _
    (isLeastEigenvalueScore_leastEigenvalueScore (by omega))

/-- **The SHIPPED score is refuted.** `Gtz.leastEigenvalue` — the `lambdaMinMat` of the
subset atom sum, the score every other module of this campaign computes with — meets the
specification (`isLeastEigenvalueScore_leastEigenvalue`), so the stall applies to it
literally, not merely to an abstract description. -/
theorem not_exchangeImprovesWithinRadius_two_leastEigenvalue :
    ¬ DoesExchangeImproveWithinRadius 7 3 2 (leastEigenvalue (m := 7) (k := 3)) :=
  not_exchangeImprovesWithinRadius_two_sevenThree _ isLeastEigenvalueScore_leastEigenvalue

/-- The shipped score, all-heavy form. -/
theorem not_exchangeImprovesWithinRadiusHeavy_two_leastEigenvalue :
    ¬ DoesExchangeImproveWithinRadiusHeavy 7 3 2 (leastEigenvalue (m := 7) (k := 3)) :=
  not_exchangeImprovesWithinRadiusHeavy_two_sevenThree _ isLeastEigenvalueScore_leastEigenvalue

/-- **The stall in one statement**: a strictly all-heavy `(7,3)`-design, a failing triple
that separates from its entire radius-two neighbourhood at the rational level `4/5`, and a
dominating triple to certify that GTZ itself is untouched. -/
theorem exists_allHeavy_sevenThreeRadiusTwoStall :
    ∃ (D : WeightedDesign 7 3) (C : Finset (Fin 7)),
      AllHeavy D ∧ C.card = 3 ∧ ¬ Dominates D C ∧ HasLeastEigenvalueAtLeast D C (4/5) ∧
        (∀ selected : Finset (Fin 7), selected.card = 3 → 1 ≤ (C ∩ selected).card →
          selected ≠ C → ¬ HasLeastEigenvalueAtLeast D selected (4/5)) ∧
        (∃ dominator : Finset (Fin 7), dominator.card = 3 ∧ Dominates D dominator ∧
          Disjoint C dominator) :=
  ⟨sevenThreeStallDesign, sevenThreeStallTriple, allHeavy_sevenThreeStallDesign,
    card_sevenThreeStallTriple, not_dominates_sevenThreeStallTriple,
    hasLeastEigenvalueAtLeast_sevenThreeStallTriple,
    not_leastEigenvalueAtLeast_of_meetsSevenThreeStall,
    ⟨{1, 2, 4}, by decide, dominates_sevenThreeDominatingTriple,
      disjoint_sevenThreeStallTriple_dominators.1⟩⟩

/-! # Witness C — the clipped trace at size seven -/

/-! ## The (7,3) witness -/

/-- **The counterexample design.**  Atoms `g_c = v_c / 6` with `v_c` integral, weights
`w_c / 15182636952`.  Parseval is the integer identity
`sum_c w_c v_c v_c^T = 36 * 15182636952 * I`, so it holds exactly. -/
noncomputable def clippedTraceStallDesign : WeightedDesign 7 3 where
  atom := ![![9 / 6, -6 / 6, -16 / 6], ![11 / 6, 4 / 6, 6 / 6], ![4 / 6, -15 / 6, 2 / 6],
            ![0 / 6, -5 / 6, -4 / 6], ![-5 / 6, 3 / 6, -2 / 6], ![-3 / 6, -4 / 6, 4 / 6],
            ![-2 / 6, 8 / 6, -4 / 6]]
  weight := ![1174232565 / 15182636952, 2759188692 / 15182636952, 777972318 / 15182636952,
              917496292 / 15182636952, 2000931882 / 15182636952, 4983629165 / 15182636952,
              2569186038 / 15182636952]
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num
  weight_sum_one := by simp [Fin.sum_univ_seven]; norm_num
  isParseval := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Fin.sum_univ_seven, atomMatrix] <;> norm_num

/-- **Strict all-heaviness**: every leverage exceeds one, the smallest being `38/36`
and the largest `373/36`.  The witness lives inside the regime the campaign's
gate-cap analysis assumes, not at a degenerate corner. -/
theorem clippedTraceStallDesign_isAllHeavy : AllHeavy clippedTraceStallDesign := by
  intro atomIndex
  fin_cases atomIndex <;>
    simp [leverageOf, clippedTraceStallDesign, Fin.sum_univ_three] <;> norm_num

/-- The stalled subset. -/
def clippedTraceStallSubset : Finset (Fin 7) := {3, 4, 5}

theorem clippedTraceStallSubset_card : clippedTraceStallSubset.card = 3 := by decide

/-- `36 * S_C = [[34,-3,-2],[-3,50,-2],[-2,-2,36]]`. -/
theorem subsetSum_clippedTraceStallSubset :
    subsetSum clippedTraceStallDesign clippedTraceStallSubset
      = !![17 / 18, -1 / 12, -1 / 18; -1 / 12, 25 / 18, -1 / 18; -1 / 18, -1 / 18, 1] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [subsetSum_apply, clippedTraceStallDesign, clippedTraceStallSubset] <;> norm_num

/-- The domination gap `S_C - I` in closed form. -/
theorem clippedTraceStallSubset_gap :
    subsetSum clippedTraceStallDesign clippedTraceStallSubset - 1
      = !![-1 / 18, -1 / 12, -1 / 18; -1 / 12, 7 / 18, -1 / 18; -1 / 18, -1 / 18, 0] := by
  rw [subsetSum_clippedTraceStallSubset]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- **The stalled subset fails to dominate**: `det (S_C - I) = -1/648 < 0`, and a
positive semidefinite matrix has nonnegative determinant. -/
theorem clippedTraceStallSubset_not_dominates : ¬ Dominates clippedTraceStallDesign clippedTraceStallSubset := by
  intro hDominates
  have hDetNonneg : 0 ≤ (subsetSum clippedTraceStallDesign clippedTraceStallSubset - 1).det :=
    Matrix.PosSemidef.det_nonneg
      (show (subsetSum clippedTraceStallDesign clippedTraceStallSubset - 1).PosSemidef from hDominates)
  rw [clippedTraceStallSubset_gap] at hDetNonneg
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.tail_cons] at hDetNonneg

/-- The Loewner floor `S_C - (3/4) I` in closed form. -/
theorem clippedTraceStallSubset_floorGap :
    subsetSum clippedTraceStallDesign clippedTraceStallSubset - (3 / 4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = !![7 / 36, -1 / 12, -1 / 18; -1 / 12, 23 / 36, -1 / 18; -1 / 18, -1 / 18, 1 / 4] := by
  rw [subsetSum_clippedTraceStallSubset]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- `36 S_C - 27 I` has quadratic form `(133(7x-3y-2z)^2 + 14(38y-5z)^2 + 7497 z^2)
/ 931`, a positive combination of squares.  Hence `S_C - (3/4) I` is positive
semidefinite and every eigenvalue of `S_C` is at least `3/4`. -/
theorem clippedTraceStallSubset_floorPsd :
    (subsetSum clippedTraceStallDesign clippedTraceStallSubset
      - (3 / 4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_sub_smul_one (subsetSum_isHermitian clippedTraceStallDesign clippedTraceStallSubset) (3 / 4),
      fun direction => ?_⟩
  rw [star_trivial, clippedTraceStallSubset_floorGap]
  have hForm : direction ⬝ᵥ (!![7 / 36, -1 / 12, -1 / 18; -1 / 12, 23 / 36, -1 / 18;
        -1 / 18, -1 / 18, 1 / 4] *ᵥ direction)
      = (7 * direction 0 ^ 2 + 23 * direction 1 ^ 2 + 9 * direction 2 ^ 2
          - 6 * direction 0 * direction 1 - 4 * direction 0 * direction 2
          - 4 * direction 1 * direction 2) / 36 := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hForm]
  nlinarith [sq_nonneg (7 * direction 0 - 3 * direction 1 - 2 * direction 2),
    sq_nonneg (38 * direction 1 - 5 * direction 2), sq_nonneg (direction 2)]

/-- The reflected gap `I - S_C` in closed form. -/
theorem clippedTraceStallSubset_reflectedGap :
    (1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - subsetSum clippedTraceStallDesign clippedTraceStallSubset
      = !![1 / 18, 1 / 12, 1 / 18; 1 / 12, -7 / 18, 1 / 18; 1 / 18, 1 / 18, 0] := by
  rw [subsetSum_clippedTraceStallSubset]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- `det (I - S_C) = 1/648 > 0`: an EVEN number of eigenvalues of `S_C` exceed one. -/
theorem clippedTraceStallSubset_reflectedDetPos :
    0 < ((1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - subsetSum clippedTraceStallDesign clippedTraceStallSubset).det := by
  rw [clippedTraceStallSubset_reflectedGap]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.tail_cons]

/-- `tr S_C = 10/3 > 3`: not every eigenvalue of `S_C` lies below one. -/
theorem clippedTraceStallSubset_traceGt : 3 < Matrix.trace (subsetSum clippedTraceStallDesign clippedTraceStallSubset) := by
  rw [subsetSum_clippedTraceStallSubset, Matrix.trace_fin_three]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

/-- `36 * S_{0,1,6} = [[206,-26,-70],[-26,116,88],[-70,88,308]]`. -/
theorem subsetSum_clippedTraceStallDominator :
    subsetSum clippedTraceStallDesign {0, 1, 6}
      = !![103 / 18, -13 / 18, -35 / 18; -13 / 18, 29 / 9, 22 / 9; -35 / 18, 22 / 9, 77 / 9] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [subsetSum_apply, clippedTraceStallDesign] <;> norm_num

/-- The domination gap at `{0,1,6}` in closed form. -/
theorem clippedTraceStallDominator_gap :
    subsetSum clippedTraceStallDesign {0, 1, 6} - 1
      = !![85 / 18, -13 / 18, -35 / 18; -13 / 18, 20 / 9, 22 / 9; -35 / 18, 22 / 9, 68 / 9] := by
  rw [subsetSum_clippedTraceStallDominator]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- **The witness design satisfies GTZ**: `{0,1,6}` dominates.  Cholesky in integers —
with `Q = 36 * (gap form)`,

    170 * 12924 * Q = 12924 (170x - 26y - 70z)^2 + (12924y + 13140z)^2 + 361618560 z^2,

an identity with all three coefficients positive. -/
theorem clippedTraceStallDominator_dominates : Dominates clippedTraceStallDesign {0, 1, 6} := by
  show (subsetSum clippedTraceStallDesign {0, 1, 6} - 1).PosSemidef
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨(subsetSum_isHermitian clippedTraceStallDesign {0, 1, 6}).sub Matrix.isHermitian_one,
      fun direction => ?_⟩
  rw [star_trivial, clippedTraceStallDominator_gap]
  have hForm : direction ⬝ᵥ (!![85 / 18, -13 / 18, -35 / 18; -13 / 18, 20 / 9, 22 / 9;
        -35 / 18, 22 / 9, 68 / 9] *ᵥ direction)
      = (170 * direction 0 ^ 2 + 80 * direction 1 ^ 2 + 272 * direction 2 ^ 2
          - 52 * direction 0 * direction 1 - 140 * direction 0 * direction 2
          + 176 * direction 1 * direction 2) / 36 := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hForm]
  nlinarith [sq_nonneg (170 * direction 0 - 26 * direction 1 - 70 * direction 2),
    sq_nonneg (12924 * direction 1 + 13140 * direction 2), sq_nonneg (direction 2)]

/-- **GTZ holds for the witness design.**  So the refutation below is a defect of the
SCORE, not evidence against the conjecture: the dominating subsets exist, they are
simply all at exchange distance three from the stalled subset. -/
theorem clippedTraceStallDesign_hasDominatingSubset :
    ∃ selected : Finset (Fin 7), selected.card = 3 ∧ Dominates clippedTraceStallDesign selected :=
  ⟨{0, 1, 6}, by decide, clippedTraceStallDominator_dominates⟩

/-- **The stalled subset scores at least `11/4`.** -/
theorem clippedTraceStallSubset_clippedTrace_ge : 11 / 4 ≤ clippedTrace clippedTraceStallDesign clippedTraceStallSubset := by
  have hBound := clippedTrace_ge_of_certificates clippedTraceStallDesign clippedTraceStallSubset (3 / 4) (by norm_num)
    clippedTraceStallSubset_floorPsd clippedTraceStallSubset_reflectedDetPos clippedTraceStallSubset_traceGt
  linarith

/-- The thirty subsets at exchange distance at most two from the stalled subset. -/
theorem clippedTraceNeighbour_cases (selected : Finset (Fin 7)) (hCard : selected.card = 3)
    (hMeets : 1 ≤ (({3, 4, 5} : Finset (Fin 7)) ∩ selected).card)
    (hDistinct : selected ≠ ({3, 4, 5} : Finset (Fin 7))) :
    selected = ({0, 1, 3} : Finset (Fin 7)) ∨
    selected = ({0, 1, 4} : Finset (Fin 7)) ∨
    selected = ({0, 1, 5} : Finset (Fin 7)) ∨
    selected = ({0, 2, 3} : Finset (Fin 7)) ∨
    selected = ({0, 2, 4} : Finset (Fin 7)) ∨
    selected = ({0, 2, 5} : Finset (Fin 7)) ∨
    selected = ({0, 3, 4} : Finset (Fin 7)) ∨
    selected = ({0, 3, 5} : Finset (Fin 7)) ∨
    selected = ({0, 3, 6} : Finset (Fin 7)) ∨
    selected = ({0, 4, 5} : Finset (Fin 7)) ∨
    selected = ({0, 4, 6} : Finset (Fin 7)) ∨
    selected = ({0, 5, 6} : Finset (Fin 7)) ∨
    selected = ({1, 2, 3} : Finset (Fin 7)) ∨
    selected = ({1, 2, 4} : Finset (Fin 7)) ∨
    selected = ({1, 2, 5} : Finset (Fin 7)) ∨
    selected = ({1, 3, 4} : Finset (Fin 7)) ∨
    selected = ({1, 3, 5} : Finset (Fin 7)) ∨
    selected = ({1, 3, 6} : Finset (Fin 7)) ∨
    selected = ({1, 4, 5} : Finset (Fin 7)) ∨
    selected = ({1, 4, 6} : Finset (Fin 7)) ∨
    selected = ({1, 5, 6} : Finset (Fin 7)) ∨
    selected = ({2, 3, 4} : Finset (Fin 7)) ∨
    selected = ({2, 3, 5} : Finset (Fin 7)) ∨
    selected = ({2, 3, 6} : Finset (Fin 7)) ∨
    selected = ({2, 4, 5} : Finset (Fin 7)) ∨
    selected = ({2, 4, 6} : Finset (Fin 7)) ∨
    selected = ({2, 5, 6} : Finset (Fin 7)) ∨
    selected = ({3, 4, 6} : Finset (Fin 7)) ∨
    selected = ({3, 5, 6} : Finset (Fin 7)) ∨
    selected = ({4, 5, 6} : Finset (Fin 7)) := by
  revert hCard hMeets hDistinct
  revert selected
  decide

/-- Neighbour `{0, 1, 3}`: `det (3 / 4 * I - S_T) = 542575/23328 > 0`. -/
theorem clippedTraceNeighbour_013_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({0, 1, 3} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {0, 1, 3} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{0, 1, 4}`: `det (3 / 4 * I - S_T) = 707741/46656 > 0`. -/
theorem clippedTraceNeighbour_014_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({0, 1, 4} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {0, 1, 4} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{0, 1, 5}`: `det (3 / 4 * I - S_T) = 15059/2916 > 0`. -/
theorem clippedTraceNeighbour_015_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({0, 1, 5} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {0, 1, 5} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{0, 2, 3}`: `det (3 / 4 * I - S_T) = 681565/23328 > 0`. -/
theorem clippedTraceNeighbour_023_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({0, 2, 3} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {0, 2, 3} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{0, 2, 4}`: `det (3 / 4 * I - S_T) = 5015/324 > 0`. -/
theorem clippedTraceNeighbour_024_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({0, 2, 4} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {0, 2, 4} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{0, 2, 5}`: `det (3 / 4 * I - S_T) = 918373/23328 > 0`. -/
theorem clippedTraceNeighbour_025_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({0, 2, 5} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {0, 2, 5} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{0, 3, 4}`: `det (3 / 4 * I - S_T) = 8381/11664 > 0`. -/
theorem clippedTraceNeighbour_034_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({0, 3, 4} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {0, 3, 4} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{0, 3, 5}`: `det (3 / 4 * I - S_T) = 9703/2592 > 0`. -/
theorem clippedTraceNeighbour_035_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({0, 3, 5} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {0, 3, 5} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{0, 3, 6}`: `det (3 / 4 * I - S_T) = 26117/2916 > 0`. -/
theorem clippedTraceNeighbour_036_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({0, 3, 6} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {0, 3, 6} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{0, 4, 5}`: `det (3 / 4 * I - S_T) = 38969/46656 > 0`. -/
theorem clippedTraceNeighbour_045_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({0, 4, 5} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {0, 4, 5} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{0, 4, 6}`: `det (3 / 4 * I - S_T) = 443015/46656 > 0`. -/
theorem clippedTraceNeighbour_046_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({0, 4, 6} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {0, 4, 6} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{0, 5, 6}`: `det (3 / 4 * I - S_T) = 601421/46656 > 0`. -/
theorem clippedTraceNeighbour_056_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({0, 5, 6} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {0, 5, 6} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{1, 2, 3}`: `det (3 / 4 * I - S_T) = 33805/2592 > 0`. -/
theorem clippedTraceNeighbour_123_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({1, 2, 3} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {1, 2, 3} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{1, 2, 4}`: `det (3 / 4 * I - S_T) = 129373/5832 > 0`. -/
theorem clippedTraceNeighbour_124_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({1, 2, 4} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {1, 2, 4} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{1, 2, 5}`: `det (3 / 4 * I - S_T) = 283/96 > 0`. -/
theorem clippedTraceNeighbour_125_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({1, 2, 5} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {1, 2, 5} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{1, 3, 4}`: `det (3 / 4 * I - S_T) = 20549/11664 > 0`. -/
theorem clippedTraceNeighbour_134_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({1, 3, 4} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {1, 3, 4} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{1, 3, 5}`: `det (3 / 4 * I - S_T) = 43/2592 > 0`. -/
theorem clippedTraceNeighbour_135_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({1, 3, 5} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {1, 3, 5} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{1, 3, 6}`: `det (3 / 4 * I - S_T) = 27563/11664 > 0`. -/
theorem clippedTraceNeighbour_136_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({1, 3, 6} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {1, 3, 6} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{1, 4, 5}`: `det (3 / 4 * I - S_T) = 44141/46656 > 0`. -/
theorem clippedTraceNeighbour_145_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({1, 4, 5} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {1, 4, 5} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{1, 4, 6}`: `det (3 / 4 * I - S_T) = 275903/46656 > 0`. -/
theorem clippedTraceNeighbour_146_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({1, 4, 6} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {1, 4, 6} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{1, 5, 6}`: `det (3 / 4 * I - S_T) = 208805/46656 > 0`. -/
theorem clippedTraceNeighbour_156_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({1, 5, 6} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {1, 5, 6} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{2, 3, 4}`: `det (3 / 4 * I - S_T) = 28421/46656 > 0`. -/
theorem clippedTraceNeighbour_234_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({2, 3, 4} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {2, 3, 4} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{2, 3, 5}`: `det (3 / 4 * I - S_T) = 2083/2592 > 0`. -/
theorem clippedTraceNeighbour_235_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({2, 3, 5} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {2, 3, 5} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{2, 3, 6}`: `det (3 / 4 * I - S_T) = 29045/46656 > 0`. -/
theorem clippedTraceNeighbour_236_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({2, 3, 6} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {2, 3, 6} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{2, 4, 5}`: `det (3 / 4 * I - S_T) = 8597/11664 > 0`. -/
theorem clippedTraceNeighbour_245_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({2, 4, 5} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {2, 4, 5} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{2, 4, 6}`: `det (1 / 4 * I - S_T) = 8207/46656 > 0`. -/
theorem clippedTraceNeighbour_246_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({2, 4, 6} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {2, 4, 6} (1 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{2, 5, 6}`: `det (3 / 4 * I - S_T) = 2135/11664 > 0`. -/
theorem clippedTraceNeighbour_256_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({2, 5, 6} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {2, 5, 6} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{3, 4, 6}`: `det (3 / 4 * I - S_T) = 15/64 > 0`. -/
theorem clippedTraceNeighbour_346_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({3, 4, 6} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {3, 4, 6} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{3, 5, 6}`: `det (3 / 4 * I - S_T) = 401/1296 > 0`. -/
theorem clippedTraceNeighbour_356_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({3, 5, 6} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {3, 5, 6} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- Neighbour `{4, 5, 6}`: `det (3 / 4 * I - S_T) = 2123/5184 > 0`. -/
theorem clippedTraceNeighbour_456_clippedTrace_lt :
    clippedTrace clippedTraceStallDesign ({4, 5, 6} : Finset (Fin 7)) < 11 / 4 :=
  clippedTrace_lt_of_det_pos clippedTraceStallDesign {4, 5, 6} (3 / 4) (by norm_num) (by
    rw [Matrix.det_fin_three]
    simp [subsetSum_apply, clippedTraceStallDesign, Matrix.sub_apply, Matrix.smul_apply]
    norm_num)

/-- **Every subset within exchange distance two of the stalled subset scores strictly
less than `11/4`.** -/
theorem clippedTraceNeighbour_lt (selected : Finset (Fin 7)) (hCard : selected.card = 3)
    (hMeets : 1 ≤ (clippedTraceStallSubset ∩ selected).card) (hDistinct : selected ≠ clippedTraceStallSubset) :
    clippedTrace clippedTraceStallDesign selected < 11 / 4 := by
  have hCases := clippedTraceNeighbour_cases selected hCard hMeets hDistinct
  rcases hCases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact clippedTraceNeighbour_013_clippedTrace_lt
  · exact clippedTraceNeighbour_014_clippedTrace_lt
  · exact clippedTraceNeighbour_015_clippedTrace_lt
  · exact clippedTraceNeighbour_023_clippedTrace_lt
  · exact clippedTraceNeighbour_024_clippedTrace_lt
  · exact clippedTraceNeighbour_025_clippedTrace_lt
  · exact clippedTraceNeighbour_034_clippedTrace_lt
  · exact clippedTraceNeighbour_035_clippedTrace_lt
  · exact clippedTraceNeighbour_036_clippedTrace_lt
  · exact clippedTraceNeighbour_045_clippedTrace_lt
  · exact clippedTraceNeighbour_046_clippedTrace_lt
  · exact clippedTraceNeighbour_056_clippedTrace_lt
  · exact clippedTraceNeighbour_123_clippedTrace_lt
  · exact clippedTraceNeighbour_124_clippedTrace_lt
  · exact clippedTraceNeighbour_125_clippedTrace_lt
  · exact clippedTraceNeighbour_134_clippedTrace_lt
  · exact clippedTraceNeighbour_135_clippedTrace_lt
  · exact clippedTraceNeighbour_136_clippedTrace_lt
  · exact clippedTraceNeighbour_145_clippedTrace_lt
  · exact clippedTraceNeighbour_146_clippedTrace_lt
  · exact clippedTraceNeighbour_156_clippedTrace_lt
  · exact clippedTraceNeighbour_234_clippedTrace_lt
  · exact clippedTraceNeighbour_235_clippedTrace_lt
  · exact clippedTraceNeighbour_236_clippedTrace_lt
  · exact clippedTraceNeighbour_245_clippedTrace_lt
  · exact clippedTraceNeighbour_246_clippedTrace_lt
  · exact clippedTraceNeighbour_256_clippedTrace_lt
  · exact clippedTraceNeighbour_346_clippedTrace_lt
  · exact clippedTraceNeighbour_356_clippedTrace_lt
  · exact clippedTraceNeighbour_456_clippedTrace_lt

/-! ### The refutation at the clipped trace -/

/-- **The stalled subset is radius-two stuck.** It scores at least `11/4`, and every
`3`-subset within exchange distance two — equivalently, every one sharing an atom with it
(`exchangeDistance_le_iff_le_card_inter_add`) — scores strictly less. -/
theorem clippedTraceStallSubset_isExchangeStuck :
    IsExchangeStuck 2 clippedTrace clippedTraceStallDesign clippedTraceStallSubset := by
  intro candidate hCard hDistance hStrict
  rcases eq_or_ne candidate clippedTraceStallSubset with rfl | hDistinct
  · exact lt_irrefl _ hStrict
  · have hCandidateCard : candidate.card = 3 := by
      rw [hCard, clippedTraceStallSubset_card]
    have hOverlap := (exchangeDistance_le_iff_le_card_inter_add
      (size := 3) (radius := 2) hCandidateCard).mp hDistance
    have hMeets : 1 ≤ (clippedTraceStallSubset ∩ candidate).card := by omega
    have hUpper := clippedTraceNeighbour_lt candidate hCandidateCard hMeets hDistinct
    linarith [clippedTraceStallSubset_clippedTrace_ge]

/-- **THE REFUTATION AT THE CLIPPED TRACE.** No radius-two exchange theorem holds for
the clipped trace at `(7,3)`. Applied to `clippedTraceStallDesign` and `C = {3,4,5}` the
hypothesis would produce a `3`-subset within exchange distance two scoring strictly more;
`C` scores at least `11/4` and every such subset scores strictly less. -/
theorem not_exchangeImprovesWithinRadius_clippedTrace_two :
    ¬ DoesExchangeImproveWithinRadius 7 3 2 clippedTrace := by
  intro hHypothesis
  obtain ⟨improved, hImprovedCard, hDistance, hStrict⟩ :=
    hHypothesis clippedTraceStallDesign clippedTraceStallSubset clippedTraceStallSubset_card
      clippedTraceStallSubset_not_dominates
  exact clippedTraceStallSubset_isExchangeStuck improved
    (by rw [hImprovedCard, clippedTraceStallSubset_card]) hDistance hStrict

/-- **The refutation in the form the campaign needs.** The witness is strictly all-heavy
(`clippedTraceStallDesign_isAllHeavy`), so the same stall refutes the ALL-HEAVY bounded
hypothesis — the weaker hypothesis, hence the stronger refutation, and the one
`gtzWeightedAll_of_heavy_bounded` would have consumed. -/
theorem not_exchangeImprovesWithinRadiusHeavy_clippedTrace_two :
    ¬ DoesExchangeImproveWithinRadiusHeavy 7 3 2 clippedTrace := by
  intro hHypothesis
  obtain ⟨improved, hImprovedCard, hDistance, hStrict⟩ :=
    hHypothesis clippedTraceStallDesign clippedTraceStallDesign_isAllHeavy
      clippedTraceStallSubset clippedTraceStallSubset_card
      clippedTraceStallSubset_not_dominates
  exact clippedTraceStallSubset_isExchangeStuck improved
    (by rw [hImprovedCard, clippedTraceStallSubset_card]) hDistance hStrict

/-- **Radius one falls with radius two**, by monotonicity of the hypothesis in the
radius. -/
theorem not_exchangeImprovesWithinRadius_clippedTrace_of_le_two {radius : ℕ}
    (hRadius : radius ≤ 2) : ¬ DoesExchangeImproveWithinRadius 7 3 radius clippedTrace :=
  fun hNarrow => not_exchangeImprovesWithinRadius_clippedTrace_two
    (doesExchangeImproveWithinRadius_mono hRadius clippedTrace hNarrow)

/-- The all-heavy refutation propagates down the radius the same way. -/
theorem not_exchangeImprovesWithinRadiusHeavy_clippedTrace_of_le_two {radius : ℕ}
    (hRadius : radius ≤ 2) : ¬ DoesExchangeImproveWithinRadiusHeavy 7 3 radius clippedTrace := by
  intro hNarrow
  refine not_exchangeImprovesWithinRadiusHeavy_clippedTrace_two ?_
  intro design hHeavy selected hCard hFails
  obtain ⟨improved, hImprovedCard, hDistance, hStrict⟩ :=
    hNarrow design hHeavy selected hCard hFails
  exact ⟨improved, hImprovedCard, le_trans hDistance hRadius, hStrict⟩

/-- **Every dominating subset of the witness lies at exchange distance three.** A
dominator scores exactly `3`, while every `3`-subset meeting `{3,4,5}` scores below
`11/4` — so the dominators are among the four subsets DISJOINT from the stalled one.
This is the structural reason the bounded exchange stalls, and it is forced for ANY score
that is maximal exactly at domination. -/
theorem dominating_disjoint_from_clippedTraceStallSubset (selected : Finset (Fin 7))
    (hCard : selected.card = 3) (hDominates : Dominates clippedTraceStallDesign selected) :
    (clippedTraceStallSubset ∩ selected).card = 0 := by
  by_contra hMeetsNonzero
  have hMeets : 1 ≤ (clippedTraceStallSubset ∩ selected).card :=
    Nat.one_le_iff_ne_zero.mpr hMeetsNonzero
  by_cases hDistinct : selected = clippedTraceStallSubset
  · rw [hDistinct] at hDominates
    exact clippedTraceStallSubset_not_dominates hDominates
  · have hFull := clippedTrace_eq_rank_of_dominates clippedTraceStallDesign selected hDominates
    have hUpper := clippedTraceNeighbour_lt selected hCard hMeets hDistinct
    rw [hFull] at hUpper
    norm_num at hUpper

/-! # Witness D — the shadow determinant argmax at size seven -/

/-! ## The refuting design -/

/-- The integer atom vectors of the witness. -/
def shadowArgmaxVector : Fin 7 → Fin 3 → ℤ :=
  ![![1, 1, 0], ![0, 1, -1], ![-1, -1, -2], ![2, 0, 0], ![2, 0, -2], ![1, 0, 1], ![-1, 2, 1]]

/-- The integer weight numerators of the witness; they sum to `60`, which is also
the Parseval scale. -/
def shadowArgmaxNumerator : Fin 7 → ℤ := ![12, 18, 2, 3, 3, 15, 7]

/-- The witness atoms, as real vectors. -/
noncomputable def shadowArgmaxAtom (atomIndex : Fin 7) : Fin 3 → ℝ :=
  fun coord => (shadowArgmaxVector atomIndex coord : ℝ)

/-- The witness weights. -/
noncomputable def shadowArgmaxWeight (atomIndex : Fin 7) : ℝ :=
  (shadowArgmaxNumerator atomIndex : ℝ) / 60

/-- **The refuting design.**  Parseval holds as the integer identity
`Σ_c n_c g_c g_cᵀ = 60 · I₃`, so the residual is exactly zero. -/
noncomputable def shadowArgmaxDesign : WeightedDesign 7 3 where
  atom := shadowArgmaxAtom
  weight := shadowArgmaxWeight
  weight_pos := by
    intro atomIndex
    fin_cases atomIndex <;>
      simp only [shadowArgmaxWeight, shadowArgmaxNumerator] <;> norm_num
  weight_sum_one := by
    rw [Fin.sum_univ_seven]
    simp only [shadowArgmaxWeight, shadowArgmaxNumerator, Matrix.cons_val]
    norm_num
  isParseval := by
    ext rowCoord colCoord
    fin_cases rowCoord <;> fin_cases colCoord <;>
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix,
        Matrix.vecMulVec_apply, Fin.sum_univ_seven, shadowArgmaxWeight, shadowArgmaxAtom,
        shadowArgmaxNumerator, shadowArgmaxVector, Matrix.cons_val, Matrix.one_apply] <;>
      norm_num

@[simp] theorem shadowArgmaxDesign_atom : shadowArgmaxDesign.atom = shadowArgmaxAtom := rfl

@[simp] theorem shadowArgmaxDesign_weight : shadowArgmaxDesign.weight = shadowArgmaxWeight := rfl

/-- The leverage of a witness atom, over the integers. -/
def shadowArgmaxLeverage (atomIndex : Fin 7) : ℤ :=
  shadowArgmaxVector atomIndex 0 ^ 2 + shadowArgmaxVector atomIndex 1 ^ 2 + shadowArgmaxVector atomIndex 2 ^ 2

/-- Every witness leverage is at least `2` — checked over all seven atoms. -/
theorem shadowArgmaxLeverage_ge_two : ∀ atomIndex : Fin 7, 2 ≤ shadowArgmaxLeverage atomIndex := by decide

/-- **The witness is strictly all-heavy**: every leverage is at least `2`, so the
refutation lands inside the campaign's all-heavy frontier. -/
theorem shadowArgmaxDesign_allHeavy : AllHeavy shadowArgmaxDesign := by
  intro atomIndex
  have hleverage : leverageOf (shadowArgmaxDesign.atom atomIndex)
      = (shadowArgmaxLeverage atomIndex : ℝ) := by
    simp only [shadowArgmaxDesign_atom, shadowArgmaxAtom, leverageOf, Fin.sum_univ_three,
      shadowArgmaxLeverage]
    push_cast
    ring
  have hinteger : (2 : ℝ) ≤ (shadowArgmaxLeverage atomIndex : ℝ) := by
    exact_mod_cast shadowArgmaxLeverage_ge_two atomIndex
  rw [hleverage]
  linarith

/-! ### The failing argmax -/

/-- The global argmax of the shadow determinant for the witness. -/
def shadowArgmaxSubset : Finset (Fin 7) := {1, 5, 6}

/-- Its enumeration. -/
def shadowArgmaxPick : Fin 3 → Fin 7 := ![1, 5, 6]

theorem shadowArgmaxSubset_card : shadowArgmaxSubset.card = 3 := by decide

theorem shadowArgmaxPick_injective : Function.Injective shadowArgmaxPick := by decide

theorem shadowArgmaxPick_image : Finset.image shadowArgmaxPick Finset.univ = shadowArgmaxSubset := by decide

/-- The unweighted atom sum of the argmax. -/
theorem subsetSum_shadowArgmaxSubset :
    subsetSum shadowArgmaxDesign shadowArgmaxSubset = !![2, -2, 0; -2, 5, 1; 0, 1, 3] := by
  show (∑ atomIndex ∈ ({1, 5, 6} : Finset (Fin 7)),
      atomMatrix (shadowArgmaxDesign.atom atomIndex)) = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ext rowCoord colCoord
  fin_cases rowCoord <;> fin_cases colCoord <;>
    simp only [Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply, shadowArgmaxDesign_atom,
      shadowArgmaxAtom, shadowArgmaxVector, Matrix.cons_val, Matrix.of_apply] <;>
    norm_num

/-- The domination gap at the argmax, as an explicit integer matrix of
determinant `−1`. -/
theorem gap_shadowArgmaxSubset :
    subsetSum shadowArgmaxDesign shadowArgmaxSubset - 1 = !![1, -2, 0; -2, 4, 1; 0, 1, 2] := by
  rw [subsetSum_shadowArgmaxSubset]
  ext rowCoord colCoord
  fin_cases rowCoord <;> fin_cases colCoord <;>
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply] <;>
    norm_num

/-- **The argmax does not dominate**, certified by the integer direction
`w = (−3, −2, 1)`, at which the gap form takes the value `−1`. -/
theorem shadowArgmaxSubset_not_dominates : ¬ Dominates shadowArgmaxDesign shadowArgmaxSubset := by
  intro hdominates
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2
    (![-3, -2, 1] : Fin 3 → ℝ)
  rw [star_trivial, gap_shadowArgmaxSubset] at hform
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val,
    Matrix.of_apply] at hform
  norm_num at hform

/-! ### The integer shadow value -/

/-- The `3 × 3` determinant of three witness atoms, over the integers, laid out
exactly as `Matrix.det_fin_three`. -/
def shadowArgmaxDet (first second third : Fin 7) : ℤ :=
  shadowArgmaxVector first 0 * shadowArgmaxVector second 1 * shadowArgmaxVector third 2
    - shadowArgmaxVector first 0 * shadowArgmaxVector second 2 * shadowArgmaxVector third 1
    - shadowArgmaxVector first 1 * shadowArgmaxVector second 0 * shadowArgmaxVector third 2
    + shadowArgmaxVector first 1 * shadowArgmaxVector second 2 * shadowArgmaxVector third 0
    + shadowArgmaxVector first 2 * shadowArgmaxVector second 0 * shadowArgmaxVector third 1
    - shadowArgmaxVector first 2 * shadowArgmaxVector second 1 * shadowArgmaxVector third 0

/-- The shadow determinant of a triple, cleared of the common denominator `60³`:
`n_a n_b n_c · det(g_a, g_b, g_c)²`. -/
def shadowArgmaxIntegerShadow (first second third : Fin 7) : ℤ :=
  shadowArgmaxNumerator first * shadowArgmaxNumerator second * shadowArgmaxNumerator third
    * shadowArgmaxDet first second third ^ 2

/-- **The exhaustive maximum.**  Over all `7³` index triples — a fortiori over
all thirty-five `3`-subsets — the integer shadow value never exceeds `30240`. -/
theorem shadowArgmaxIntegerShadow_le : ∀ first second third : Fin 7,
    shadowArgmaxIntegerShadow first second third ≤ 30240 := by decide

/-- The argmax attains the bound. -/
theorem shadowArgmaxIntegerShadow_attained : shadowArgmaxIntegerShadow 1 5 6 = 30240 := by decide

/-- The selected-atom determinant of the witness is the integer determinant. -/
theorem det_selectedAtomRows_shadowArgmaxDesign (pick : Fin 3 → Fin 7) :
    (selectedAtomRows shadowArgmaxDesign pick).det
      = (shadowArgmaxDet (pick 0) (pick 1) (pick 2) : ℝ) := by
  rw [Matrix.det_fin_three]
  simp only [selectedAtomRows, Matrix.of_apply, shadowArgmaxDesign_atom, shadowArgmaxAtom, shadowArgmaxDet]
  push_cast
  ring

/-- **The witness score in closed form**: the shadow determinant of any enumerated
triple is its integer shadow value over `60³ = 216000`. -/
theorem shadowDeterminant_shadowArgmaxDesign (pick : Fin 3 → Fin 7)
    (hinj : Function.Injective pick) :
    shadowDeterminant shadowArgmaxDesign (Finset.image pick Finset.univ)
      = (shadowArgmaxIntegerShadow (pick 0) (pick 1) (pick 2) : ℝ) / 216000 := by
  rw [shadowDeterminant_eq_weightProduct_mul_detSq shadowArgmaxDesign pick hinj rfl,
    Fin.prod_univ_three, det_selectedAtomRows_shadowArgmaxDesign]
  simp only [shadowArgmaxDesign_weight, shadowArgmaxWeight, shadowArgmaxIntegerShadow]
  push_cast
  ring

/-- The argmax scores `7/50`. -/
theorem shadowDeterminant_shadowArgmaxSubset :
    shadowDeterminant shadowArgmaxDesign shadowArgmaxSubset = 7 / 50 := by
  have hindex : shadowArgmaxIntegerShadow (shadowArgmaxPick 0) (shadowArgmaxPick 1) (shadowArgmaxPick 2)
      = 30240 := by decide
  rw [← shadowArgmaxPick_image, shadowDeterminant_shadowArgmaxDesign shadowArgmaxPick shadowArgmaxPick_injective,
    hindex]
  norm_num

/-- **No `3`-subset beats the argmax.**  Every triple's shadow determinant is its
integer shadow value over `216000`, and that value is at most `30240`. -/
theorem shadowDeterminant_le_shadowArgmaxSubset (selected : Finset (Fin 7))
    (hcard : selected.card = 3) :
    shadowDeterminant shadowArgmaxDesign selected
      ≤ shadowDeterminant shadowArgmaxDesign shadowArgmaxSubset := by
  have hvalue := shadowDeterminant_shadowArgmaxDesign (selected.orderEmbOfFin hcard)
    (selected.orderEmbOfFin hcard).injective
  rw [image_orderEmbOfFin hcard] at hvalue
  have hcast : (shadowArgmaxIntegerShadow (selected.orderEmbOfFin hcard 0)
      (selected.orderEmbOfFin hcard 1) (selected.orderEmbOfFin hcard 2) : ℝ)
      ≤ (30240 : ℝ) := by
    exact_mod_cast shadowArgmaxIntegerShadow_le (selected.orderEmbOfFin hcard 0)
      (selected.orderEmbOfFin hcard 1) (selected.orderEmbOfFin hcard 2)
  rw [hvalue, shadowDeterminant_shadowArgmaxSubset]
  linarith

/-! ## The refutation -/

/-- **THE REFUTATION, sharp form.**  The shadow determinant is not an
exchange-improving score even on the all-heavy stratum — the campaign's actual
frontier.  The witness `shadowArgmaxDesign` is strictly all-heavy, its subset
`{1, 5, 6}` fails to dominate, and no `3`-subset scores higher. -/
theorem not_exchangeImprovesHeavy_shadowDeterminant :
    ¬ DoesExchangeImproveHeavy 7 3 (shadowDeterminant (m := 7) (k := 3)) := by
  intro himproves
  obtain ⟨improved, himprovedCard, hstrict⟩ :=
    himproves shadowArgmaxDesign shadowArgmaxDesign_allHeavy shadowArgmaxSubset shadowArgmaxSubset_card
      shadowArgmaxSubset_not_dominates
  exact absurd (shadowDeterminant_le_shadowArgmaxSubset improved himprovedCard) (not_le.mpr hstrict)

/-- **The refutation, unrestricted form.** -/
theorem not_exchangeImproves_shadowDeterminant :
    ¬ DoesExchangeImprove 7 3 (shadowDeterminant (m := 7) (k := 3)) := fun himproves =>
  not_exchangeImprovesHeavy_shadowDeterminant
    (doesExchangeImproveHeavy_of_doesExchangeImprove _ himproves)

/-- **The rank-generic route is closed too.**  `gtzWeightedAll_of_exchangeImproves`
consumes a family of scores indexed by the size; the shadow-determinant family
fails already at size `7`, so it cannot feed that reduction at rank `3`. -/
theorem not_exchangeImproves_shadowDeterminant_family :
    ¬ ∀ size : ℕ, 3 ≤ size →
        DoesExchangeImprove size 3
          (fun (D : WeightedDesign size 3) (selected : Finset (Fin size)) =>
            shadowDeterminant D selected) := by
  intro hfamily
  exact not_exchangeImproves_shadowDeterminant (hfamily 7 (by norm_num))

/-- The witness is not a counterexample to GTZ: `{0, 1, 6}` dominates.  So what fails is
the score's argmax rule, not the conjecture.  (An exhaustive exact-minor scan outside Lean
counts ten dominating triples of the thirty-five; that count is MEASURED, and only this
one witness is proved.) -/
theorem shadowArgmaxDesign_hasDominatingSubset :
    ∃ selected : Finset (Fin 7), selected.card = 3 ∧ Dominates shadowArgmaxDesign selected := by
  refine ⟨{0, 1, 6}, by decide, ?_⟩
  have hsum : subsetSum shadowArgmaxDesign {0, 1, 6} = !![2, -1, -1; -1, 6, 1; -1, 1, 2] := by
    show (∑ atomIndex ∈ ({0, 1, 6} : Finset (Fin 7)),
        atomMatrix (shadowArgmaxDesign.atom atomIndex)) = _
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ext rowCoord colCoord
    fin_cases rowCoord <;> fin_cases colCoord <;>
      simp only [Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply, shadowArgmaxDesign_atom,
        shadowArgmaxAtom, shadowArgmaxVector, Matrix.cons_val, Matrix.of_apply] <;>
      norm_num
  -- the gap is the explicit sum of squares  (1,−1,−1)(1,−1,−1)ᵀ + 4·(0,1,0)(0,1,0)ᵀ
  have hdecomposition : subsetSum shadowArgmaxDesign {0, 1, 6} - 1
      = atomMatrix ![1, -1, -1] + (4 : ℝ) • atomMatrix ![0, 1, 0] := by
    rw [hsum]
    ext rowCoord colCoord
    fin_cases rowCoord <;> fin_cases colCoord <;>
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply, atomMatrix, Matrix.vecMulVec_apply, Matrix.of_apply] <;>
      norm_num
  show (subsetSum shadowArgmaxDesign {0, 1, 6} - 1).PosSemidef
  rw [hdecomposition]
  exact (posSemidef_atomMatrix _).add ((posSemidef_atomMatrix _).smul (by norm_num))


/-! ## The ledger, as theorems

Three statements close the file: what is refuted, what is content-free, and what is left.
Nothing here is new mathematics — each is an assembly of the results above, stated so that
a reader cannot mistake "content-free" for "refuted". -/

/-- **REFUTED: every bounded radius below the rank, for all three candidate scores, at
`(7,3)`.** The least eigenvalue and the clipped trace fall to explicit radius-two stalls;
the shadow determinant falls harder, its global argmax failing outright, so in particular
no radius bound saves it. -/
theorem boundedRadiusExchange_refuted_sevenThree {radius : ℕ} (hradius : radius ≤ 2) :
    ¬ DoesExchangeImproveWithinRadius 7 3 radius (leastEigenvalue (m := 7) (k := 3)) ∧
      ¬ DoesExchangeImproveWithinRadius 7 3 radius clippedTrace ∧
      ¬ DoesExchangeImproveWithinRadius 7 3 radius (shadowDeterminant (m := 7) (k := 3)) :=
  ⟨fun himproves => not_exchangeImprovesWithinRadius_two_leastEigenvalue
      (doesExchangeImproveWithinRadius_mono hradius _ himproves),
   not_exchangeImprovesWithinRadius_clippedTrace_of_le_two hradius,
   fun himproves => not_exchangeImproves_shadowDeterminant
      (doesExchangeImprove_of_withinRadius _ himproves)⟩

/-- **REFUTED on the all-heavy stratum too**, which is the stratum
`Gtz.gtzWeightedAll_of_heavy_bounded` reduces the conjecture to — so the refutation blocks
the route where the route actually runs. -/
theorem boundedRadiusExchangeHeavy_refuted_sevenThree {radius : ℕ} (hradius : radius ≤ 2) :
    ¬ DoesExchangeImproveWithinRadiusHeavy 7 3 radius (leastEigenvalue (m := 7) (k := 3)) ∧
      ¬ DoesExchangeImproveWithinRadiusHeavy 7 3 radius clippedTrace ∧
      ¬ DoesExchangeImproveWithinRadiusHeavy 7 3 radius (shadowDeterminant (m := 7) (k := 3)) := by
  refine ⟨fun himproves => not_exchangeImprovesWithinRadiusHeavy_two_leastEigenvalue ?_,
    not_exchangeImprovesWithinRadiusHeavy_clippedTrace_of_le_two hradius,
    fun himproves => not_exchangeImprovesHeavy_shadowDeterminant
      (doesExchangeImproveHeavy_of_withinRadiusHeavy _ himproves)⟩
  intro design hHeavy selected hCard hFails
  obtain ⟨improved, hImprovedCard, hDistance, hStrict⟩ :=
    himproves design hHeavy selected hCard hFails
  exact ⟨improved, hImprovedCard, le_trans hDistance hradius, hStrict⟩

/-- **CONTENT-FREE, NOT REFUTED: radius three at rank three.** Every `3`-subset lies within
exchange distance `3` of every other, so the radius-three hypothesis IS the unrestricted
one; at a least-eigenvalue score that is `GtzWeighted 7 3` verbatim, which is OPEN. The
honest summary of this file is "no radius survives with content", never "every radius is
refuted". -/
theorem doesExchangeImproveWithinRadius_three_sevenThree_iff_gtzWeighted
    (score : WeightedDesign 7 3 → Finset (Fin 7) → ℝ)
    (hscore : IsLeastEigenvalueScore score) :
    DoesExchangeImproveWithinRadius 7 3 3 score ↔ GtzWeighted 7 3 :=
  Iff.trans (doesExchangeImproveWithinRadius_iff_unbounded_of_rank_le (by omega) score)
    (doesExchangeImprove_iff_gtzWeighted_ofSpec (by omega) score hscore)

/-- **The reduction the refutations block**, kept in the file so the direction of
implication is never in doubt: a bounded-radius improving score at ANY radius would close
weighted GTZ at `(7,3)`. Refuting the hypothesis says nothing about the conjecture, and
every witness above satisfies it. -/
theorem gtzWeighted_sevenThree_of_exchangeImprovesWithinRadius {radius : ℕ}
    (score : WeightedDesign 7 3 → Finset (Fin 7) → ℝ)
    (hBounded : DoesExchangeImproveWithinRadius 7 3 radius score) : GtzWeighted 7 3 :=
  gtzWeighted_of_exchangeImprovesWithinRadius (by omega) score hBounded

end Gtz

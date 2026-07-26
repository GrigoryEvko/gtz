/-
# A2, the critical-point quadric law — as an IMPLICATION FROM STATIONARITY DATA

**The whole point of this file is where the analysis lives.**  Nonsmooth
first-order theory — Clarke subdifferentials, the eigenvalue subdifferential,
Danskin's theorem, partial smoothness, the active manifold — stays OUTSIDE Lean,
as a *stated hypothesis*.  What is inside Lean, and kernel-checked, is the pure
linear algebra that the hypothesis implies.  No derivative, no limit, no
manifold, no subdifferential appears anywhere below.  `IsQuadricStationaryData`
is a bundle of finitely many equations and inequalities; every theorem here is a
consequence of those equations by algebra alone.

## The data

`IsQuadricStationaryData D value multiplier activeSet activeSubset activeWeight
tightDir` packages what a nonsmooth first-order analysis of
`F(D) = max_{|C| = k} lambda_min(S_C)` would produce at an interior critical
point of value `v`:

* an index set `activeSet` for the attaining `k`-subsets, with nonnegative
  Clarke multipliers `activeWeight` summing to one;
* per active index a `k`-subset `activeSubset i` and a UNIT tight vector
  `tightDir i` with `S_{C_i} u_i = v u_i`;
* ATOM STATIONARITY, `sum_{C ∋ c} lambda_C <u_C, g_c> u_C = t_c * Lambda g_c`
  at every atom `c`, with `Lambda` the symmetric Lagrange multiplier of the
  Parseval matrix constraint;
* WEIGHT STATIONARITY, `g_c^T Lambda g_c` the SAME number at every atom (the
  multiplier of the weight-sum constraint).

## PROVED here (unconditional, given that data)

* `quadricLaw_of_isQuadricStationaryData` — **the quadric law**: the shared
  constant is `v` itself, so every atom lies on the single central quadric
  `g_c^T Lambda g_c = v`.  Contract atom stationarity against `g_c`, sum over
  `c`, and read `sum_c t_c = 1` on the right against
  `sum_C lambda_C u_C^T S_C u_C = v` on the left.
* `multiplierMatrix_eq_of_isQuadricStationaryData` — `Lambda` is DETERMINED:
  `Lambda = v * sum_C lambda_C u_C u_C^T`.  Apply atom stationarity after
  resolving an arbitrary probe through Parseval.
* `posSemidef_multiplierMatrix_of_isQuadricStationaryData`,
  `trace_multiplierMatrix_of_isQuadricStationaryData` — hence `Lambda ⪰ 0` and
  `tr Lambda = v`, both corollaries of the determination, not extra input.
* `coverageLaw_of_isQuadricStationaryData` — **the coverage law**,
  `sum_{C ∋ c} lambda_C <u_C, g_c>^2 = t_c * v`, the RESTRICTED sum.  This is the
  obligation `Gtz.Ties.CriticalTieMultiplier` records in its header as prose; here
  it is `contractedStationarity` followed by `quadricLaw`.  Its two immediate
  consequences at `v ≠ 0` are
  `exists_mem_activeSubset_of_isQuadricStationaryData` (the active subsets cover
  every atom) and `size_le_rank_mul_card_activeSet_of_isQuadricStationaryData`
  (`m ≤ k * |A|`).
* `tightOverlap_sum_eq_one_of_isQuadricStationaryData` — **(C1)**
  `sum_C lambda_C <u_C, g_c>^2 = 1` at every atom, the UNRESTRICTED sum (the
  quadric law divided by `v`).
* `exists_rayleighProbe_ge_rank_of_isQuadricStationaryData` — **(C2)**, and in a
  form STRONGER than the source note: EVERY `k`-subset, active or not, carries a
  unit probe whose Rayleigh quotient is at least `k`.  Summing (C1) over the `k`
  atoms of any `C` gives `sum_C' lambda_C' u_C'^T S_C u_C' = k`, a convex
  combination, so one active tight direction attains at least `k`.  Stated as an
  explicit probe rather than as `lambda_max` because the repo has NO `lambdaMax`
  at all: `Gtz.lambdaMinMat` (`Gtz.Quantitative.MarginContinuity`) is the only
  eigenvalue function in the repository, and `Gtz.LinAlg.PsdKit` is deliberately
  spectra-free and sqrt-free.
* `value_eq_rank_of_singleActive` — **(C3)** with ONE active subset the value is
  forced: `v = k`.  `value_eq_rank_of_constant_activeSubset` is the sharp form:
  what matters is a single active SUBSET, not a single active INDEX, so a tight
  eigenvalue of multiplicity above one — packaged as several indices carrying the
  same `k`-subset — is covered too.
* `not_isQuadricStationaryData_of_singleActive_of_rank_lt_size` — **the sharp
  interior exclusion**: at `k < m` there is NO stationarity datum with `v ≠ 0` on a
  single active subset, whatever the value.  Coverage forces `m = k`
  (`size_eq_rank_of_singleActive`), and at `m = k` the only `k`-subset is
  everything.
* `not_isQuadricStationaryData_of_singleActive_of_value_lt_one` — the `v < 1`
  reading of the same fact, with TWO hypotheses (`v ≠ 0`, `v < 1`).
* `isotropicQuadric_iff_leverage_eq_rank` — the isotropic case, honestly:
  `(v/k) I` satisfies the quadric at every atom IFF every leverage equals `k`.

## HOW FAR THE EXCLUSION REACHES — the correction that matters most

The single-active branch is EMPTY whenever `k < m`, by
`not_isQuadricStationaryData_of_singleActive_of_rank_lt_size`.  The campaign's open
sizes are `(6,3)` and `(7,3)`, both with `k < m`.  So the `v < 1` exclusion rules
out nothing there that coverage does not already rule out for a stronger reason,
and it must NOT be advertised as ruling out "the configuration a descent argument
would have to produce".

What a descent argument would have to produce is a LARGE active set.  The
unconditional filters this file supplies — coverage, and `|A| ≥ 3` from (C3) plus
the rank-one and independence arguments — leave a residue whose size is stated
plainly and is not small: at `(6,3)` there are 2101 active-set support patterns up
to relabelling that survive them, and at `(7,3)` there are 7011184
[EXACT combinatorics, outside Lean, not mechanized].  Deciding any one of them
carries the INEQUALITY `v < 1`, which no ideal-emptiness engine can see.  That is
the honest position of the interior route.

## The `v ≠ 0` hypothesis is LOAD-BEARING, and BOTH halves are proved

(C1), (C2), (C3) and the exclusions all carry `value ≠ 0`.

* it cannot be dropped: `degenerateQuadricStationaryDesign_isQuadricStationaryData`
  exhibits a genuine `(3,2)` design — all atoms nonzero, all weights positive,
  exactly rational — carrying stationarity data with `Lambda = 0`, ONE active
  subset, and `v = 0 ≠ 2 = k`.  So (C3) and the exclusion are FALSE without it, and
  `exists_isQuadricStationaryData_singleActive_value_ne_rank` says so as a theorem.
  The degeneracy is the eigenvalue-zero direction of a dependent `k`-subset, which
  `Gtz.not_dominates_of_parallel` already tells us designs may contain.
* it is INHABITED: `splitSevenDesign_isQuadricStationaryData` gives the split
  tetrahedron rank-three data at `v = 1` with TWENTY active subsets and
  `Lambda = I/3`, assembled entirely from `Gtz.Ties.StratumFirstOrder`
  (`rainbowSevenMultiplier` positive and summing to one,
  `rainbowSevenTriple_tightEigenvector`, and `rainbowSevenMultiplier_marginal`,
  which IS atom stationarity).  Without it every substantive theorem here would be
  a statement about a possibly-empty class.
  `exists_isQuadricStationaryData_value_ne_zero` is the packaged form.

## What the bundle does NOT pin, said out loud

`IsQuadricStationaryData` requires `value` to be an eigenvalue of `S_{C_i}` at a
unit vector.  It does NOT require `value = lambda_min(S_{C_i})`, and it does NOT
require `value = F(D)`.  The degenerate witness exercises that slack fully: its
"active" subset `{0,1}` does not dominate at all
(`not_dominates_degenerateQuadricStationaryActiveSubset`) while `{0,2}` dominates
STRICTLY (`posDef_gap_degenerateQuadricStationaryDesign`), so `F(D) = 25/16 > 1`
and the design satisfies `GtzWeighted 3 2` with margin.  For the NON-existence
theorems this weakening is sound — a weaker predicate makes the negation stronger,
and that is the only direction used — but the reading "the data package a
maximiser" is therefore not asserted anywhere.

## THE CIRCULARITY FIREWALL — read before instantiating anything here

Nothing in this file supplies stationarity data at any design, and nothing here
may be read as saying a tie IS a critical point.

Applying A2 at a tie presupposes that the tie is a critical point of `F`, which
presupposes `F ≥ 1` in a neighbourhood — i.e. `GtzWeighted` near it.  The trap is
recorded in the repo already: see the "NOT proved here, and NOT provable this
way" section of `Gtz.Ties.TotalTieCorankOne`, which states that a proof of
totality through criticality of the max would prove `GtzWeighted` at the same
size, and the provenance note of `Gtz.Ties.CriticalTieMultiplier`, which says the
same for the quadric law itself.

The two LEGITIMATE readings are:

* (a) UNCONDITIONAL, and the whole point of `value < 1`: at a HYPOTHETICAL
  interior critical point with `v < 1` the data are contradictory.  Nothing is
  assumed about any actual design — the theorem is a non-existence statement
  about the data bundle.
* (b) INSIDE an induction on `m`, where `GtzWeighted` at smaller sizes is
  already available, the analysis may legitimately produce the data at a tie.

ILLEGITIMATE: any unconditional structural claim about ties obtained by assuming
they are critical points.  Every theorem below takes `IsQuadricStationaryData` as
a HYPOTHESIS in its statement, never as something derived; the conditionality is
therefore in the types, not only in this prose.

## Agreement with the shipped exclusion, disclosed

`Gtz.IsCriticalMultiplierAt` (`Gtz.Ties.CriticalTieMultiplier`) is the same
first-order object in the tie normalisation `tr Lambda = 1`, quadric value `1`,
and gap annihilation at a single subset.
`isCriticalMultiplierAt_of_singleActive_of_value_one` proves the agreement: at
`v = 1` with one active subset the data produce exactly that predicate, so
`Gtz.not_isCriticalMultiplierAt` re-derives the exclusion for `2 ≤ k`.  The (C3)
route is strictly stronger — it needs no `v = 1`, and it returns the exact value
`v = k` rather than a contradiction — so the shipped theorem is subsumed, not
duplicated.

## NOT here, deliberately

* No projection chart.  Everything below is in the raw `(g, t)` coordinates and
  needs no chart, so `Gtz.Quantitative.ProjectionChartLegs` is neither imported
  nor re-derived, and no chart or inertia lemma is duplicated.
* No stratum emptiness certificate.  The external Groebner stage produced its
  `M(K4)` (`q6m8`) and `F7-minus` (`q7m21`) verdicts through `msolve` WITHOUT a
  cofactor certificate; the minimal saturation is the FULL product of atom scales,
  which puts the Nullstellensatz degree at six or more and the Macaulay system
  around `12376 x 5824` over `Q` at cofactor degree three, so there is nothing of a
  size a `ring` call could check.  Those verdicts are therefore
  EXACT-VIA-EXTERNAL-TOOL, not PROVED, and they are absent from this file rather
  than asserted in it.
* No transport of them into tie-freeness.  What the external stage decided is that
  those two strata carry no TOTAL tie (every basis tangent).  A tie is weaker
  (SOME basis PSD-singular, NO basis positive definite), and "every tie is a total
  tie" is proved only at corank one; `Gtz.Ties.TotalTieCorankOne` records that a
  proof through criticality of the maximum would be circular.  Reading the two
  verdicts as `StratumIsTieFree` is therefore CONDITIONAL on an open hypothesis,
  and no statement in this file performs that reading.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.LinAlg.EigenvalueSubdifferential
import Gtz.Design.StressCertificate
import Gtz.Reduction.LiftingLemma
import Gtz.Quantitative.DecisionAtlasSevenThree
import Gtz.Ties.CriticalTieMultiplier
import Gtz.Ties.StratumFirstOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ} {activeIndex : Type*}

/-! ## Two design-free brackets -/

/-- A matrix is determined by its action on vectors.  Used once, to upgrade the
per-probe identity for `Lambda` to a matrix identity. -/
theorem eq_of_forall_mulVec_eq {rank : ℕ}
    {leftMatrix rightMatrix : Matrix (Fin rank) (Fin rank) ℝ}
    (hagree : ∀ probe : Fin rank → ℝ, leftMatrix *ᵥ probe = rightMatrix *ᵥ probe) :
    leftMatrix = rightMatrix := by
  ext rowIndex colIndex
  have hcoord := congrFun (hagree (Pi.single colIndex 1)) rowIndex
  simpa using hcoord

/-- **The polarized subset form**: the bilinear form of `S_C` is the sum of
products of atom pairings.

Disclosure of overlap: the DIAGONAL instance `leftProbe = rightProbe` is already
shipped twice — as `Gtz.subsetSum_form_eq_sum_sq` (`Gtz.Reduction.LiftingLemma`)
and again as `Gtz.dotProduct_subsetSum_mulVec_of_finset`
(`Gtz.Ties.TotalTieCorankOne`), which are the same statement.  Nothing is
re-derived here; the new content is the OFF-diagonal case, which neither covers
and which the multiplier determination below needs. -/
theorem subsetSum_bilinearForm_eq_sum_mul (D : WeightedDesign m k) (C : Finset (Fin m))
    (leftProbe rightProbe : Fin k → ℝ) :
    leftProbe ⬝ᵥ (subsetSum D C *ᵥ rightProbe)
      = ∑ c ∈ C, (D.atom c ⬝ᵥ leftProbe) * (D.atom c ⬝ᵥ rightProbe) := by
  rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
    dotProduct_comm leftProbe (D.atom c), mul_comm]

/-- A vector is determined by its pairings.  The vector-level sibling of
`eq_of_forall_mulVec_eq`, used once, to upgrade the per-probe marginal identity of
the split tetrahedron to a vector identity. -/
theorem eq_of_forall_dotProduct_eq {rank : ℕ} {leftVector rightVector : Fin rank → ℝ}
    (hagree : ∀ probe : Fin rank → ℝ, leftVector ⬝ᵥ probe = rightVector ⬝ᵥ probe) :
    leftVector = rightVector := by
  funext coordIndex
  simpa using hagree (Pi.single coordIndex 1)

/-- **A tight direction reads its eigenvalue off the whole bilinear form**: if
`S_C u = v u` then `u^T S_C w = v <u, w>` for every probe `w`, because `S_C` is
symmetric. -/
theorem tightDirection_bilinearForm_eq_smul (D : WeightedDesign m k) (C : Finset (Fin m))
    {tightVec : Fin k → ℝ} {value : ℝ}
    (heigen : subsetSum D C *ᵥ tightVec = value • tightVec) (probe : Fin k → ℝ) :
    tightVec ⬝ᵥ (subsetSum D C *ᵥ probe) = value * (tightVec ⬝ᵥ probe) := by
  have hadjoint := dotProduct_mulVec_transpose (subsetSum D C) tightVec probe
  rw [transpose_subsetSum_self, heigen, smul_dotProduct, smul_eq_mul] at hadjoint
  exact hadjoint.symm

/-! ## The stationarity data -/

/-- **The first-order stationarity data of `F = max_{|C| = k} lambda_min(S_C)` at an
interior critical point of value `value`** — as a bundle of equations, with the
analysis that would produce it left entirely outside.

`activeSet` indexes the attaining `k`-subsets, `activeWeight` are the Clarke
multipliers, `tightDir i` is a unit eigenvector of `S_{activeSubset i}` at
`value`, and `multiplierMatrix` is the Lagrange multiplier of the Parseval matrix
constraint.  The last two fields are the two stationarity equations: differentiating
in the ATOMS, and differentiating in the WEIGHTS.

This is a HYPOTHESIS, never a theorem.  Instantiating it at a tie requires
knowing `GtzWeighted` near that tie — see the firewall section of the file
header, and the recorded trap in `Gtz.Ties.TotalTieCorankOne`. -/
structure IsQuadricStationaryData (D : WeightedDesign m k) (value : ℝ)
    (multiplierMatrix : Matrix (Fin k) (Fin k) ℝ) (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin m)) (activeWeight : activeIndex → ℝ)
    (tightDir : activeIndex → (Fin k → ℝ)) : Prop where
  /-- The Clarke multipliers are nonnegative. -/
  activeWeight_nonneg : ∀ i ∈ activeSet, 0 ≤ activeWeight i
  /-- The Clarke multipliers sum to one. -/
  activeWeight_sum_one : ∑ i ∈ activeSet, activeWeight i = 1
  /-- Every active subset has exactly `k` atoms. -/
  activeSubset_card : ∀ i ∈ activeSet, (activeSubset i).card = k
  /-- Every tight direction is a unit vector. -/
  tightDir_unit : ∀ i ∈ activeSet, tightDir i ⬝ᵥ tightDir i = 1
  /-- Every tight direction is an eigenvector of its subset sum at `value`. -/
  tightDir_isEigenvector : ∀ i ∈ activeSet,
    subsetSum D (activeSubset i) *ᵥ tightDir i = value • tightDir i
  /-- Stationarity in the atoms:
  `sum_{C ∋ c} lambda_C <u_C, g_c> u_C = t_c * Lambda g_c`. -/
  atomStationarity : ∀ atomLabel : Fin m,
    ∑ i ∈ activeSet,
        (if atomLabel ∈ activeSubset i
          then activeWeight i * (tightDir i ⬝ᵥ D.atom atomLabel) else 0) • tightDir i
      = D.weight atomLabel • (multiplierMatrix *ᵥ D.atom atomLabel)
  /-- Stationarity in the weights: the multiplier's quadratic form is the same
  number at every atom. -/
  weightStationarity : ∀ atomFirst atomSecond : Fin m,
    D.atom atomFirst ⬝ᵥ (multiplierMatrix *ᵥ D.atom atomFirst)
      = D.atom atomSecond ⬝ᵥ (multiplierMatrix *ᵥ D.atom atomSecond)

variable {D : WeightedDesign m k} {value : ℝ}
  {multiplierMatrix : Matrix (Fin k) (Fin k) ℝ} {activeSet : Finset activeIndex}
  {activeSubset : activeIndex → Finset (Fin m)} {activeWeight : activeIndex → ℝ}
  {tightDir : activeIndex → (Fin k → ℝ)}

/-! ## Consequences of the multiplier normalisation alone -/

/-- The multipliers sum to one, so the active set is not empty. -/
theorem activeSet_nonempty_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) :
    activeSet.Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hsum := hdata.activeWeight_sum_one
  rw [hempty, Finset.sum_empty] at hsum
  exact absurd hsum (by norm_num)

/-- Nonnegative multipliers summing to one cannot all vanish. -/
theorem exists_pos_activeWeight_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) :
    ∃ i ∈ activeSet, 0 < activeWeight i := by
  by_contra hnone
  simp only [not_exists, not_and, not_lt] at hnone
  have hzero : ∀ i ∈ activeSet, activeWeight i = 0 := fun i hi =>
    le_antisymm (hnone i hi) (hdata.activeWeight_nonneg i hi)
  have hsum := hdata.activeWeight_sum_one
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at hsum
  exact absurd hsum (by norm_num)

/-- **The value is nonnegative.**  Any active tight direction is a unit vector
whose Rayleigh quotient is `value`, and that quotient is a sum of squares. -/
theorem value_nonneg_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) :
    0 ≤ value := by
  obtain ⟨activeLabel, hmem⟩ := activeSet_nonempty_of_isQuadricStationaryData hdata
  have hrayleigh : ∑ c ∈ activeSubset activeLabel,
      (D.atom c ⬝ᵥ tightDir activeLabel) ^ 2 = value := by
    rw [← subsetSum_form_eq_sum_sq, hdata.tightDir_isEigenvector activeLabel hmem,
      dotProduct_smul, smul_eq_mul, hdata.tightDir_unit activeLabel hmem, mul_one]
  rw [← hrayleigh]
  exact Finset.sum_nonneg fun c _ => sq_nonneg _

/-! ## The quadric law -/

/-- **Atom stationarity contracted against its own atom.**  Pairing the atom
equation with `g_c` turns the tight directions into squared overlaps and the
right side into `t_c` times the multiplier's quadratic form. -/
theorem contractedStationarity_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (atomLabel : Fin m) :
    ∑ i ∈ activeSet,
        (if atomLabel ∈ activeSubset i
          then activeWeight i * (tightDir i ⬝ᵥ D.atom atomLabel) ^ 2 else 0)
      = D.weight atomLabel * (D.atom atomLabel ⬝ᵥ (multiplierMatrix *ᵥ D.atom atomLabel)) := by
  have hpaired := congrArg (fun vec => vec ⬝ᵥ D.atom atomLabel) (hdata.atomStationarity atomLabel)
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul] at hpaired
  rw [dotProduct_comm (multiplierMatrix *ᵥ D.atom atomLabel) (D.atom atomLabel)] at hpaired
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hpaired
  by_cases hmem : atomLabel ∈ activeSubset i
  · simp only [hmem, if_true]
    ring
  · simp only [hmem, if_false, zero_mul]

/-- **THE QUADRIC LAW (A2).**  Every atom of the design lies on the single central
quadric of the multiplier, at level exactly `value`:

    `g_c^T Lambda g_c = value`   for EVERY atom `c`.

Weight stationarity says the left side is atom-independent; the content is that
the shared constant is `value` itself.  Proof: sum the contracted atom identity
over all atoms.  On the right the constant factors out against `sum_c t_c = 1`;
on the left the double sum reorders into
`sum_C lambda_C u_C^T S_C u_C = value * sum_C lambda_C = value`.

No analysis enters — this is the given equations plus Parseval. -/
theorem quadricLaw_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (atomLabel : Fin m) :
    D.atom atomLabel ⬝ᵥ (multiplierMatrix *ᵥ D.atom atomLabel) = value := by
  have hweightSide : ∑ c, D.weight c * (D.atom c ⬝ᵥ (multiplierMatrix *ᵥ D.atom c))
      = D.atom atomLabel ⬝ᵥ (multiplierMatrix *ᵥ D.atom atomLabel) := by
    have hconstant : ∀ c ∈ (Finset.univ : Finset (Fin m)),
        D.weight c * (D.atom c ⬝ᵥ (multiplierMatrix *ᵥ D.atom c))
          = D.weight c * (D.atom atomLabel ⬝ᵥ (multiplierMatrix *ᵥ D.atom atomLabel)) :=
      fun c _ => by rw [hdata.weightStationarity c atomLabel]
    rw [Finset.sum_congr rfl hconstant, ← Finset.sum_mul, D.weight_sum_one, one_mul]
  have hactiveSide : ∑ c : Fin m, ∑ i ∈ activeSet,
      (if c ∈ activeSubset i
        then activeWeight i * (tightDir i ⬝ᵥ D.atom c) ^ 2 else 0) = value := by
    rw [Finset.sum_comm]
    have hperActive : ∀ i ∈ activeSet,
        (∑ c : Fin m, (if c ∈ activeSubset i
          then activeWeight i * (tightDir i ⬝ᵥ D.atom c) ^ 2 else 0))
          = activeWeight i * value := by
      intro i hi
      rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
      congr 1
      have hflip : ∀ c ∈ activeSubset i,
          (tightDir i ⬝ᵥ D.atom c) ^ 2 = (D.atom c ⬝ᵥ tightDir i) ^ 2 :=
        fun c _ => by rw [dotProduct_comm]
      rw [Finset.sum_congr rfl hflip, ← subsetSum_form_eq_sum_sq,
        hdata.tightDir_isEigenvector i hi, dotProduct_smul, smul_eq_mul,
        hdata.tightDir_unit i hi, mul_one]
    rw [Finset.sum_congr rfl hperActive, ← Finset.sum_mul, hdata.activeWeight_sum_one, one_mul]
  calc D.atom atomLabel ⬝ᵥ (multiplierMatrix *ᵥ D.atom atomLabel)
      = ∑ c, D.weight c * (D.atom c ⬝ᵥ (multiplierMatrix *ᵥ D.atom c)) := hweightSide.symm
    _ = ∑ c : Fin m, ∑ i ∈ activeSet,
          (if c ∈ activeSubset i
            then activeWeight i * (tightDir i ⬝ᵥ D.atom c) ^ 2 else 0) :=
        Finset.sum_congr rfl fun c _ =>
          (contractedStationarity_of_isQuadricStationaryData hdata c).symm
    _ = value := hactiveSide

/-- **THE COVERAGE LAW.**  The contracted atom identity read through the quadric
law: the multiplier mass of the active subsets CONTAINING `c`, weighted by the
squared overlaps, is exactly `t_c * value`:

    `sum_{C ∋ c} lambda_C <u_C, g_c>^2 = t_c * value`   for EVERY atom `c`.

This is the obligation `Gtz.Ties.CriticalTieMultiplier` records in its header as
prose rather than as a theorem; here it is two lines, `contractedStationarity`
followed by `quadricLaw`.  Contrast (C1)
`tightOverlap_sum_eq_one_of_isQuadricStationaryData`, whose sum is
UNRESTRICTED and equals `1`; the difference of the two,
`sum_{C ∌ c} lambda_C <u_C, g_c>^2 = 1 - t_c * value`, is a separate fact and is
not used below. -/
theorem coverageLaw_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (atomLabel : Fin m) :
    ∑ i ∈ activeSet,
        (if atomLabel ∈ activeSubset i
          then activeWeight i * (tightDir i ⬝ᵥ D.atom atomLabel) ^ 2 else 0)
      = D.weight atomLabel * value := by
  rw [contractedStationarity_of_isQuadricStationaryData hdata atomLabel,
    quadricLaw_of_isQuadricStationaryData hdata atomLabel]

/-- **The active subsets COVER every atom** once the value is nonzero.  An atom
in no active subset makes the coverage law read `0 = t_c * value` with `t_c > 0`,
forcing `value = 0`.  This is the pigeonhole behind the size bound below, and it
is the reason the single-active branch is so narrow. -/
theorem exists_mem_activeSubset_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (atomLabel : Fin m) :
    ∃ i ∈ activeSet, atomLabel ∈ activeSubset i := by
  by_contra hnone
  simp only [not_exists, not_and] at hnone
  have hvanish : ∑ i ∈ activeSet,
      (if atomLabel ∈ activeSubset i
        then activeWeight i * (tightDir i ⬝ᵥ D.atom atomLabel) ^ 2 else 0) = 0 :=
    Finset.sum_eq_zero fun activeLabel hmem => if_neg (hnone activeLabel hmem)
  rw [coverageLaw_of_isQuadricStationaryData hdata atomLabel] at hvanish
  exact hvalueNe ((mul_eq_zero.mp hvanish).resolve_left (ne_of_gt (D.weight_pos atomLabel)))

/-- **The size is bounded by rank times the number of active indices.**  Coverage
puts every atom in some active subset, and each has `k` atoms, so
`m ≤ k * |activeSet|`.  Consequence stated below: with ONE active index the design
must have `m = k`, so at every size `k < m` — the campaign's `(6,3)` and `(7,3)`
included — the single-active branch is EMPTY and the `value < 1` exclusion has
nothing left to rule out. -/
theorem size_le_rank_mul_card_activeSet_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) :
    m ≤ k * activeSet.card := by
  classical
  have hcovered : (Finset.univ : Finset (Fin m)) ⊆ activeSet.biUnion activeSubset := by
    intro atomLabel _
    obtain ⟨activeLabel, hmem, hin⟩ :=
      exists_mem_activeSubset_of_isQuadricStationaryData hdata hvalueNe atomLabel
    exact Finset.mem_biUnion.mpr ⟨activeLabel, hmem, hin⟩
  have hcardUniv : (Finset.univ : Finset (Fin m)).card ≤ (activeSet.biUnion activeSubset).card :=
    Finset.card_le_card hcovered
  have hcardBound : (activeSet.biUnion activeSubset).card ≤ ∑ i ∈ activeSet, (activeSubset i).card :=
    Finset.card_biUnion_le
  have hcardConst : ∑ i ∈ activeSet, (activeSubset i).card = activeSet.card * k := by
    rw [Finset.sum_congr rfl hdata.activeSubset_card, Finset.sum_const, smul_eq_mul]
  rw [Finset.card_univ, Fintype.card_fin] at hcardUniv
  calc m ≤ (activeSet.biUnion activeSubset).card := hcardUniv
    _ ≤ ∑ i ∈ activeSet, (activeSubset i).card := hcardBound
    _ = activeSet.card * k := hcardConst
    _ = k * activeSet.card := Nat.mul_comm _ _

/-! ## The multiplier is determined -/

/-- **The multiplier is the tight-direction barycentre.**

    `Lambda = value * sum_C lambda_C u_C u_C^T`.

Resolve an arbitrary probe through Parseval, apply atom stationarity to every
atom, reorder, and collapse each active block with
`tightDirection_bilinearForm_eq_smul`.  Everything downstream — positive
semidefiniteness, the trace, (C1) — is a corollary of this identity rather than
separate input. -/
theorem multiplierMatrix_eq_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) :
    multiplierMatrix = value • ∑ i ∈ activeSet, activeWeight i • atomMatrix (tightDir i) := by
  refine eq_of_forall_mulVec_eq fun probe => ?_
  have hparseval : ∑ c, D.weight c • ((D.atom c ⬝ᵥ probe) • D.atom c) = probe := by
    have hcongruence :=
      congrArg (fun frame : Matrix (Fin k) (Fin k) ℝ => frame *ᵥ probe) D.isParseval
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hcongruence
    refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) hcongruence
    rw [atomMatrix, vecMulVec_mulVec_eq]
  calc multiplierMatrix *ᵥ probe
      = multiplierMatrix *ᵥ (∑ c, D.weight c • ((D.atom c ⬝ᵥ probe) • D.atom c)) := by
        rw [hparseval]
    _ = ∑ c, ∑ i ∈ activeSet,
          ((D.atom c ⬝ᵥ probe) * (if c ∈ activeSubset i
            then activeWeight i * (tightDir i ⬝ᵥ D.atom c) else 0)) • tightDir i := by
        rw [Matrix.mulVec_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_comm, ← hdata.atomStationarity c,
          Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
    _ = ∑ i ∈ activeSet, ∑ c : Fin m,
          ((D.atom c ⬝ᵥ probe) * (if c ∈ activeSubset i
            then activeWeight i * (tightDir i ⬝ᵥ D.atom c) else 0)) • tightDir i :=
        Finset.sum_comm
    _ = ∑ i ∈ activeSet, (value * (activeWeight i * (tightDir i ⬝ᵥ probe))) • tightDir i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← Finset.sum_smul]
      congr 1
      have hcollapse : ∀ c ∈ (Finset.univ : Finset (Fin m)),
          (D.atom c ⬝ᵥ probe) * (if c ∈ activeSubset i
            then activeWeight i * (tightDir i ⬝ᵥ D.atom c) else 0)
            = (if c ∈ activeSubset i
              then activeWeight i * ((D.atom c ⬝ᵥ tightDir i) * (D.atom c ⬝ᵥ probe))
              else 0) := by
        intro c _
        by_cases hmem : c ∈ activeSubset i
        · simp only [hmem, if_true]
          rw [dotProduct_comm (tightDir i) (D.atom c)]
          ring
        · simp only [hmem, if_false, mul_zero]
      rw [Finset.sum_congr rfl hcollapse, Finset.sum_ite_mem, Finset.univ_inter,
        ← Finset.mul_sum, ← subsetSum_bilinearForm_eq_sum_mul,
        tightDirection_bilinearForm_eq_smul D (activeSubset i)
          (hdata.tightDir_isEigenvector i hi) probe]
      ring
    _ = (value • ∑ i ∈ activeSet, activeWeight i • atomMatrix (tightDir i)) *ᵥ probe := by
        rw [Matrix.smul_mulVec, Matrix.sum_mulVec, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.smul_mulVec, atomMatrix, vecMulVec_mulVec_eq, smul_smul, smul_smul]
        congr 1
        ring

/-- **The multiplier is positive semidefinite.**  It is `value` (nonnegative, by
`value_nonneg_of_isQuadricStationaryData`) times a nonnegative combination of
rank-one projectors. -/
theorem posSemidef_multiplierMatrix_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) :
    multiplierMatrix.PosSemidef := by
  rw [multiplierMatrix_eq_of_isQuadricStationaryData hdata]
  have hbarycentre : (∑ i ∈ activeSet, activeWeight i • atomMatrix (tightDir i)).PosSemidef :=
    Finset.sum_induction _ Matrix.PosSemidef
      (fun _ _ hleft hright => hleft.add hright) Matrix.PosSemidef.zero
      fun i hi => (posSemidef_atomMatrix (tightDir i)).smul (hdata.activeWeight_nonneg i hi)
  exact hbarycentre.smul (value_nonneg_of_isQuadricStationaryData hdata)

/-- **The multiplier's trace is the value.**  Each tight projector has trace one
because its direction is a unit vector, and the multipliers sum to one. -/
theorem trace_multiplierMatrix_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) :
    Matrix.trace multiplierMatrix = value := by
  rw [multiplierMatrix_eq_of_isQuadricStationaryData hdata, Matrix.trace_smul, Matrix.trace_sum]
  have hperActive : ∀ i ∈ activeSet,
      Matrix.trace (activeWeight i • atomMatrix (tightDir i)) = activeWeight i := by
    intro i hi
    rw [Matrix.trace_smul, trace_atomMatrix, smul_eq_mul]
    simp only [leverageOf]
    rw [← dotProduct_self_eq_sum_sq, hdata.tightDir_unit i hi, mul_one]
  rw [Finset.sum_congr rfl hperActive, hdata.activeWeight_sum_one, smul_eq_mul, mul_one]

/-! ## (C1) and (C2) -/

/-- **(C1)**: at every atom the tight overlaps carry total multiplier mass one,

    `sum_C lambda_C <u_C, g_c>^2 = 1` .

The quadric law read through the determination of `Lambda`, divided by `value`.
This is where `value ≠ 0` first becomes load-bearing: at `value = 0` the
multiplier is the zero matrix and the quadric law is vacuous. -/
theorem tightOverlap_sum_eq_one_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (atomLabel : Fin m) :
    ∑ i ∈ activeSet, activeWeight i * (tightDir i ⬝ᵥ D.atom atomLabel) ^ 2 = 1 := by
  have hquadric := quadricLaw_of_isQuadricStationaryData hdata atomLabel
  rw [multiplierMatrix_eq_of_isQuadricStationaryData hdata] at hquadric
  have hform : D.atom atomLabel ⬝ᵥ
      ((value • ∑ i ∈ activeSet, activeWeight i • atomMatrix (tightDir i))
        *ᵥ D.atom atomLabel)
      = value * ∑ i ∈ activeSet, activeWeight i * (tightDir i ⬝ᵥ D.atom atomLabel) ^ 2 := by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.sum_mulVec, dotProduct_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix, vecMulVec_mulVec_eq,
      dotProduct_smul, smul_eq_mul, dotProduct_comm (D.atom atomLabel) (tightDir i)]
    ring
  rw [hform] at hquadric
  exact mul_left_cancel₀ hvalueNe (by rw [mul_one]; exact hquadric)

/-- **(C2), active form**: summing (C1) over the `k` atoms of ANY `k`-subset `C`
gives `sum_C' lambda_C' u_C'^T S_C u_C' = k`, a convex combination in the
multipliers, so some active tight direction has Rayleigh quotient at least `k`
against `S_C`.

Note the strengthening over the informal statement of the corollary: `C` is an
arbitrary `k`-subset, not necessarily active.  Nothing in (C1) refers to `C`. -/
theorem exists_active_rayleighForm_ge_rank_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (C : Finset (Fin m)) (hcard : C.card = k) :
    ∃ i ∈ activeSet, (k : ℝ) ≤ tightDir i ⬝ᵥ (subsetSum D C *ᵥ tightDir i) := by
  have hmass : ∑ i ∈ activeSet,
      activeWeight i * (tightDir i ⬝ᵥ (subsetSum D C *ᵥ tightDir i)) = (k : ℝ) := by
    have hoverAtoms : ∑ c ∈ C, ∑ i ∈ activeSet,
        activeWeight i * (tightDir i ⬝ᵥ D.atom c) ^ 2 = (k : ℝ) := by
      rw [Finset.sum_congr rfl fun c _ =>
        tightOverlap_sum_eq_one_of_isQuadricStationaryData hdata hvalueNe c,
        Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
    rw [Finset.sum_comm] at hoverAtoms
    rw [← hoverAtoms]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [subsetSum_form_eq_sum_sq]
    exact Finset.sum_congr rfl fun c _ => by rw [dotProduct_comm]
  obtain ⟨positiveLabel, hpositiveMem, hpositive⟩ :=
    exists_pos_activeWeight_of_isQuadricStationaryData hdata
  by_contra hnone
  simp only [not_exists, not_and, not_le] at hnone
  have hstrict : ∑ i ∈ activeSet,
      activeWeight i * (tightDir i ⬝ᵥ (subsetSum D C *ᵥ tightDir i))
        < ∑ i ∈ activeSet, activeWeight i * (k : ℝ) := by
    refine Finset.sum_lt_sum (fun i hi => ?_) ⟨positiveLabel, hpositiveMem, ?_⟩
    · exact mul_le_mul_of_nonneg_left (hnone i hi).le (hdata.activeWeight_nonneg i hi)
    · exact mul_lt_mul_of_pos_left (hnone positiveLabel hpositiveMem) hpositive
  rw [hmass, ← Finset.sum_mul, hdata.activeWeight_sum_one, one_mul] at hstrict
  exact lt_irrefl _ hstrict

/-- **(C2)**: every `k`-subset carries a nonzero probe whose Rayleigh quotient
against `S_C` is at least `k` — the spectra-free reading of
`lambda_max(S_C) ≥ k`.

Stated with an explicit probe for a concrete reason: the repository has NO
largest-eigenvalue function.  `Gtz.lambdaMinMat`
(`Gtz.Quantitative.MarginContinuity`) is its only eigenvalue definition, there is
no `lambdaMax` anywhere, and `Gtz.LinAlg.PsdKit` is deliberately spectra-free and
sqrt-free.  A probe is therefore the statement, not a weakening of one. -/
theorem exists_rayleighProbe_ge_rank_of_isQuadricStationaryData
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (C : Finset (Fin m)) (hcard : C.card = k) :
    ∃ probe : Fin k → ℝ, probe ≠ 0 ∧
      (k : ℝ) * (probe ⬝ᵥ probe) ≤ probe ⬝ᵥ (subsetSum D C *ᵥ probe) := by
  obtain ⟨activeLabel, hmem, hrayleigh⟩ :=
    exists_active_rayleighForm_ge_rank_of_isQuadricStationaryData hdata hvalueNe C hcard
  have hunit := hdata.tightDir_unit activeLabel hmem
  refine ⟨tightDir activeLabel, ?_, ?_⟩
  · intro hzero
    rw [hzero, zero_dotProduct] at hunit
    exact absurd hunit (by norm_num)
  · rw [hunit, mul_one]
    exact hrayleigh

/-! ## (C3) and the interior exclusion -/

/-- **(C3)**: with a SINGLE active subset the value is forced to be the rank.

The single multiplier is one, so (C1) reads `<u, g_c>^2 = 1` at every atom.
Summing that over the `k` atoms of the active subset gives `u^T S_C u = k`; but
`u` is a unit eigenvector at `value`, so the same number is `value`. -/
theorem value_eq_rank_of_singleActive {singleActive : activeIndex}
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hsingle : activeSet = {singleActive}) (hvalueNe : value ≠ 0) :
    value = (k : ℝ) := by
  have hmem : singleActive ∈ activeSet := by
    rw [hsingle]; exact Finset.mem_singleton_self _
  have hweightOne : activeWeight singleActive = 1 := by
    have hsum := hdata.activeWeight_sum_one
    rwa [hsingle, Finset.sum_singleton] at hsum
  have hoverlap : ∀ c : Fin m, (D.atom c ⬝ᵥ tightDir singleActive) ^ 2 = 1 := by
    intro c
    have hone := tightOverlap_sum_eq_one_of_isQuadricStationaryData hdata hvalueNe c
    rw [hsingle, Finset.sum_singleton, hweightOne, one_mul,
      dotProduct_comm (tightDir singleActive) (D.atom c)] at hone
    exact hone
  have hcard := hdata.activeSubset_card singleActive hmem
  have hrayleigh : tightDir singleActive
      ⬝ᵥ (subsetSum D (activeSubset singleActive) *ᵥ tightDir singleActive) = (k : ℝ) := by
    rw [subsetSum_form_eq_sum_sq,
      Finset.sum_congr rfl (fun c _ => hoverlap c :
        ∀ c ∈ activeSubset singleActive, (D.atom c ⬝ᵥ tightDir singleActive) ^ 2 = 1),
      Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
  rw [hdata.tightDir_isEigenvector singleActive hmem, dotProduct_smul, smul_eq_mul,
    hdata.tightDir_unit singleActive hmem, mul_one] at hrayleigh
  exact hrayleigh

/-- **(C3) is really about a single active SUBSET, not a single active index.**
The bundle lets several indices carry the SAME `k`-subset — that is how a tight
eigenvalue of multiplicity above one is packaged, with one index per basis vector
of the tight eigenspace — and in that case (C3) still applies.

Proof: (C1) summed over the `k` atoms of the common subset `C` gives
`sum_i lambda_i (u_i^T S_C u_i) = k`; every `u_i` is a UNIT eigenvector of the same
`S_C` at `value`, so each Rayleigh quotient is `value`, and the multipliers sum to
one.  Strictly generalises `value_eq_rank_of_singleActive`, which is the
one-index case. -/
theorem value_eq_rank_of_constant_activeSubset {commonSubset : Finset (Fin m)}
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0)
    (hconstant : ∀ activeLabel ∈ activeSet, activeSubset activeLabel = commonSubset) :
    value = (k : ℝ) := by
  obtain ⟨someActive, hsomeMem⟩ := activeSet_nonempty_of_isQuadricStationaryData hdata
  have hcard : commonSubset.card = k := by
    rw [← hconstant someActive hsomeMem]; exact hdata.activeSubset_card someActive hsomeMem
  have hmass : ∑ activeLabel ∈ activeSet, activeWeight activeLabel
      * (tightDir activeLabel ⬝ᵥ (subsetSum D commonSubset *ᵥ tightDir activeLabel))
      = (k : ℝ) := by
    have hoverAtoms : ∑ atomLabel ∈ commonSubset, ∑ activeLabel ∈ activeSet,
        activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ D.atom atomLabel) ^ 2 = (k : ℝ) := by
      rw [Finset.sum_congr rfl fun atomLabel _ =>
        tightOverlap_sum_eq_one_of_isQuadricStationaryData hdata hvalueNe atomLabel,
        Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
    rw [Finset.sum_comm] at hoverAtoms
    rw [← hoverAtoms]
    refine Finset.sum_congr rfl fun activeLabel _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [subsetSum_form_eq_sum_sq]
    exact Finset.sum_congr rfl fun atomLabel _ => by rw [dotProduct_comm]
  have hperActive : ∀ activeLabel ∈ activeSet,
      activeWeight activeLabel
          * (tightDir activeLabel ⬝ᵥ (subsetSum D commonSubset *ᵥ tightDir activeLabel))
        = activeWeight activeLabel * value := by
    intro activeLabel hmem
    rw [← hconstant activeLabel hmem, hdata.tightDir_isEigenvector activeLabel hmem,
      dotProduct_smul, smul_eq_mul, hdata.tightDir_unit activeLabel hmem, mul_one]
  rw [Finset.sum_congr rfl hperActive, ← Finset.sum_mul, hdata.activeWeight_sum_one,
    one_mul] at hmass
  exact hmass

/-- **The single-active branch forces `m = k`.**  Coverage
(`size_le_rank_mul_card_activeSet_of_isQuadricStationaryData` at
`|activeSet| = 1`) gives `m ≤ k`, and the active subset lives inside `Fin m` so
`k ≤ m`.

This is the sharp reading of the single-active hypothesis, and it is what makes
the `value < 1` exclusion below vacuous at every size the campaign is open at:
`(6,3)` and `(7,3)` both have `k < m`. -/
theorem size_eq_rank_of_singleActive {singleActive : activeIndex}
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hsingle : activeSet = {singleActive}) (hvalueNe : value ≠ 0) :
    m = k := by
  have hmem : singleActive ∈ activeSet := by
    rw [hsingle]; exact Finset.mem_singleton_self _
  have hsizeLe : m ≤ k := by
    have hbound := size_le_rank_mul_card_activeSet_of_isQuadricStationaryData hdata hvalueNe
    rwa [hsingle, Finset.card_singleton, Nat.mul_one] at hbound
  have hrankLe : k ≤ m := by
    have hcard := hdata.activeSubset_card singleActive hmem
    calc k = (activeSubset singleActive).card := hcard.symm
      _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = m := by rw [Finset.card_univ, Fintype.card_fin]
  exact le_antisymm hsizeLe hrankLe

/-- **THE SHARP INTERIOR EXCLUSION.**  Whenever the rank is strictly below the
size there is NO stationarity datum with a nonzero value on a single active
subset — no matter what the value is.

This subsumes and explains `not_isQuadricStationaryData_of_singleActive_of_value_lt_one`:
at `(6,3)` and `(7,3)` the single-active class is empty for this reason, so the
`value < 1` hypothesis of that theorem does no work there.  What both statements
share is the reading: a hypothetical interior critical point whose maximum is
attained on ONE `k`-subset would have to be a design with `m = k`, where
`GtzWeighted` is trivial. -/
theorem not_isQuadricStationaryData_of_singleActive_of_rank_lt_size (hrankLt : k < m)
    {singleActive : activeIndex} (hsingle : activeSet = {singleActive}) (hvalueNe : value ≠ 0) :
    ¬ IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir :=
  fun hdata => absurd (size_eq_rank_of_singleActive hdata hsingle hvalueNe) hrankLt.ne'

/-- **The interior exclusion, general form.**  No stationarity data exist on a
single active subset with a nonzero value different from the rank. -/
theorem not_isQuadricStationaryData_of_singleActive_of_value_ne_rank
    {singleActive : activeIndex} (hsingle : activeSet = {singleActive}) (hvalueNe : value ≠ 0)
    (hmismatch : value ≠ (k : ℝ)) :
    ¬ IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir :=
  fun hdata => hmismatch (value_eq_rank_of_singleActive hdata hsingle hvalueNe)

/-- **THE BELOW-ONE INTERIOR EXCLUSION.**  There is no stationarity datum whose
value is nonzero, strictly below one, and attained on a single active subset.

Read this in the sound direction, and only in it.  It is a NON-EXISTENCE
statement about the data bundle, so it is unconditional: it assumes nothing about
any actual design, and in particular it does not assert that any design is a
critical point.  See the firewall section of the file header.

TWO hypotheses, not three, and the reach is narrow — both corrections against the
first draft of this file.

* `1 ≤ k` is DERIVABLE and has been removed.  (C3) returns `value = k`, and
  `value ≠ 0` forces `k ≠ 0`; the discarded justification ("at `k = 0` the
  conclusion `value = 0` is consistent with `value < 1`") was wrong, because
  `value = 0` contradicts `value ≠ 0`.
* the ruled-out class is EMPTY whenever `k < m`, by
  `not_isQuadricStationaryData_of_singleActive_of_rank_lt_size`.  So at the
  campaign's open sizes `(6,3)` and `(7,3)` this theorem excludes nothing that the
  sharp exclusion does not already exclude for a stronger reason, and it must not
  be advertised as ruling out "the configuration a descent argument would have to
  produce".  The configurations a descent argument has to produce have LARGE
  active sets — see the residue note in the file header.

`value ≠ 0` genuinely cannot be dropped:
`exists_isQuadricStationaryData_singleActive_value_ne_rank` exhibits a design
where it fails. -/
theorem not_isQuadricStationaryData_of_singleActive_of_value_lt_one
    {singleActive : activeIndex} (hsingle : activeSet = {singleActive}) (hvalueNe : value ≠ 0)
    (hbelowOne : value < 1) :
    ¬ IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir := by
  refine not_isQuadricStationaryData_of_singleActive_of_value_ne_rank hsingle hvalueNe ?_
  intro hequal
  rw [hequal] at hbelowOne hvalueNe
  have hrankNe : k ≠ 0 := fun hzero => hvalueNe (by rw [hzero]; norm_num)
  have hcast : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hrankNe
  exact absurd hbelowOne (not_lt.mpr hcast)

/-! ## The isotropic case -/

/-- **The isotropic candidate, honestly.**  The scalar multiplier `(value/k) I`
satisfies the quadric law at every atom exactly when every leverage equals the
rank.

Both directions are pure design arithmetic — no stationarity data are involved,
which is why this is stated for a bare design.  Note what is NOT claimed: that
`Lambda = (value/k) I` FOLLOWS from equal leverage.  It does not.  The quadric
equations are `m` affine conditions on the six independent entries of a symmetric
`3x3` multiplier, so they underdetermine it: at the tetrahedron the affine
solution family is TWO-DIMENSIONAL, and the isotropic point is one of its
members [EXACT rational arithmetic, outside Lean, not mechanized].  So equal
leverage is equivalent to the isotropic candidate being ONE admissible
multiplier, never to it being the only one. -/
theorem isotropicQuadric_iff_leverage_eq_rank (D : WeightedDesign m k) {isotropicValue : ℝ}
    (hvalueNe : isotropicValue ≠ 0) (hrankNe : k ≠ 0) :
    (∀ c : Fin m, D.atom c
        ⬝ᵥ (((isotropicValue / (k : ℝ)) • (1 : Matrix (Fin k) (Fin k) ℝ)) *ᵥ D.atom c)
          = isotropicValue)
      ↔ ∀ c : Fin m, leverageOf (D.atom c) = (k : ℝ) := by
  have hrankCastNe : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hrankNe
  have hform : ∀ c : Fin m, D.atom c
      ⬝ᵥ (((isotropicValue / (k : ℝ)) • (1 : Matrix (Fin k) (Fin k) ℝ)) *ᵥ D.atom c)
        = (isotropicValue / (k : ℝ)) * leverageOf (D.atom c) := by
    intro c
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
      dotProduct_self_eq_sum_sq]
    simp only [leverageOf]
  constructor
  · intro hquadric c
    have hscaled : (isotropicValue / (k : ℝ)) * leverageOf (D.atom c) = isotropicValue := by
      rw [← hform c]; exact hquadric c
    refine mul_left_cancel₀ hvalueNe ?_
    calc isotropicValue * leverageOf (D.atom c)
        = (isotropicValue / (k : ℝ)) * leverageOf (D.atom c) * (k : ℝ) := by
          field_simp
      _ = isotropicValue * (k : ℝ) := by rw [hscaled]
  · intro hleverage c
    rw [hform c, hleverage c, div_mul_cancel₀ _ hrankCastNe]

/-- **The isotropic multiplier forces equal leverage.**  The stationarity-side
reading of the forward direction: if the determined multiplier happens to be
scalar then every atom has leverage exactly `k`. -/
theorem leverage_eq_rank_of_isotropicMultiplier
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (hrankNe : k ≠ 0)
    (hisotropic : multiplierMatrix = (value / (k : ℝ)) • (1 : Matrix (Fin k) (Fin k) ℝ))
    (atomLabel : Fin m) :
    leverageOf (D.atom atomLabel) = (k : ℝ) := by
  refine (isotropicQuadric_iff_leverage_eq_rank D hvalueNe hrankNe).mp (fun c => ?_) atomLabel
  rw [← hisotropic]
  exact quadricLaw_of_isQuadricStationaryData hdata c

/-! ## Agreement with the shipped single-subset exclusion -/

/-- **The two first-order objects agree.**  At `value = 1` with a single active
subset, the stationarity data produce exactly a
`Gtz.IsCriticalMultiplierAt` — unit trace, gap annihilation at the active
subset, and the quadric at level one — so
`Gtz.not_isCriticalMultiplierAt` re-derives the exclusion for `2 ≤ k`.

This is a disclosure, not a new result: `value_eq_rank_of_singleActive` already
subsumes it, needing no `value = 1` and returning the exact value `value = k`
rather than a contradiction. -/
theorem isCriticalMultiplierAt_of_singleActive_of_value_one {singleActive : activeIndex}
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hsingle : activeSet = {singleActive}) (hvalueOne : value = 1) :
    IsCriticalMultiplierAt D (activeSubset singleActive) multiplierMatrix := by
  have hmem : singleActive ∈ activeSet := by
    rw [hsingle]; exact Finset.mem_singleton_self _
  have hweightOne : activeWeight singleActive = 1 := by
    have hsum := hdata.activeWeight_sum_one
    rwa [hsingle, Finset.sum_singleton] at hsum
  refine ⟨?_, ?_, ?_⟩
  · rw [trace_multiplierMatrix_of_isQuadricStationaryData hdata, hvalueOne]
  · have hnull : (subsetSum D (activeSubset singleActive) - 1) *ᵥ tightDir singleActive = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hdata.tightDir_isEigenvector singleActive hmem,
        hvalueOne, one_smul, sub_self]
    have hsymmetric : (subsetSum D (activeSubset singleActive) - 1)ᵀ
        = subsetSum D (activeSubset singleActive) - 1 := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, transpose_subsetSum_self]
    rw [multiplierMatrix_eq_of_isQuadricStationaryData hdata, hsingle, Finset.sum_singleton,
      hweightOne, one_smul, hvalueOne, one_smul, atomMatrix, Matrix.vecMulVec_mul,
      ← Matrix.mulVec_transpose, hsymmetric, hnull]
    ext rowIndex colIndex
    simp [Matrix.vecMulVec_apply]
  · intro c
    rw [quadricLaw_of_isQuadricStationaryData hdata c, hvalueOne]

/-! ## The `value ≠ 0` hypothesis is load-bearing — a rational witness

The three atoms `(5/4, 0)`, `(5/4, 0)`, `(0, 5/3)` with weights `8/25`, `8/25`,
`9/25` form an exactly rational `(3,2)` design: `2 * (8/25) * (25/16) = 1` on the
first axis, `(9/25) * (25/9) = 1` on the second, and the weights sum to one.  The
two parallel atoms span a line, so the `2`-subset `{0, 1}` has a SINGULAR sum,
and the orthogonal unit direction `e_1` is a tight eigenvector at eigenvalue `0`.
With `Lambda = 0` and that single active subset every stationarity equation holds
trivially — and the value is `0`, not the rank `2`.

Parallel atoms are legal: `Gtz.not_dominates_of_parallel` is about what such a
subset cannot do, not about designs that cannot contain one. -/

/-- The atoms of the degenerate witness: a parallel pair on the first axis and a
single atom on the second. -/
noncomputable def degenerateQuadricStationaryAtom : Fin 3 → Fin 2 → ℝ :=
  ![![5 / 4, 0], ![5 / 4, 0], ![0, 5 / 3]]

/-- The weights of the degenerate witness. -/
noncomputable def degenerateQuadricStationaryWeight : Fin 3 → ℝ :=
  ![8 / 25, 8 / 25, 9 / 25]

/-- **The degenerate witness is a genuine design** — all atoms nonzero, all
weights positive, Parseval exact over the rationals. -/
noncomputable def degenerateQuadricStationaryDesign : WeightedDesign 3 2 where
  atom := degenerateQuadricStationaryAtom
  weight := degenerateQuadricStationaryWeight
  weight_pos := by
    intro atomLabel
    fin_cases atomLabel <;> simp [degenerateQuadricStationaryWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_three]
    simp [degenerateQuadricStationaryWeight]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_three, smul_eq_mul]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [degenerateQuadricStationaryAtom, degenerateQuadricStationaryWeight] <;>
      norm_num

/-- The tight direction of the degenerate witness: the second axis, orthogonal to
the parallel pair. -/
def degenerateQuadricStationaryTightDir : Fin 2 → ℝ := ![0, 1]

/-- **The degenerate stationarity datum**: one active subset, the zero
multiplier, value `0`.  Every equation of `IsQuadricStationaryData` holds, and
the value is not the rank. -/
theorem degenerateQuadricStationaryDesign_isQuadricStationaryData :
    IsQuadricStationaryData degenerateQuadricStationaryDesign 0
      (0 : Matrix (Fin 2) (Fin 2) ℝ) ({0} : Finset (Fin 1))
      (fun _ => ({0, 1} : Finset (Fin 3))) (fun _ => (1 : ℝ))
      (fun _ => degenerateQuadricStationaryTightDir) where
  activeWeight_nonneg := by intro i _; norm_num
  activeWeight_sum_one := by rw [Finset.sum_singleton]
  activeSubset_card := by intro i _; decide
  tightDir_unit := by
    intro i _
    simp [degenerateQuadricStationaryTightDir, dotProduct, Fin.sum_univ_two]
  tightDir_isEigenvector := by
    intro i _
    funext coordIndex
    rw [subsetSum]
    fin_cases coordIndex <;>
      simp [degenerateQuadricStationaryDesign, degenerateQuadricStationaryAtom,
        degenerateQuadricStationaryTightDir, atomMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, Matrix.sum_apply, Matrix.vecMulVec_apply]
  atomStationarity := by
    intro atomLabel
    rw [Finset.sum_singleton, Matrix.zero_mulVec, smul_zero]
    funext coordIndex
    fin_cases atomLabel <;> fin_cases coordIndex <;>
      simp [degenerateQuadricStationaryDesign, degenerateQuadricStationaryAtom,
        degenerateQuadricStationaryTightDir, dotProduct, Fin.sum_univ_two]
  weightStationarity := by
    intro atomFirst atomSecond
    simp [Matrix.zero_mulVec]

/-- **The `value ≠ 0` hypothesis of (C3) and of the interior exclusion cannot be
dropped**: there is a design, a single active subset, and stationarity data whose
value differs from the rank.  So `value_eq_rank_of_singleActive` is FALSE without
it, and `not_isQuadricStationaryData_of_singleActive_of_value_lt_one` is too —
the witness has `value = 0 < 1` with `1 ≤ k = 2`. -/
theorem exists_isQuadricStationaryData_singleActive_value_ne_rank :
    ∃ (D : WeightedDesign 3 2) (value : ℝ) (multiplier : Matrix (Fin 2) (Fin 2) ℝ)
      (activeSubset : Fin 1 → Finset (Fin 3)) (activeWeight : Fin 1 → ℝ)
      (tightDir : Fin 1 → (Fin 2 → ℝ)),
      IsQuadricStationaryData D value multiplier ({0} : Finset (Fin 1)) activeSubset
        activeWeight tightDir ∧ value ≠ (2 : ℝ) ∧ value < 1 :=
  ⟨degenerateQuadricStationaryDesign, 0, 0, fun _ => ({0, 1} : Finset (Fin 3)), fun _ => 1,
    fun _ => degenerateQuadricStationaryTightDir,
    degenerateQuadricStationaryDesign_isQuadricStationaryData, by norm_num, by norm_num⟩

/-- **The degenerate witness's "active" subset is a MINIMISER, not a maximiser** —
the disclosure that keeps the reading of `IsQuadricStationaryData` honest.

The bundle constrains `value` to be an eigenvalue of `S_{C_i}` at a unit vector.
It does NOT require `value = lambda_min(S_{C_i})`, and it does not require
`value = F(D) = max_C lambda_min(S_C)`.  At the degenerate witness this slack is
exercised at full stretch: the datum's subset `{0, 1}` does not even dominate,
while `{0, 2}` dominates STRICTLY, so `F(D) = 25/16 > 1` and the design satisfies
`GtzWeighted 3 2` with margin.

For a NON-existence theorem this weakening is sound — a weaker predicate makes the
negation stronger — and that is the only direction the file uses.  What it costs
is the reading "the data package a maximiser", which is therefore not asserted
anywhere. -/
theorem not_dominates_degenerateQuadricStationaryActiveSubset :
    ¬ Dominates degenerateQuadricStationaryDesign ({0, 1} : Finset (Fin 3)) := by
  intro hdominates
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2
    degenerateQuadricStationaryTightDir
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    subsetSum] at hform
  have hnegative : degenerateQuadricStationaryTightDir ⬝ᵥ
      ((∑ c ∈ ({0, 1} : Finset (Fin 3)), atomMatrix (degenerateQuadricStationaryDesign.atom c))
        *ᵥ degenerateQuadricStationaryTightDir)
      - degenerateQuadricStationaryTightDir ⬝ᵥ degenerateQuadricStationaryTightDir = -1 := by
    rw [show ({0, 1} : Finset (Fin 3)) = {(0 : Fin 3), (1 : Fin 3)} from rfl]
    simp [degenerateQuadricStationaryDesign, degenerateQuadricStationaryAtom,
      degenerateQuadricStationaryTightDir, atomMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.sum_apply, Matrix.vecMulVec_apply]
  rw [hnegative] at hform
  exact absurd hform (by norm_num)

/-- **The degenerate witness dominates STRICTLY on a different subset**, so it
satisfies `GtzWeighted 3 2` with margin `25/16 - 1 = 9/16` in the worse coordinate.
This is the second half of the disclosure above: the witness is a perfectly good
design; only its stationarity DATA are degenerate. -/
theorem posDef_gap_degenerateQuadricStationaryDesign :
    (subsetSum degenerateQuadricStationaryDesign ({0, 2} : Finset (Fin 3)) - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hprobeNe => ?_⟩
  · rw [subsetSum]
    exact ((Matrix.posSemidef_sum ({0, 2} : Finset (Fin 3)) fun atomIndex _ =>
      posSemidef_atomMatrix (degenerateQuadricStationaryDesign.atom atomIndex)).1).sub
        Matrix.isHermitian_one
  · have hclosed : probe ⬝ᵥ
        ((subsetSum degenerateQuadricStationaryDesign ({0, 2} : Finset (Fin 3)) - 1) *ᵥ probe)
        = (9 / 16 : ℝ) * probe 0 ^ 2 + (16 / 9 : ℝ) * probe 1 ^ 2 := by
      rw [subsetSum, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
        show ({0, 2} : Finset (Fin 3)) = {(0 : Fin 3), (2 : Fin 3)} from rfl]
      simp [degenerateQuadricStationaryDesign, degenerateQuadricStationaryAtom, atomMatrix,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sum_apply, Matrix.vecMulVec_apply]
      ring
    rw [star_trivial, hclosed]
    obtain ⟨coordIndex, hcoordNe⟩ := Function.ne_iff.mp hprobeNe
    have hcoordNeZero : probe coordIndex ≠ 0 := by simpa using hcoordNe
    have hcoordSqPos : 0 < probe coordIndex ^ 2 := by
      rcases lt_or_gt_of_ne hcoordNeZero with hnegative | hpositive
      · nlinarith
      · nlinarith
    have hcoordLeSum : probe coordIndex ^ 2 ≤ ∑ index : Fin 2, probe index ^ 2 :=
      Finset.single_le_sum (fun index _ => sq_nonneg (probe index)) (Finset.mem_univ coordIndex)
    rw [Fin.sum_univ_two] at hcoordLeSum
    nlinarith [sq_nonneg (probe 0), sq_nonneg (probe 1)]

/-! ## `value ≠ 0` is INHABITED, not merely consistent — the split tetrahedron

The degenerate witness above shows `value ≠ 0` cannot be dropped.  It does not
show that anything satisfies it, and every substantive theorem in this file —
(C1), (C2), (C3), both exclusions, `leverage_eq_rank_of_isotropicMultiplier` —
carries it.  So without the datum below the file's real content would be
hypothetically empty.

The split tetrahedron `Gtz.splitSevenDesign` supplies it, with nothing new proved
about the design: `Gtz.Ties.StratumFirstOrder` already ships every ingredient.
The twenty rainbow triples are the active set, `Gtz.rainbowSevenMultiplier` the
Clarke multipliers (positive, summing to one), the missed tetrahedron direction —
normalised, since `|v_d|^2 = 3` — the tight direction at eigenvalue `1`
(`Gtz.rainbowSevenTriple_tightEigenvector`), and
`Gtz.rainbowSevenMultiplier_marginal` IS atom stationarity against
`Lambda = I / 3`.

So: rank three, `value = 1`, TWENTY active subsets, multiplier `I/3`.  Note what
this does NOT say — it does not say the split tetrahedron is a critical point of
`F`.  It says the equations of `IsQuadricStationaryData` are satisfiable at a
nonzero value, which is what the hypothesis set of this file needs.  The firewall
stands: producing the data from criticality is the analysis that lives outside.
-/

/-- `1/sqrt 3` squared is `1/3` — the one arithmetic fact the unit normalisation
of the tetrahedron directions needs. -/
theorem inv_sqrt_three_mul_self_eq_third :
    (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = (3 : ℝ)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- The UNIT tight direction of the `i`-th rainbow triple: the missed tetrahedron
direction scaled to norm one.  `Gtz.rainbowSevenTriple_tightEigenvector` gives the
eigenvector unnormalised, and `IsQuadricStationaryData` wants unit vectors. -/
noncomputable def rainbowSevenUnitTightDir (tripleIndex : Fin 20) : Fin 3 → ℝ :=
  (Real.sqrt 3)⁻¹ • tetraAtom (rainbowSevenMissedDirection tripleIndex)

/-- **The marginal identity in VECTOR form.**  `Gtz.rainbowSevenMultiplier_marginal`
states it against an arbitrary probe; atom stationarity needs the vectors
themselves. -/
theorem rainbowSevenMultiplier_marginal_vector (atomIndex : Fin 7) :
    ∑ tripleIndex : Fin 20,
        (if atomIndex ∈ rainbowSevenTriple tripleIndex then rainbowSevenMultiplier tripleIndex
          else 0) • tetraAtom (rainbowSevenMissedDirection tripleIndex)
      = (-(splitSevenDesign.weight atomIndex)) • splitSevenDesign.atom atomIndex := by
  refine eq_of_forall_dotProduct_eq fun probe => ?_
  rw [sum_dotProduct, smul_dotProduct, smul_eq_mul]
  have hperTriple : ∀ tripleIndex : Fin 20,
      ((if atomIndex ∈ rainbowSevenTriple tripleIndex then rainbowSevenMultiplier tripleIndex
        else 0) • tetraAtom (rainbowSevenMissedDirection tripleIndex)) ⬝ᵥ probe
        = (if atomIndex ∈ rainbowSevenTriple tripleIndex then
            rainbowSevenMultiplier tripleIndex
              * (tetraAtom (rainbowSevenMissedDirection tripleIndex) ⬝ᵥ probe)
          else 0) := by
    intro tripleIndex
    rw [smul_dotProduct, smul_eq_mul]
    by_cases hmem : atomIndex ∈ rainbowSevenTriple tripleIndex
    · simp only [hmem, if_true]
    · simp only [hmem, if_false, zero_mul]
  rw [Finset.sum_congr rfl fun tripleIndex _ => hperTriple tripleIndex,
    rainbowSevenMultiplier_marginal atomIndex probe]
  ring

/-- **THE NON-VACUITY WITNESS AT A NONZERO VALUE.**  The split tetrahedron carries
stationarity data with rank three, `value = 1`, twenty active subsets and
`Lambda = I / 3` — so (C1), (C2), (C3) and both exclusions are not hypothetically
empty statements.

Every field is discharged from `Gtz.Ties.StratumFirstOrder`; nothing new is proved
about the design here, and in particular nothing here says the design is a
critical point of `F`. -/
theorem splitSevenDesign_isQuadricStationaryData :
    IsQuadricStationaryData splitSevenDesign 1 ((3 : ℝ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (Finset.univ : Finset (Fin 20)) rainbowSevenTriple rainbowSevenMultiplier
      rainbowSevenUnitTightDir where
  activeWeight_nonneg := fun tripleIndex _ => (rainbowSevenMultiplier_pos tripleIndex).le
  activeWeight_sum_one := rainbowSevenMultiplier_sum_one
  activeSubset_card := fun tripleIndex _ => rainbowSevenTriple_card tripleIndex
  tightDir_unit := by
    intro tripleIndex _
    rw [rainbowSevenUnitTightDir, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      tetraAtom_dot_self, ← mul_assoc, inv_sqrt_three_mul_self_eq_third]
    norm_num
  tightDir_isEigenvector := by
    intro tripleIndex _
    rw [rainbowSevenUnitTightDir, Matrix.mulVec_smul,
      rainbowSevenTriple_tightEigenvector tripleIndex, one_smul]
  atomStationarity := by
    intro atomLabel
    have hperTriple : ∀ tripleIndex : Fin 20,
        (if atomLabel ∈ rainbowSevenTriple tripleIndex then
          rainbowSevenMultiplier tripleIndex
            * (rainbowSevenUnitTightDir tripleIndex ⬝ᵥ splitSevenDesign.atom atomLabel)
        else 0) • rainbowSevenUnitTightDir tripleIndex
          = (-(3 : ℝ)⁻¹) • ((if atomLabel ∈ rainbowSevenTriple tripleIndex then
              rainbowSevenMultiplier tripleIndex else 0)
                • tetraAtom (rainbowSevenMissedDirection tripleIndex)) := by
      intro tripleIndex
      by_cases hmem : atomLabel ∈ rainbowSevenTriple tripleIndex
      · have hpairing : rainbowSevenUnitTightDir tripleIndex
            ⬝ᵥ splitSevenDesign.atom atomLabel = (Real.sqrt 3)⁻¹ * (-1) := by
          rw [rainbowSevenUnitTightDir, smul_dotProduct, smul_eq_mul, splitSevenDesign_atom,
            tetraAtom_dot_of_ne (rainbowSevenTriple_direction_ne_missed hmem).symm]
        simp only [hmem, if_true]
        rw [hpairing, rainbowSevenUnitTightDir, smul_smul, smul_smul]
        congr 1
        calc rainbowSevenMultiplier tripleIndex * ((Real.sqrt 3)⁻¹ * (-1)) * (Real.sqrt 3)⁻¹
            = -(rainbowSevenMultiplier tripleIndex * ((Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹)) := by
              ring
          _ = -(3 : ℝ)⁻¹ * rainbowSevenMultiplier tripleIndex := by
              rw [inv_sqrt_three_mul_self_eq_third]; ring
      · simp only [hmem, if_false, zero_smul, smul_zero]
    rw [Finset.sum_congr rfl fun tripleIndex _ => hperTriple tripleIndex, ← Finset.smul_sum,
      rainbowSevenMultiplier_marginal_vector atomLabel, Matrix.smul_mulVec, Matrix.one_mulVec,
      smul_smul, smul_smul]
    congr 1
    ring
  weightStationarity := by
    intro atomFirst atomSecond
    have hquadric : ∀ atomLabel : Fin 7, splitSevenDesign.atom atomLabel
        ⬝ᵥ (((3 : ℝ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ splitSevenDesign.atom atomLabel)
          = 1 := by
      intro atomLabel
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
        splitSevenDesign_atom, tetraAtom_dot_self]
      norm_num
    rw [hquadric atomFirst, hquadric atomSecond]

/-- **The hypothesis set of this file is inhabited.**  There are stationarity data
with a NONZERO value — so `tightOverlap_sum_eq_one_of_isQuadricStationaryData`,
`exists_rayleighProbe_ge_rank_of_isQuadricStationaryData`,
`value_eq_rank_of_singleActive` and both exclusions are statements about a
non-empty class.

The witness has twenty active subsets, which is also the honest picture of where
the residue lives: by `not_isQuadricStationaryData_of_singleActive_of_rank_lt_size`
the SMALL active sets are the excluded ones, and the large ones are what a descent
argument would actually have to produce. -/
theorem exists_isQuadricStationaryData_value_ne_zero :
    ∃ (D : WeightedDesign 7 3) (value : ℝ) (multiplier : Matrix (Fin 3) (Fin 3) ℝ)
      (activeSubset : Fin 20 → Finset (Fin 7)) (activeWeight : Fin 20 → ℝ)
      (tightDir : Fin 20 → (Fin 3 → ℝ)),
      IsQuadricStationaryData D value multiplier (Finset.univ : Finset (Fin 20)) activeSubset
        activeWeight tightDir ∧ value ≠ 0 :=
  ⟨splitSevenDesign, 1, (3 : ℝ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ), rainbowSevenTriple,
    rainbowSevenMultiplier, rainbowSevenUnitTightDir,
    splitSevenDesign_isQuadricStationaryData, one_ne_zero⟩

end Gtz

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
* `tightOverlap_sum_eq_one_of_isQuadricStationaryData` — **(C1)**
  `sum_C lambda_C <u_C, g_c>^2 = 1` at every atom (the quadric law divided by
  `v`).
* `exists_rayleighProbe_ge_rank_of_isQuadricStationaryData` — **(C2)**, and in a
  form STRONGER than the source note: EVERY `k`-subset, active or not, carries a
  unit probe whose Rayleigh quotient is at least `k`.  Summing (C1) over the `k`
  atoms of any `C` gives `sum_C' lambda_C' u_C'^T S_C u_C' = k`, a convex
  combination, so one active tight direction attains at least `k`.  Stated as an
  explicit probe rather than as `lambda_max`, because the repo's PSD kit
  (`Gtz.LinAlg.PsdKit`) is deliberately spectra-free and sqrt-free.
* `value_eq_rank_of_singleActive` — **(C3)** with ONE active subset the value is
  forced: `v = k`.
* `not_isQuadricStationaryData_of_singleActive_of_value_lt_one` — hence, for
  `1 ≤ k`, **no such stationarity data exists with `v < 1` on a single active
  subset**.  This is the campaign's first kernel-checked interior-exclusion
  statement.  Its hypotheses are exactly three: one active subset, `v ≠ 0`, and
  `v < 1`.
* `isotropicQuadric_iff_leverage_eq_rank` — the isotropic case, honestly:
  `(v/k) I` satisfies the quadric at every atom IFF every leverage equals `k`.

## The `v ≠ 0` hypothesis is LOAD-BEARING, and that is proved

(C1), (C2), (C3) and the exclusion all carry `value ≠ 0`.  That is not
bookkeeping: `degenerateQuadricStationaryDesign_isQuadricStationaryData` exhibits
a genuine `(3,2)` design — all atoms nonzero, all weights positive, exactly
rational — carrying stationarity data with `Lambda = 0`, ONE active subset, and
`v = 0 ≠ 2 = k`.  So (C3) and the exclusion are FALSE without `v ≠ 0`, and
`exists_isQuadricStationaryData_singleActive_value_ne_rank` says so as a theorem.
The degeneracy is the eigenvalue-zero direction of a dependent `k`-subset, which
`Gtz.not_dominates_of_parallel` already tells us designs may contain.

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
  `M(K4)` and `F7-minus` verdicts through `msolve` WITHOUT a cofactor
  certificate; the Macaulay system for the Nullstellensatz identity is roughly
  `12376 x 5824` over `Q` at cofactor degree three, so there is nothing of a size
  a `ring` call could check.  Those verdicts are therefore
  EXACT-VIA-EXTERNAL-TOOL, not PROVED, and they are absent from this file rather
  than asserted in it.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.LinAlg.EigenvalueSubdifferential
import Gtz.Reduction.RayleighCertificate
import Gtz.Ties.CriticalTieMultiplier

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
`lambda_max(S_C) ≥ k`.  Stated with an explicit probe because
`Gtz.LinAlg.PsdKit` has no spectral theorem by design. -/
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

/-- **The interior exclusion, general form.**  No stationarity data exist on a
single active subset with a nonzero value different from the rank. -/
theorem not_isQuadricStationaryData_of_singleActive_of_value_ne_rank
    {singleActive : activeIndex} (hsingle : activeSet = {singleActive}) (hvalueNe : value ≠ 0)
    (hmismatch : value ≠ (k : ℝ)) :
    ¬ IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir :=
  fun hdata => hmismatch (value_eq_rank_of_singleActive hdata hsingle hvalueNe)

/-- **THE FIRST KERNEL-CHECKED INTERIOR EXCLUSION.**  For `1 ≤ k` there is no
stationarity datum whose value is nonzero, strictly below one, and attained on a
single active subset.

Read this in the sound direction, and only in it.  It is a NON-EXISTENCE
statement about the data bundle, so it is unconditional: it assumes nothing about
any actual design, and in particular it does not assert that any design is a
critical point.  What it rules out is a hypothetical interior critical point with
`F < 1` whose maximum is attained once — the configuration a descent argument
would have to produce.  See the firewall section of the file header.

The three hypotheses are all necessary.  `1 ≤ k` because at `k = 0` the
conclusion `value = 0` is consistent with `value < 1`; `value ≠ 0` because
`exists_isQuadricStationaryData_singleActive_value_ne_rank` exhibits a design
where it fails; and `activeSet = {singleActive}` because (C3) is exactly a
single-active statement — nothing below excludes larger active sets. -/
theorem not_isQuadricStationaryData_of_singleActive_of_value_lt_one (hrank : 1 ≤ k)
    {singleActive : activeIndex} (hsingle : activeSet = {singleActive}) (hvalueNe : value ≠ 0)
    (hbelowOne : value < 1) :
    ¬ IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir := by
  refine not_isQuadricStationaryData_of_singleActive_of_value_ne_rank hsingle hvalueNe ?_
  have hcast : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrank
  intro hequal
  rw [hequal] at hbelowOne
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

end Gtz

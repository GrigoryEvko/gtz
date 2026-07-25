/-
# Moment directions: the frame form without a subdifferential

The design-side frame form of `Gtz.Certificates.FrameBridge` was reduced to a
"frame existence" step whose stated wall was the max-min-eigenvalue
subdifferential (Danskin / Overton–Womersley), absent from Mathlib. That wall
was wanted for one purpose only: to compare the domination value at a tie with
its value at NEIGHBOURING designs, i.e. to supply a derivative.

This file supplies that comparison WITHOUT any derivative, subdifferential,
eigenvalue or spectral input, in the manner of `SchurRankOne` (polarization in
place of a matrix square root) and `CapCriterion` (a witness pair in place of
Cauchy interlacing). The replacement is an EXACT finite congruence whose effect
on domination is a ring identity rather than a first-order estimate.

**The moment direction.** A signed reweighting `v` of a design with
`Σ_c v_c = 0` and `Σ_c v_c g_c g_cᵀ = E` costs nothing in total weight and adds
`E` to the frame operator. When `t + v` stays positive and `I + E ≻ 0`, the
congruence `R` of `exists_congruence_to_one` at `I + E` turns
`(R^T g_c, t_c + v_c)` into a genuine design — Parseval conjugates exactly.

**Theorem A**, quantitative form (`exists_shiftedDominator_of_momentDirection`).
If a design admits a moment direction with excess `E` and `I + E ≻ 0`, then —
given `GtzWeighted m k` — some `k`-subset satisfies the SHIFTED Loewner bound
`S_C ⪰ I + E`. This is the spectra-free reading of `Φ(D) ≥ 1 + λ_min(E)`; the
whole proof is `posSemidef_congr_right` applied to
`R^T S_C R − I = R^T (S_C − (I + E)) R`, and nothing is linearised. The strict
corollary (`exists_strictDominator_of_momentDirection`) reads
`S_C − I = (S_C − I − E) + E` as positive semidefinite plus positive definite
when `E ≻ 0`.

Numerically this bound is SHARP and not slack. 216 000 independent optimizer
landings over nine attack structures and eight `(m,k)` cells drove
`λ_min(S_C) − 1 − e` onto the equality manifold; every apparent violation (69 of
them, all at `k = 3`, `m ≥ 7`) re-adjudicated POSITIVE at 60 decimal digits after
re-whitening to an exact design and repairing the direction to strict
feasibility, with minimum margin `+4.9·10⁻¹⁶`. A further 509 semidefinite checks
of the Loewner form at `k = 2, 3, 4` found no violation either.

**Theorem B** (`exists_conicMultiplier_of_noStrictDominator`). Contrapositive
plus finite-dimensional duality: at a design where no `k`-subset dominates
strictly, the identity is not a moment excess, so a linear functional separates
it, and that functional IS the frame form's multiplier —

    `g_cᵀ Λ g_c = tr Λ ≠ 0` at EVERY atom.

In the planar Bloch coordinates this is verbatim the hypothesis
`freeConst + ⟨ξ, S_c⟩ + β ℓ_c = 0` of `Gtz.conic_normalization` with
`freeConst = −tr Λ`, `ξ` the traceless part of `Λ` and `β = tr Λ / 2`; the
normalization `freeConst = −2β` that `conic_normalization` derives holds here
identically, and `tr Λ ≠ 0` is exactly the `β ≠ 0` branch guard that
`Gtz.collinear_stratum_empty` was written to supply. Parseval forces
`tr Λ = Σ_c t_c g_cᵀ Λ g_c`, so the constant on the right is not a free
parameter — the atoms lie on ONE conic through the design's own trace.

**Theorem A′** (`exists_strictDominator_of_boundaryMomentDirection`), the
size-dropping form. Scaling a moment direction until the FIRST weight reaches
zero and deleting that atom leaves a genuine design of size `m` inside a design
of size `m + 1`. So the GTZ input drops by one, and the circularity of Theorem A
(which consumes `GtzWeighted` at the design's own size) is removed. At `(6,3)`
the input becomes `GtzWeighted 5 3`, a landed theorem, so the conclusion there is
UNCONDITIONAL: **no weighted `(6,3)` tie admits a boundary moment direction with
positive-definite excess**, with no appeal to `GtzWeighted 6 3`. Numerically that
constraint is not idle — 111 of 115 random clone-free `(6,3)` designs do admit
one (best reachable `λ_min(E)` about `0.10`), while all five kernel-proven
`(6,3)`/`(4,3)` ties reach exactly `0` to solver tolerance.

**SCOPE, stated bluntly.** Theorem A consumes `GtzWeighted m k` at the SAME `m`.
It is therefore unconditional exactly where that instance is landed: at `k = 2`
for every `m` (`gtz_rank_two`) and at every `m ≤ 5` for every `k`
(`gtzWeighted_of_le_five`). Those instantiations live in the Reduction layer,
which this file may not import; a consumer there discharges `hgtz` in one line.
Pointing Theorem A at `GtzWeighted 6 3` or `GtzWeighted 7 3` would be CIRCULAR
and must not be done — Theorem A′ is the form to use there.

**Where each form has CONTENT.** The identity is a moment excess exactly when the
atom-moment differences span the symmetric matrices, which needs
`m ≥ k(k+1)/2 + 1`: verified at `100%` of random clone-free designs for
`(4,2), (5,2), (7,3), (8,3), (11,4)` and `0%` for `(3,2), (4,3), (5,3), (6,3),
(9,4), (10,4)`. So Theorem B — whose excess is the IDENTITY — is sharp at `k = 2`
and at `(7,3)`, but says little at `(6,3)`. The MATRIX excess of Theorems A and A′
is less restricted — it is positive for GENERIC designs at `(6,3)` too — but it
is not unrestricted, and the exception is exactly where the interest lies:

> **Theorems A and A′ are VACUOUS on every EQUAL-LEVERAGE design.** `tr E`
> equals `Σ_c v_c ℓ_c`, and `Σ_c v_c = 0`, so equal leverages force `tr E = 0`,
> hence `E` traceless, hence never `≻ 0` and never with `λ_min(E) > 0`. That
> includes `splitTetraDesign`, the only kernel-proven `(6,3)` tie family. An
> unequal-leverage `(6,3)` tie does exist — split `sharpDesign`'s atoms `0` and
> `1`, leverages `(4/3, 4/3, 19/3, 19/3, 19/3, 19/3)` — and there the statement
> bites; but that is a CLONE configuration, which residual 10 excludes. Whether
> any clone-free unequal-leverage `(6,3)` tie exists is open, and it is what
> decides whether the `(6,3)` corollary has content for residual 10.

So the matrix form has teeth at the binding size only off the equal-leverage
locus, and the dual object it calls for is a POSITIVE SEMIDEFINITE conic
multiplier — see the residual note below.

**The rank bridge is blocked, so Danskin is dissolved only where Theorem B
applies.** Theorem B is rank-2; the sole route to rank 3 is compression, and it
is closed: at all seven kernel-proven rank-3 ties the minimum over 2-planes of
`Φ₂(shadow)` is bounded away from `1` (`4/3` at the tetrahedron and its split,
`1.12` at `sharpDesign`, by 200 000-plane search), so Theorem B's hypothesis
never holds there — and in every plane tested the shadow is OFF-CONIC with only
traceless multipliers, so its conclusion fails too. `zeroAtom_pushoff`
corroborates. The honest claim is therefore NOT that Danskin is unnecessary
outright, but that it is unnecessary for the object this file produces.

What the file delivers at the open ranks is the exact converse reading. A design
with no strictly dominating `k`-subset that DOES admit a moment direction would
refute `GtzWeighted m k` outright. So "every clone-free tie is on the conic" is
a CONSEQUENCE of GTZ at that size, not an independent conjecture, and hunting
for a clone-free off-conic tie is hunting for a GTZ counterexample — which is
why 10^5-scale optimizer campaigns keep failing to find one.

**WHAT IS STILL OPEN, and it is not a subdifferential.** Two steps separate the
conic here from `Gtz.FrameBridge.FrameForm`. (1) Re-coordinatization: rewriting
`g_cᵀ Λ g_c = tr Λ` as `ℓ(1/2 − ⟨u, ξ⟩) = 1` (the hypothesis of
`Gtz.moment_row_annihilated`) needs the traceless/Bloch decomposition of `Λ`,
then a gauge rotation to `ξ = (ρ, 0)` and the algebraic tan-half-angle
`coord = u₁/(1 + u₀)`; from there `Gtz.tight_half_angle_biquadratic` and
`Gtz.pair_dominates_iff_halfAngle` already close the biquadratic form. That is
dictionary work, roughly twenty to thirty-five declarations, no new mathematics.
(2) At rank three the frame form is asked of a 2-plane VIEW of the design, and a
rank-three tie need NOT have "no strictly dominating pair" in an arbitrary view —
`Gtz.exists_pair_dominates_in_plane` only gives WEAK domination in every view.
Producing a view in which the best pair is exactly tight is the planar-to-3D
transfer, and it is a genuinely open step of a different kind from the
subdifferential this file replaces.

**THE ONE MISSING DUAL.** Theorem B dualizes the IDENTITY excess by plain
finite-dimensional duality, which is why its multiplier carries only `tr Λ ≠ 0`.
Dualizing the MATRIX excess of Theorem A′ — "no reachable excess is positive
definite" — needs separation of a linear subspace of symmetric matrices from the
positive-definite cone, and returns the sharper multiplier `Λ ⪰ 0`, `Λ ≠ 0`,
`g_cᵀ Λ g_c = tr Λ > 0`. That is the object the eigenvalue subdifferential was
supposed to produce, and it is the version with content at `(6,3)`. Mathlib has
neither the convexity nor the openness of the positive-definite cone (`rg -i
subgrad` over the whole tree returns nothing either), so it is a real gap — but a
gap of about a hundred lines of elementary convex geometry restricted to the
symmetric subspace, NOT the Drusvyatskiy–Kempton spectral transfer machinery.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.SchurRankOne
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ### Moment directions -/

/-- **A moment direction** of a weighted design: a signed reweighting
`reweight` that costs nothing in total weight (`Σ_c v_c = 0`) and moves the
frame operator by `excessMatrix` (`Σ_c v_c g_c g_cᵀ = E`).

Geometrically it is the exact tangent datum a first-order optimality argument
would need, but it is used here as a FINITE perturbation, never differentiated. -/
def IsMomentDirection (D : WeightedDesign m k) (reweight : Fin m → ℝ)
    (excessMatrix : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  (∑ c, reweight c = 0) ∧
    (∑ c, reweight c • atomMatrix (D.atom c) = excessMatrix)

/-- Scaling a moment direction scales its excess. -/
theorem IsMomentDirection.smul {D : WeightedDesign m k} {reweight : Fin m → ℝ}
    {excessMatrix : Matrix (Fin k) (Fin k) ℝ}
    (hmoment : IsMomentDirection D reweight excessMatrix) (scale : ℝ) :
    IsMomentDirection D (scale • reweight) (scale • excessMatrix) := by
  obtain ⟨hzeroSum, hexcess⟩ := hmoment
  constructor
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hzeroSum, mul_zero]
  · rw [← hexcess, Finset.smul_sum]
    exact Finset.sum_congr rfl fun c _ => by
      simp only [Pi.smul_apply, smul_eq_mul, smul_smul]

/-- The reweighted frame operator of a moment direction is `I + E`. -/
theorem reweighted_isParseval (D : WeightedDesign m k) {reweight : Fin m → ℝ}
    {excessMatrix : Matrix (Fin k) (Fin k) ℝ}
    (hmoment : IsMomentDirection D reweight excessMatrix) :
    ∑ c, (D.weight c + reweight c) • atomMatrix (D.atom c) = 1 + excessMatrix := by
  have hsplit : ∑ c, (D.weight c + reweight c) • atomMatrix (D.atom c)
      = (∑ c, D.weight c • atomMatrix (D.atom c))
        + ∑ c, reweight c • atomMatrix (D.atom c) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by rw [add_smul]
  rw [hsplit, D.isParseval, hmoment.2]

/-! ### The congruence-rescaled design -/

/-- **The rescaled, reweighted design**. Given a moment direction with excess
`E`, weights that stay positive, and a congruence `R` with
`Rᵀ (I + E) R = I`, the atoms `Rᵀ g_c` with weights `t_c + v_c` form a genuine
weighted design. Parseval conjugates exactly — this is `atomMatrix_conj`, the
same identity every whitening / compression / Naimark step of the campaign
runs on. -/
def congruentReweightedDesign (D : WeightedDesign m k) (reweight : Fin m → ℝ)
    (excessMatrix congruence : Matrix (Fin k) (Fin k) ℝ)
    (hmoment : IsMomentDirection D reweight excessMatrix)
    (hpositive : ∀ c, 0 < D.weight c + reweight c)
    (hcongruence : congruenceᵀ * (1 + excessMatrix) * congruence = 1) :
    WeightedDesign m k where
  atom := fun c => congruenceᵀ *ᵥ D.atom c
  weight := fun c => D.weight c + reweight c
  weight_pos := hpositive
  weight_sum_one := by
    rw [Finset.sum_add_distrib, D.weight_sum_one, hmoment.1, add_zero]
  isParseval := by
    have hconjugate : ∑ c, (D.weight c + reweight c)
          • atomMatrix (congruenceᵀ *ᵥ D.atom c)
        = congruenceᵀ
            * (∑ c, (D.weight c + reweight c) • atomMatrix (D.atom c))
            * congruenceᵀᵀ := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by
        rw [atomMatrix_conj, Matrix.mul_smul, Matrix.smul_mul]
    rw [hconjugate, reweighted_isParseval D hmoment, Matrix.transpose_transpose,
      hcongruence]

/-- The subset sum of the rescaled design is the congruated subset sum. -/
theorem subsetSum_congruentReweightedDesign (D : WeightedDesign m k)
    (reweight : Fin m → ℝ)
    (excessMatrix congruence : Matrix (Fin k) (Fin k) ℝ)
    (hmoment : IsMomentDirection D reweight excessMatrix)
    (hpositive : ∀ c, 0 < D.weight c + reweight c)
    (hcongruence : congruenceᵀ * (1 + excessMatrix) * congruence = 1)
    (C : Finset (Fin m)) :
    subsetSum (congruentReweightedDesign D reweight excessMatrix congruence
        hmoment hpositive hcongruence) C
      = congruenceᵀ * subsetSum D C * congruence := by
  rw [subsetSum, subsetSum, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  show atomMatrix (congruenceᵀ *ᵥ D.atom c) = _
  rw [atomMatrix_conj, Matrix.transpose_transpose]

/-! ### Theorem A: a moment direction forces strict domination -/

/-- Subset sums are symmetric. -/
theorem transpose_subsetSum_self (D : WeightedDesign m k) (C : Finset (Fin m)) :
    (subsetSum D C)ᵀ = subsetSum D C := by
  rw [subsetSum, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ext rowIndex colIndex
  simp only [Matrix.transpose_apply, atomMatrix, Matrix.vecMulVec_apply]
  ring

/-- **Theorem A — a positive-definite moment excess forces STRICT domination.**

If a weighted design admits a moment direction whose excess is positive
definite and whose reweighting keeps every weight positive, then, granted
`GtzWeighted m k`, some `k`-subset dominates strictly: `S_C − I ≻ 0`.

The proof carries no analysis at all. Congruate the design by `R` with
`Rᵀ(I + E)R = I` and reweight by `t + v`; the result is a genuine design, so
`GtzWeighted` hands back a subset `C` with `Rᵀ S_C R ⪰ I = Rᵀ(I + E)R`.
Congruence-invariance of positive semidefiniteness (`posSemidef_congr_right`,
`R` invertible) transports this to `S_C ⪰ I + E`, and `S_C − I = (S_C − I − E) + E`
is then positive semidefinite plus positive definite. -/
theorem exists_shiftedDominator_of_momentDirection
    (hgtz : GtzWeighted m k) (D : WeightedDesign m k) (reweight : Fin m → ℝ)
    (excessMatrix : Matrix (Fin k) (Fin k) ℝ)
    (hmoment : IsMomentDirection D reweight excessMatrix)
    (hpositive : ∀ c, 0 < D.weight c + reweight c)
    (hshifted : ((1 : Matrix (Fin k) (Fin k) ℝ) + excessMatrix).PosDef) :
    ∃ C : Finset (Fin m), C.card = k
      ∧ (subsetSum D C - (1 + excessMatrix)).PosSemidef := by
  obtain ⟨congruence, hdet, hcongruence⟩ := exists_congruence_to_one hshifted
  obtain ⟨C, hcard, hdominates⟩ :=
    hgtz (congruentReweightedDesign D reweight excessMatrix congruence hmoment
      hpositive hcongruence)
  refine ⟨C, hcard, ?_⟩
  -- transport the weak domination of the congruated design back
  have hgapForm : subsetSum (congruentReweightedDesign D reweight excessMatrix
        congruence hmoment hpositive hcongruence) C - 1
      = congruenceᵀ * (subsetSum D C - (1 + excessMatrix)) * congruence := by
    rw [subsetSum_congruentReweightedDesign, Matrix.mul_sub, Matrix.sub_mul,
      hcongruence]
  rw [Dominates, hgapForm] at hdominates
  have hsymmetric : (subsetSum D C - (1 + excessMatrix))ᵀ
      = subsetSum D C - (1 + excessMatrix) := by
    rw [Matrix.transpose_sub, transpose_subsetSum_self,
      PosDef.transpose_eq hshifted]
  exact (posSemidef_congr_right hsymmetric hdet).mpr hdominates

/-- **Theorem A — a positive-definite moment excess forces STRICT domination.**
The corollary of the shifted form at a positive-definite excess: `I + E ≻ 0`
holds automatically and `S_C − I = (S_C − I − E) + E` is positive semidefinite
plus positive definite. -/
theorem exists_strictDominator_of_momentDirection
    (hgtz : GtzWeighted m k) (D : WeightedDesign m k) (reweight : Fin m → ℝ)
    (excessMatrix : Matrix (Fin k) (Fin k) ℝ)
    (hmoment : IsMomentDirection D reweight excessMatrix)
    (hpositive : ∀ c, 0 < D.weight c + reweight c)
    (hexcessPosDef : excessMatrix.PosDef) :
    ∃ C : Finset (Fin m), C.card = k ∧ (subsetSum D C - 1).PosDef := by
  obtain ⟨C, hcard, htransported⟩ :=
    exists_shiftedDominator_of_momentDirection hgtz D reweight excessMatrix hmoment
      hpositive (Matrix.PosDef.add Matrix.PosDef.one hexcessPosDef)
  refine ⟨C, hcard, ?_⟩
  have hrewrite : subsetSum D C - 1
      = (subsetSum D C - (1 + excessMatrix)) + excessMatrix := by
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [hrewrite, add_comm (subsetSum D C - (1 + excessMatrix)) excessMatrix]
  exact Matrix.PosDef.add_posSemidef hexcessPosDef htransported

/-! ### Scaling to the weight boundary: dropping the size by one

Theorem A consumes `GtzWeighted m k` at the design's OWN size, which is circular
at the binding open sizes. Scaling a moment direction until the first weight
reaches zero removes that circularity: the surviving atoms form a design of size
ONE SMALLER, so the input becomes `GtzWeighted m k` for a design of size `m + 1`.
At `(6,3)` that input is `GtzWeighted 5 3`, a landed theorem
(`gtzWeighted_of_le_five`), so the conclusion there is UNCONDITIONAL. -/

/-- **The boundary-deflated design**: reweight to the boundary (weight zero at
`dropIndex`), drop that atom, and congruate by `R` with `Rᵀ(I + E)R = I`. The
result is a genuine design of size one smaller. -/
def deflatedCongruentDesign (D : WeightedDesign (m + 1) k)
    (reweight : Fin (m + 1) → ℝ)
    (excessMatrix congruence : Matrix (Fin k) (Fin k) ℝ) (dropIndex : Fin (m + 1))
    (hmoment : IsMomentDirection D reweight excessMatrix)
    (hzeroAtDrop : D.weight dropIndex + reweight dropIndex = 0)
    (hpositive : ∀ survivor : Fin m, 0 < D.weight (dropIndex.succAbove survivor)
      + reweight (dropIndex.succAbove survivor))
    (hcongruence : congruenceᵀ * (1 + excessMatrix) * congruence = 1) :
    WeightedDesign m k where
  atom := fun survivor => congruenceᵀ *ᵥ D.atom (dropIndex.succAbove survivor)
  weight := fun survivor => D.weight (dropIndex.succAbove survivor)
    + reweight (dropIndex.succAbove survivor)
  weight_pos := hpositive
  weight_sum_one := by
    have hsplit := Fin.sum_univ_succAbove (fun c => D.weight c + reweight c) dropIndex
    rw [Finset.sum_add_distrib, D.weight_sum_one, hmoment.1, add_zero, hzeroAtDrop,
      zero_add] at hsplit
    exact hsplit.symm
  isParseval := by
    have hsplit := Fin.sum_univ_succAbove
      (fun c => (D.weight c + reweight c)
        • atomMatrix (congruenceᵀ *ᵥ D.atom c)) dropIndex
    rw [hzeroAtDrop, zero_smul, zero_add] at hsplit
    have hfull : ∑ c, (D.weight c + reweight c)
          • atomMatrix (congruenceᵀ *ᵥ D.atom c) = 1 := by
      have hconjugate : ∑ c, (D.weight c + reweight c)
            • atomMatrix (congruenceᵀ *ᵥ D.atom c)
          = congruenceᵀ
              * (∑ c, (D.weight c + reweight c) • atomMatrix (D.atom c))
              * congruenceᵀᵀ := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by
          rw [atomMatrix_conj, Matrix.mul_smul, Matrix.smul_mul]
      rw [hconjugate, reweighted_isParseval D hmoment, Matrix.transpose_transpose,
        hcongruence]
    exact hsplit.symm.trans hfull

/-- The subset sum of the boundary-deflated design is the congruated subset sum
over the image of the surviving indices. -/
theorem subsetSum_deflatedCongruentDesign (D : WeightedDesign (m + 1) k)
    (reweight : Fin (m + 1) → ℝ)
    (excessMatrix congruence : Matrix (Fin k) (Fin k) ℝ) (dropIndex : Fin (m + 1))
    (hmoment : IsMomentDirection D reweight excessMatrix)
    (hzeroAtDrop : D.weight dropIndex + reweight dropIndex = 0)
    (hpositive : ∀ survivor : Fin m, 0 < D.weight (dropIndex.succAbove survivor)
      + reweight (dropIndex.succAbove survivor))
    (hcongruence : congruenceᵀ * (1 + excessMatrix) * congruence = 1)
    (C : Finset (Fin m)) :
    subsetSum (deflatedCongruentDesign D reweight excessMatrix congruence dropIndex
        hmoment hzeroAtDrop hpositive hcongruence) C
      = congruenceᵀ * subsetSum D (C.image dropIndex.succAbove) * congruence := by
  rw [subsetSum, subsetSum, Matrix.mul_sum, Matrix.sum_mul,
    Finset.sum_image (fun _ _ _ _ hEq => Fin.succAbove_right_injective hEq)]
  refine Finset.sum_congr rfl fun survivor _ => ?_
  show atomMatrix (congruenceᵀ *ᵥ D.atom (dropIndex.succAbove survivor)) = _
  rw [atomMatrix_conj, Matrix.transpose_transpose]

/-- **Theorem A′ — the size-dropping form, free of the circularity.** A design
of size `m + 1` with a moment direction whose excess is positive definite and
whose reweighting kills exactly the weight at `dropIndex` has a strictly
dominating `k`-subset, granted `GtzWeighted m k` — the input at size `m`, ONE
SMALLER than the design.

At `(6,3)` this is unconditional: `GtzWeighted 5 3` is landed. So no weighted
`(6,3)` TIE admits a moment direction with positive-definite excess, with no
appeal to `GtzWeighted 6 3`.

The surviving-weight positivity is a genuine side condition: when the boundary
scaling zeroes two or more weights at once the reduction drops by more than one
and this statement does not apply (the further-dropped instances are again
`GtzWeighted j k` for smaller `j`). Numerically the simultaneous case is
non-generic — 111 of 115 random clone-free `(6,3)` designs zeroed exactly one
weight. -/
theorem exists_strictDominator_of_boundaryMomentDirection
    (hgtz : GtzWeighted m k) (D : WeightedDesign (m + 1) k)
    (reweight : Fin (m + 1) → ℝ) (excessMatrix : Matrix (Fin k) (Fin k) ℝ)
    (dropIndex : Fin (m + 1))
    (hmoment : IsMomentDirection D reweight excessMatrix)
    (hzeroAtDrop : D.weight dropIndex + reweight dropIndex = 0)
    (hpositive : ∀ survivor : Fin m, 0 < D.weight (dropIndex.succAbove survivor)
      + reweight (dropIndex.succAbove survivor))
    (hexcessPosDef : excessMatrix.PosDef) :
    ∃ C : Finset (Fin (m + 1)), C.card = k ∧ (subsetSum D C - 1).PosDef := by
  have hshifted : ((1 : Matrix (Fin k) (Fin k) ℝ) + excessMatrix).PosDef :=
    Matrix.PosDef.add Matrix.PosDef.one hexcessPosDef
  obtain ⟨congruence, hdet, hcongruence⟩ := exists_congruence_to_one hshifted
  obtain ⟨C, hcard, hdominates⟩ :=
    hgtz (deflatedCongruentDesign D reweight excessMatrix congruence dropIndex
      hmoment hzeroAtDrop hpositive hcongruence)
  refine ⟨C.image dropIndex.succAbove,
    Finset.card_image_of_injective C Fin.succAbove_right_injective |>.trans hcard, ?_⟩
  have hgapForm : subsetSum (deflatedCongruentDesign D reweight excessMatrix
        congruence dropIndex hmoment hzeroAtDrop hpositive hcongruence) C - 1
      = congruenceᵀ
          * (subsetSum D (C.image dropIndex.succAbove) - (1 + excessMatrix))
          * congruence := by
    rw [subsetSum_deflatedCongruentDesign, Matrix.mul_sub, Matrix.sub_mul,
      hcongruence]
  rw [Dominates, hgapForm] at hdominates
  have hsymmetric : (subsetSum D (C.image dropIndex.succAbove)
        - (1 + excessMatrix))ᵀ
      = subsetSum D (C.image dropIndex.succAbove) - (1 + excessMatrix) := by
    rw [Matrix.transpose_sub, transpose_subsetSum_self, PosDef.transpose_eq hshifted]
  have htransported : (subsetSum D (C.image dropIndex.succAbove)
      - (1 + excessMatrix)).PosSemidef :=
    (posSemidef_congr_right hsymmetric hdet).mpr hdominates
  have hrewrite : subsetSum D (C.image dropIndex.succAbove) - 1
      = (subsetSum D (C.image dropIndex.succAbove) - (1 + excessMatrix))
        + excessMatrix := by
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [hrewrite, add_comm (subsetSum D (C.image dropIndex.succAbove)
    - (1 + excessMatrix)) excessMatrix]
  exact Matrix.PosDef.add_posSemidef hexcessPosDef htransported

/-! ### Non-vacuity of the moment-direction hypothesis -/

/-- A two-atom rank-one design with unequal leverages, `g = (2, 1/2)` and
weights `(1/5, 4/5)`. Used only to witness that the hypothesis of Theorem A is
inhabited. -/
noncomputable def unevenLeveragePair : WeightedDesign 2 1 where
  atom := fun c => fun _ => if c = 0 then 2 else 1 / 2
  weight := fun c => if c = 0 then 1 / 5 else 4 / 5
  weight_pos := by
    intro c
    fin_cases c <;> norm_num
  weight_sum_one := by
    rw [Fin.sum_univ_two]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    fin_cases rowIndex
    fin_cases colIndex
    rw [Fin.sum_univ_two]
    simp [atomMatrix, Matrix.vecMulVec_apply]
    norm_num

/-- **Theorem A is not vacuous**: a weighted design with a moment direction
whose excess is positive definite, and whose reweighting keeps every weight
positive, genuinely exists. (Numerically this is the GENERIC situation once
`m > k(k+1)/2`: the atom-moment differences then span the symmetric matrices,
so the identity is a moment excess. This witness pins the smallest case in the
kernel.) -/
theorem exists_design_with_posDefMomentDirection :
    ∃ (D : WeightedDesign 2 1) (reweight : Fin 2 → ℝ)
      (excessMatrix : Matrix (Fin 1) (Fin 1) ℝ),
      IsMomentDirection D reweight excessMatrix
        ∧ (∀ c, 0 < D.weight c + reweight c) ∧ excessMatrix.PosDef := by
  refine ⟨unevenLeveragePair, fun c => if c = 0 then 4 / 15 else -(4 / 15),
    1, ⟨?_, ?_⟩, ?_, Matrix.PosDef.one⟩
  · rw [Fin.sum_univ_two]
    norm_num
  · ext rowIndex colIndex
    fin_cases rowIndex
    fin_cases colIndex
    rw [Fin.sum_univ_two]
    simp [unevenLeveragePair, atomMatrix, Matrix.vecMulVec_apply]
    norm_num
  · intro c
    fin_cases c <;> · simp [unevenLeveragePair]; norm_num

/-! ### The moment map and its range -/

/-- The total-reweight functional `v ↦ Σ_c v_c`. -/
def totalReweight : (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun reweight := ∑ c, reweight c
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' scale reweight := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

/-- The frame-operator move `v ↦ Σ_c v_c g_c g_cᵀ` of a reweighting. -/
def reweightMoment (D : WeightedDesign m k) :
    (Fin m → ℝ) →ₗ[ℝ] Matrix (Fin k) (Fin k) ℝ where
  toFun reweight := ∑ c, reweight c • atomMatrix (D.atom c)
  map_add' _ _ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by rw [Pi.add_apply, add_smul]
  map_smul' scale reweight := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [smul_smul]

/-- **The moment map** of a design: a reweighting is sent to its total weight
change together with the frame-operator move it produces. Its range is the set
of achievable `(total, excess)` pairs, and `IsMomentDirection` says exactly that
`(0, E)` is in it. -/
def designMomentMap (D : WeightedDesign m k) :
    (Fin m → ℝ) →ₗ[ℝ] (ℝ × Matrix (Fin k) (Fin k) ℝ) :=
  totalReweight.prod (reweightMoment D)

/-- Membership of `(0, E)` in the moment range IS a moment direction. -/
theorem momentDirection_iff_mem_designMomentRange (D : WeightedDesign m k)
    (excessMatrix : Matrix (Fin k) (Fin k) ℝ) :
    (∃ reweight : Fin m → ℝ, IsMomentDirection D reweight excessMatrix)
      ↔ ((0 : ℝ), excessMatrix) ∈ LinearMap.range (designMomentMap D) := by
  constructor
  · rintro ⟨reweight, hzeroSum, hexcess⟩
    exact ⟨reweight, by
      show (totalReweight reweight, reweightMoment D reweight) = _
      rw [show totalReweight reweight = ∑ c, reweight c from rfl,
        show reweightMoment D reweight
          = ∑ c, reweight c • atomMatrix (D.atom c) from rfl, hzeroSum, hexcess]⟩
  · rintro ⟨reweight, hmap⟩
    have hfirst : (∑ c, reweight c) = 0 := congrArg Prod.fst hmap
    have hsecond : (∑ c, reweight c • atomMatrix (D.atom c)) = excessMatrix :=
      congrArg Prod.snd hmap
    exact ⟨reweight, hfirst, hsecond⟩

/-! ### Finite-dimensional duality: the conic multiplier -/

/-- Every linear functional on square matrices is the Frobenius pairing against
the matrix of its values on the matrix units. -/
theorem linearFunctional_eq_matrixPairing
    (phi : Matrix (Fin k) (Fin k) ℝ →ₗ[ℝ] ℝ) (X : Matrix (Fin k) (Fin k) ℝ) :
    phi X = ∑ rowIndex, ∑ colIndex,
      X rowIndex colIndex * phi (Matrix.single rowIndex colIndex 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  rw [map_sum]
  refine Finset.sum_congr rfl fun rowIndex _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun colIndex _ => ?_
  have hsingle : Matrix.single rowIndex colIndex (X rowIndex colIndex)
      = (X rowIndex colIndex) • Matrix.single rowIndex colIndex (1 : ℝ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hsingle, map_smul, smul_eq_mul]

/-- The Frobenius pairing with a rank-one atom is the quadratic form. -/
theorem matrixPairing_atomMatrix (multiplier : Matrix (Fin k) (Fin k) ℝ)
    (vector : Fin k → ℝ) :
    ∑ rowIndex, ∑ colIndex,
        atomMatrix vector rowIndex colIndex * multiplier rowIndex colIndex
      = vector ⬝ᵥ (multiplier *ᵥ vector) := by
  simp only [atomMatrix, Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun rowIndex _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun colIndex _ => by ring

/-- The Frobenius pairing with the identity is the trace. -/
theorem matrixPairing_one (multiplier : Matrix (Fin k) (Fin k) ℝ) :
    ∑ rowIndex, ∑ colIndex, (1 : Matrix (Fin k) (Fin k) ℝ) rowIndex colIndex
        * multiplier rowIndex colIndex
      = Matrix.trace multiplier := by
  simp [Matrix.one_apply, Matrix.trace, Matrix.diag]

/-- The quadratic form does not see the transpose. -/
theorem dotProduct_mulVec_transpose_self (matrix : Matrix (Fin k) (Fin k) ℝ)
    (vector : Fin k → ℝ) :
    vector ⬝ᵥ (matrixᵀ *ᵥ vector) = vector ⬝ᵥ (matrix *ᵥ vector) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun rowIndex _ =>
    Finset.sum_congr rfl fun colIndex _ => by ring

/-- **The conic multiplier from moment degeneracy.** If the identity is NOT a
moment excess of the design — no signed cost-free reweighting moves the frame
operator to `I` — then a linear functional separates it, and reading that
functional as a matrix gives a multiplier `Λ` with

    `g_cᵀ Λ g_c = tr Λ ≠ 0`  at every atom.

Parseval is what pins the right-hand constant: pairing the per-atom relation
against the weights turns the free constant into `tr Λ` itself, so the atoms
lie on ONE conic determined by the design. This is the design-side frame form,
produced with no eigenvalue, no subdifferential and no derivative. -/
theorem exists_conicMultiplier_of_identity_notMoment (D : WeightedDesign m k)
    (hnotmem : ((0 : ℝ), (1 : Matrix (Fin k) (Fin k) ℝ))
      ∉ LinearMap.range (designMomentMap D)) :
    ∃ multiplier : Matrix (Fin k) (Fin k) ℝ,
      Matrix.trace multiplier ≠ 0 ∧
      ∀ c, D.atom c ⬝ᵥ (multiplier *ᵥ D.atom c) = Matrix.trace multiplier := by
  obtain ⟨functional, hnonzero, hkill⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem hnotmem inferInstance
  set matrixPart : Matrix (Fin k) (Fin k) ℝ →ₗ[ℝ] ℝ :=
    functional.comp (LinearMap.inr ℝ ℝ (Matrix (Fin k) (Fin k) ℝ)) with hmatrixPart
  have hmatrixPartApply : ∀ X : Matrix (Fin k) (Fin k) ℝ,
      matrixPart X = functional ((0 : ℝ), X) := fun _ => rfl
  set multiplier : Matrix (Fin k) (Fin k) ℝ :=
    Matrix.of fun rowIndex colIndex =>
      matrixPart (Matrix.single rowIndex colIndex 1) with hmultiplier
  have hpairing : ∀ X : Matrix (Fin k) (Fin k) ℝ,
      matrixPart X
        = ∑ rowIndex, ∑ colIndex, X rowIndex colIndex * multiplier rowIndex colIndex :=
    fun X => linearFunctional_eq_matrixPairing matrixPart X
  -- the functional kills the whole moment range
  have hvanish : ∀ reweight : Fin m → ℝ, functional (designMomentMap D reweight) = 0 := by
    intro reweight
    have hmem : functional (designMomentMap D reweight)
        ∈ Submodule.map functional (LinearMap.range (designMomentMap D)) :=
      Submodule.mem_map_of_mem (LinearMap.mem_range_self _ reweight)
    rw [hkill, Submodule.mem_bot] at hmem
    exact hmem
  -- reading it at the indicator of a single atom
  have hatomRow : ∀ c : Fin m,
      functional ((1 : ℝ), atomMatrix (D.atom c)) = 0 := by
    intro c
    set indicator : Fin m → ℝ := fun d => if d = c then (1 : ℝ) else 0
      with hindicator
    have hmapped : designMomentMap D indicator = ((1 : ℝ), atomMatrix (D.atom c)) := by
      show (totalReweight indicator, reweightMoment D indicator) = _
      have hfirst : (∑ d, indicator d) = 1 := by
        rw [hindicator]
        simp
      have hsecond : (∑ d, indicator d • atomMatrix (D.atom d))
          = atomMatrix (D.atom c) := by
        have hsingleTerm := Finset.sum_eq_single_of_mem
          (s := (Finset.univ : Finset (Fin m))) c (Finset.mem_univ c)
          (f := fun d => indicator d • atomMatrix (D.atom d))
          (fun d _ hne => by
            have hzeroEntry : indicator d = 0 := by rw [hindicator]; simp [hne]
            rw [hzeroEntry, zero_smul])
        have honeEntry : indicator c = 1 := by rw [hindicator]; simp
        rw [hsingleTerm, honeEntry, one_smul]
      rw [show totalReweight indicator = ∑ d, indicator d from rfl,
        show reweightMoment D indicator
          = ∑ d, indicator d • atomMatrix (D.atom d) from rfl,
        hfirst, hsecond]
    rw [← hmapped]
    exact hvanish _
  set constantTerm : ℝ := functional ((1 : ℝ), (0 : Matrix (Fin k) (Fin k) ℝ))
    with hconstantTerm
  have hsplit : ∀ X : Matrix (Fin k) (Fin k) ℝ,
      functional ((1 : ℝ), X) = constantTerm + matrixPart X := by
    intro X
    have hdecompose : ((1 : ℝ), X)
        = ((1 : ℝ), (0 : Matrix (Fin k) (Fin k) ℝ)) + ((0 : ℝ), X) := by
      rw [Prod.mk_add_mk, add_zero, zero_add]
    rw [hdecompose, map_add, hmatrixPartApply]
  have hatomValue : ∀ c : Fin m,
      matrixPart (atomMatrix (D.atom c)) = -constantTerm := by
    intro c
    have hzero := hatomRow c
    rw [hsplit] at hzero
    linarith
  -- Parseval turns the free constant into the trace
  have hidentityValue : matrixPart (1 : Matrix (Fin k) (Fin k) ℝ) = -constantTerm := by
    rw [← D.isParseval, map_sum]
    have hterms : ∀ c ∈ (Finset.univ : Finset (Fin m)),
        matrixPart (D.weight c • atomMatrix (D.atom c))
          = D.weight c * (-constantTerm) := by
      intro c _
      rw [map_smul, smul_eq_mul, hatomValue c]
    rw [Finset.sum_congr rfl hterms, ← Finset.sum_mul, D.weight_sum_one, one_mul]
  have htraceValue : Matrix.trace multiplier = -constantTerm := by
    rw [← hidentityValue, hpairing, matrixPairing_one]
  refine ⟨multiplier, ?_, ?_⟩
  · rw [htraceValue]
    intro hzero
    exact hnonzero (by rw [← hmatrixPartApply, hidentityValue, hzero])
  · intro c
    rw [htraceValue, ← matrixPairing_atomMatrix, ← hpairing, hatomValue c]

/-- The symmetric form of the conic multiplier: symmetrizing changes neither
the trace nor any quadratic form, so the conic can always be presented by a
symmetric `Λ`. -/
theorem exists_symmetricConicMultiplier_of_identity_notMoment
    (D : WeightedDesign m k)
    (hnotmem : ((0 : ℝ), (1 : Matrix (Fin k) (Fin k) ℝ))
      ∉ LinearMap.range (designMomentMap D)) :
    ∃ multiplier : Matrix (Fin k) (Fin k) ℝ,
      multiplierᵀ = multiplier ∧ Matrix.trace multiplier ≠ 0 ∧
      ∀ c, D.atom c ⬝ᵥ (multiplier *ᵥ D.atom c) = Matrix.trace multiplier := by
  obtain ⟨raw, htrace, hconic⟩ :=
    exists_conicMultiplier_of_identity_notMoment D hnotmem
  have htraceSymmetrized :
      Matrix.trace ((2 : ℝ)⁻¹ • (raw + rawᵀ)) = Matrix.trace raw := by
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_transpose, smul_eq_mul]
    ring
  refine ⟨(2 : ℝ)⁻¹ • (raw + rawᵀ), ?_, ?_, ?_⟩
  · rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose,
      add_comm]
  · rw [htraceSymmetrized]
    exact htrace
  · intro c
    rw [htraceSymmetrized, Matrix.smul_mulVec, dotProduct_smul, Matrix.add_mulVec,
      dotProduct_add, dotProduct_mulVec_transpose_self, hconic c, smul_eq_mul]
    ring

/-! ### Theorem B: the frame form at a design with no strict dominator -/

/-- **Theorem B — no strictly dominating `k`-subset forces the conic.**

At a design where no `k`-subset dominates strictly — the second conjunct of
`IsTie`, so this hypothesis is WEAKER than being a tie — granted
`GtzWeighted m k`, there is a symmetric `Λ` with

    `g_cᵀ Λ g_c = tr Λ ≠ 0`  at EVERY atom.

Combining Theorem A with finite-dimensional duality: a moment direction with
positive-definite excess would produce a strict dominator, so the identity is
not a moment excess (after scaling the direction down until the reweighted
weights stay positive), and duality converts that into the multiplier.

In planar Bloch coordinates this is exactly the hypothesis of
`Gtz.conic_normalization` — `freeConst + ⟨ξ, S_c⟩ + β ℓ_c = 0` with
`freeConst = −tr Λ`, `β = tr Λ / 2` — whose own conclusion `freeConst = −2β` is
here an identity, and `tr Λ ≠ 0` is the `β ≠ 0` branch guard. -/
theorem exists_conicMultiplier_of_noStrictDominator
    (hgtz : GtzWeighted m k) (D : WeightedDesign m k) (hrank : 0 < k)
    (hnoStrict : ∀ C : Finset (Fin m), C.card = k →
      ¬ (subsetSum D C - 1).PosDef) :
    ∃ multiplier : Matrix (Fin k) (Fin k) ℝ,
      multiplierᵀ = multiplier ∧ Matrix.trace multiplier ≠ 0 ∧
      ∀ c, D.atom c ⬝ᵥ (multiplier *ᵥ D.atom c) = Matrix.trace multiplier := by
  refine exists_symmetricConicMultiplier_of_identity_notMoment D ?_
  intro hmem
  obtain ⟨reweight, hmoment⟩ :=
    (momentDirection_iff_mem_designMomentRange D (1 : Matrix (Fin k) (Fin k) ℝ)).mpr hmem
  -- a design with atoms is nonempty as soon as the rank is
  have hatomCount : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hzero | hpos
    · exfalso
      subst hzero
      have hparseval := D.isParseval
      rw [Finset.univ_eq_empty, Finset.sum_empty] at hparseval
      have hentry := congrFun (congrFun hparseval ⟨0, hrank⟩) ⟨0, hrank⟩
      rw [Matrix.zero_apply, Matrix.one_apply_eq] at hentry
      exact zero_ne_one hentry
    · exact hpos
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hatomCount⟩, Finset.mem_univ _⟩
  set scale : ℝ :=
    Finset.univ.inf' hnonempty (fun c => D.weight c / (1 + |reweight c|)) with hscale
  have hscalePos : 0 < scale := by
    rw [hscale, Finset.lt_inf'_iff]
    exact fun c _ => div_pos (D.weight_pos c) (by positivity)
  have hpositive : ∀ c, 0 < D.weight c + (scale • reweight) c := by
    intro c
    have hbound : scale ≤ D.weight c / (1 + |reweight c|) :=
      Finset.inf'_le _ (Finset.mem_univ c)
    have hdenom : (0 : ℝ) < 1 + |reweight c| := by positivity
    have hkey : scale * (1 + |reweight c|) ≤ D.weight c :=
      (le_div_iff₀ hdenom).mp hbound
    have hlower : scale * (-|reweight c|) ≤ scale * reweight c :=
      mul_le_mul_of_nonneg_left (neg_abs_le (reweight c)) hscalePos.le
    show 0 < D.weight c + scale * reweight c
    nlinarith [hscalePos]
  have hscaledExcess : ((scale • (1 : Matrix (Fin k) (Fin k) ℝ))).PosDef :=
    Matrix.PosDef.smul Matrix.PosDef.one hscalePos
  obtain ⟨C, hcard, hstrict⟩ :=
    exists_strictDominator_of_momentDirection hgtz D (scale • reweight)
      (scale • (1 : Matrix (Fin k) (Fin k) ℝ)) (hmoment.smul scale) hpositive
      hscaledExcess
  exact hnoStrict C hcard hstrict

end Gtz

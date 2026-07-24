/-
# The Rayleigh certificate at a tie (residual 10, first rung)

The design-side frame form (`Gtz.FrameBridge`) reduces `tie ⟹ ≤ 11 atoms` to the
frame existence, whose remaining wall is the max-min-eigenvalue subdifferential
(Danskin/Overton–Womersley, absent from Mathlib) plus the assembly of the stress
multiplier. This file mechanizes the FIRST RUNG of that wall — the elementary
Rayleigh certificate that identifies the active tight eigendirection — using only
the kernel `subsetSum_form_eq_sum_sq` / `sum_sq_ge_of_dominates` and Parseval, no
spectral theory.

The chain:

  * `dominationGap_form` — the domination-gap quadratic form `wᵀ(S_C − I)w` equals
    `Σ_{c∈C}(g_c·w)² − |w|²`;
  * `tightDirection_rayleigh_identity` — at a tight direction (gap zero),
    `Σ_{c∈C}(g_c·w)² = |w|²`: the tight eigendirection's total squared projection
    from the dominating subset equals `|w|²` (the Rayleigh value is exactly 1);
  * `tightDirection_minimizes_gap` — the tight direction GLOBALLY minimizes the gap
    form over all directions (it achieves the floor 0 that domination guarantees).
    This IS the active-min-eigenvector certificate: `w` is a null vector of
    `S_C − I`, the datum the eigenvalue subdifferential is built from;
  * `parseval_weighted_sum_sq` — the full weighted Rayleigh identity from Parseval:
    `Σ_c t_c (g_c·w)² = |w|²` for every `w`;
  * `tightDirection_subset_eq_weighted` — THE stationarity seed: at a tie the
    unweighted active-subset sum equals the full weighted sum,
    `Σ_{c∈C}(g_c·w)² = Σ_c t_c (g_c·w)²`, i.e. `Σ_c (𝟙_C(c) − t_c)(g_c·w)² = 0` — a
    linear relation on the squared projections, the first constraint toward the
    focal-conic condition `⟨Λ, g_c g_cᵀ⟩ = −β`.

What remains WALLED (genuinely open, not landed here): assembling the stress
multiplier `Λ` across the family of active tight subsets/directions and running
Gordan's alternative to turn these per-direction stationarity relations into the
per-atom focal-conic equation. That assembly is the eigenvalue-subdifferential /
Danskin content the frame existence still needs.
-/
import Mathlib
import Gtz.Basic
import Gtz.MarginTransfer
import Gtz.LiftingLemma

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- **The domination-gap quadratic form**: `wᵀ(S_C − I)w = Σ_{c∈C}(g_c·w)² − |w|²`,
the equality behind the domination inequality `sum_sq_ge_of_dominates`. -/
theorem dominationGap_form (D : WeightedDesign m k) (C : Finset (Fin m))
    (w : Fin k → ℝ) :
    w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w)
      = (∑ c ∈ C, (D.atom c ⬝ᵥ w) ^ 2) - w ⬝ᵥ w := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, subsetSum_form_eq_sum_sq]

/-- **The tight-direction Rayleigh identity**: a tight direction `w` of a subset
`C` — one where the domination-gap form vanishes — has total squared projection
`Σ_{c∈C}(g_c·w)² = |w|²`. The tight eigendirection sees exactly unit Rayleigh value
from the selected atoms; this is the certificate that `λ_min(S_C) = 1` is achieved
at `w`. -/
theorem tightDirection_rayleigh_identity (D : WeightedDesign m k)
    (C : Finset (Fin m)) {w : Fin k → ℝ}
    (htight : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0) :
    ∑ c ∈ C, (D.atom c ⬝ᵥ w) ^ 2 = w ⬝ᵥ w := by
  rw [dominationGap_form] at htight
  linarith

/-- **The tight direction globally minimizes the gap form** (the active
min-eigenvector certificate). Given domination (so the gap form is `≥ 0`
everywhere by `sum_sq_ge_of_dominates`) and a tight direction `w` (gap zero), the
gap at `w` is `≤` the gap at any other direction `v`. So `w` is a null vector of
`S_C − I` — a minimizing eigenvector of `S_C` at eigenvalue 1, the datum the
eigenvalue subdifferential is assembled from. -/
theorem tightDirection_minimizes_gap (D : WeightedDesign m k)
    {C : Finset (Fin m)} (hdom : Dominates D C) {w : Fin k → ℝ}
    (htight : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0) (v : Fin k → ℝ) :
    w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) ≤ v ⬝ᵥ ((subsetSum D C - 1) *ᵥ v) := by
  rw [htight, dominationGap_form]
  have hcoercive := sum_sq_ge_of_dominates hdom v
  linarith

/-- **The tight direction is a null vector of the gap matrix**: a PSD matrix
whose quadratic form vanishes at `w` annihilates `w`. So a tight direction of a
dominating subset satisfies `(S_C − I)·w = 0` exactly — the upgrade from "Rayleigh
value 1" to a genuine kernel vector. -/
theorem tightDirection_isNullVector (D : WeightedDesign m k)
    {C : Finset (Fin m)} (hdom : Dominates D C) {w : Fin k → ℝ}
    (htight : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0) :
    (subsetSum D C - 1) *ᵥ w = 0 :=
  (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hdom w).mp htight

/-- **The tight direction is a unit eigenvector**: `S_C·w = w`. The active
min-eigenvector of the dominating subset is pinned exactly (eigenvalue 1) — the
precise datum the eigenprojector multiplier of the eigenvalue subdifferential is
built from. -/
theorem tightDirection_isEigenvector (D : WeightedDesign m k)
    {C : Finset (Fin m)} (hdom : Dominates D C) {w : Fin k → ℝ}
    (htight : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0) :
    subsetSum D C *ᵥ w = w := by
  have hnull := tightDirection_isNullVector D hdom htight
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hnull
  exact hnull

/-- **The full weighted Rayleigh identity from Parseval**: since the weighted atoms
resolve the identity (`Σ_c t_c g_c g_cᵀ = I`), every direction `w` satisfies
`Σ_c t_c (g_c·w)² = |w|²`. The weight-side companion of the unweighted
subset identity. -/
theorem parseval_weighted_sum_sq (D : WeightedDesign m k) (w : Fin k → ℝ) :
    ∑ c, D.weight c * (D.atom c ⬝ᵥ w) ^ 2 = w ⬝ᵥ w := by
  have hkey : w ⬝ᵥ ((∑ c, D.weight c • atomMatrix (D.atom c)) *ᵥ w)
      = ∑ c, D.weight c * (D.atom c ⬝ᵥ w) ^ 2 := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun c _ => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]
  rw [D.isParseval, Matrix.one_mulVec] at hkey
  exact hkey.symm

/-- **The stationarity seed** (residual 10's first design-side constraint). At a
tie, a tight direction `w` of a dominating subset `C` satisfies

    Σ_{c∈C} (g_c·w)²  =  Σ_c t_c (g_c·w)²

(both equal `|w|²`), i.e. `Σ_c (𝟙_C(c) − t_c)(g_c·w)² = 0`: a linear relation on the
squared projections tying the active unweighted subset to the full weighted design.
Ranging this over the family of active tight directions is the first constraint of
the focal-conic condition; the multiplier assembly (Gordan + the eigenvalue
subdifferential) is the standing wall. -/
theorem tightDirection_subset_eq_weighted (D : WeightedDesign m k)
    (C : Finset (Fin m)) {w : Fin k → ℝ}
    (htight : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0) :
    ∑ c ∈ C, (D.atom c ⬝ᵥ w) ^ 2 = ∑ c, D.weight c * (D.atom c ⬝ᵥ w) ^ 2 := by
  rw [tightDirection_rayleigh_identity D C htight, ← parseval_weighted_sum_sq D w]

/-- **The rank-one Frobenius coupling** (the focal-conic building block): the
Frobenius inner product of two rank-one projectors `w·wᵀ` and `g·gᵀ` is the squared
overlap `(w·g)²`. So the eigenprojector multiplier `Λ = w·wᵀ` of a single tight
direction couples with each atom `g_c·g_cᵀ` exactly as `(w·g_c)²` — the term the
focal-conic stationarity `⟨Λ, g_c·g_cᵀ⟩ = −β` is written in. At a rank-one
multiplier the focal conic is thus the statement that the atoms' `w`-projections lie
on a level set of `(w·g_c)²`. -/
theorem atomMatrix_frobenius_eq_sq (w g : Fin k → ℝ) :
    Matrix.trace (atomMatrix w * atomMatrix g) = (w ⬝ᵥ g) ^ 2 := by
  unfold atomMatrix
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul,
    smul_eq_mul]
  ring

/-- **The general trace pairing with a rank-one multiplier**: the Frobenius inner
product of the rank-one projector `Λ = w·wᵀ` with an arbitrary matrix `M` is the
quadratic form `wᵀ M w`. This is the KKT bridge — pairing the eigenprojector
multiplier of a tight direction with any matrix reads off that matrix's quadratic
form at `w`. The Frobenius coupling `atomMatrix_frobenius_eq_sq` is the special
case `M = g·gᵀ` (`wᵀ(g gᵀ)w = (w·g)²`). -/
theorem atomMatrix_trace_pairing (M : Matrix (Fin k) (Fin k) ℝ) (w : Fin k → ℝ) :
    Matrix.trace (atomMatrix w * M) = w ⬝ᵥ (M *ᵥ w) := by
  unfold atomMatrix
  rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm]

/-- **Complementary slackness for the rank-one eigenprojector multiplier**
(residual 10's KKT structure). At a tie, the eigenprojector multiplier
`Λ = w·wᵀ` of a tight direction `w` of a dominating subset `C` pairs to ZERO with
the gap matrix `S_C − I`:

    ⟨Λ, S_C − I⟩ = trace((w wᵀ)(S_C − I)) = wᵀ(S_C − I)w = 0.

Both `Λ ⪰ 0` and `S_C − I ⪰ 0` (domination), so this is genuine complementary
slackness: the rank-one multiplier is Frobenius-orthogonal to the gap matrix, i.e.
supported exactly on the active (tight) constraint. This is the KKT slackness datum
the eigenvalue-subdifferential multiplier assembly is built from; the assembly
across the family of active directions (Gordan) is the standing wall. -/
theorem tightDirection_complementarySlackness (D : WeightedDesign m k)
    (C : Finset (Fin m)) {w : Fin k → ℝ}
    (htight : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0) :
    Matrix.trace (atomMatrix w * (subsetSum D C - 1)) = 0 := by
  rw [atomMatrix_trace_pairing]
  exact htight

/-- **The gap operator annihilates the rank-one multiplier** (residual 10's KKT
stationarity, operator form). At a tie, the gap matrix `S_C − I` times the
eigenprojector multiplier `Λ = w·wᵀ` of a tight direction is the zero matrix:

    (S_C − I) · Λ = 0.

This is sharper than the scalar complementary slackness `⟨Λ, S_C − I⟩ = 0`: the
FULL operator product vanishes, so `Λ`'s column space lies in the kernel of the gap
matrix (the active min-eigenspace at eigenvalue 1). It follows directly from
`(S_C − I)·w = 0` through `Matrix.mul_vecMulVec` (`M · vecMulVec w w =
vecMulVec (M·w) w`), needing no symmetry. This is the exact stationarity operator
identity the eigenvalue-subdifferential multiplier assembly consumes. -/
theorem tightDirection_gapAnnihilatesMultiplier (D : WeightedDesign m k)
    {C : Finset (Fin m)} (hdom : Dominates D C) {w : Fin k → ℝ}
    (htight : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0) :
    (subsetSum D C - 1) * atomMatrix w = 0 := by
  have hnull : (subsetSum D C - 1) *ᵥ w = 0 := tightDirection_isNullVector D hdom htight
  unfold atomMatrix
  rw [Matrix.mul_vecMulVec, hnull]
  ext i j
  simp [Matrix.vecMulVec_apply]

/-- **The gap operator annihilates the whole multiplier candidate family**
(residual 10: the wall isolated). Given a dominating subset `C` and a finite family
of tight directions `wᵢ` (each a null direction of `S_C − I`), ANY linear combination
of their rank-one eigenprojectors

    Λ = ∑ᵢ coeffᵢ · (wᵢ · wᵢᵀ)

is annihilated by the gap matrix: `(S_C − I) · Λ = 0`. The stress multiplier the
eigenvalue-subdifferential produces is exactly such a combination with `coeffᵢ ≥ 0`
(a PSD element of the active eigenspace's cone), so operator complementary slackness
`(S_C − I)·Λ = 0` holds AUTOMATICALLY for every candidate — by linearity from the
per-direction `tightDirection_gapAnnihilatesMultiplier`, no spectral theory. This
pins down precisely what stays walled: NOT the annihilation (free, here) but the
EXISTENCE of coefficients making `⟨Λ, g_c·g_cᵀ⟩` match the focal-conic values across
the active atoms — Gordan's alternative over the eigenvalue subdifferential. -/
theorem gapAnnihilates_multiplierCandidate (D : WeightedDesign m k)
    {C : Finset (Fin m)} (hdom : Dominates D C)
    {index : Type*} (family : Finset index) (tightDir : index → Fin k → ℝ)
    (coeff : index → ℝ)
    (htight : ∀ i ∈ family,
      tightDir i ⬝ᵥ ((subsetSum D C - 1) *ᵥ tightDir i) = 0) :
    (subsetSum D C - 1) * (∑ i ∈ family, coeff i • atomMatrix (tightDir i)) = 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [mul_smul_comm, tightDirection_gapAnnihilatesMultiplier D hdom (htight i hi),
    smul_zero]

end Gtz

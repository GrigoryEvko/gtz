/-
# The leverage-weighted average that GTZ derandomises

Volume sampling — the projection determinantal measure `π(C) = det P_C` on
`rank`-subsets (`Gtz.shadowDeterminant`, `Gtz.sum_shadowDeterminant_eq_one`) — has
first marginal `Pr[c ∈ C] = P_cc = t_c · ℓ_c`.  So the DPP-averaged atom sum is the
LEVERAGE-WEIGHTED atom sum

    leverageWeightedAtomSum D  =  ∑_c (t_c · ℓ_c) · g_c g_cᵀ,

and the headline of this file is that **that matrix is Loewner-above the identity,
at every size and every rank**, with the shares `s_c = t_c ℓ_c` — the very
quantities whose sum is the rank — as its coefficients.  GTZ asks for ONE
`rank`-subset above the identity; this file proves the AVERAGE is above the
identity.  GTZ is exactly the derandomisation of this inequality.

The proof is two elementary steps and no measure theory:

  * Cauchy–Schwarz per atom, `Gtz.atom_form_le_leverage`:  `⟨g_c,x⟩² ≤ ℓ_c ⟨x,x⟩`;
  * Jensen for the probability weights `t`, `sq_weightedMean_le_weightedMean_sq`:
    `(∑ t_c a_c)² ≤ ∑ t_c a_c²`, applied to `a_c = ⟨g_c,x⟩²` whose `t`-mean is
    `⟨x,x⟩` by Parseval (`sum_weight_mul_atomOverlap_sq`).  That Jensen step is
    NOT new: it is Mathlib's discrete Cauchy–Schwarz
    `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` specialised to probability
    weights, and the wrapper below is four lines over it.  An earlier revision of
    this file re-proved it from a hand-rolled weighted-variance identity on the
    false premise that Mathlib had no such lemma under a findable name; the
    duplicate is gone.  See also `Finset.sum_mul_sq_le_sq_mul_sq` (the squared
    form) and `Finset.sq_sum_div_le_sum_sq_div` (Sedrakyan).

Chaining them gives `⟨x,x⟩ · ∑_c t_c ℓ_c ⟨g_c,x⟩² ≥ ∑_c t_c ⟨g_c,x⟩⁴ ≥ ⟨x,x⟩²`,
which is the Rayleigh form of the headline once `⟨x,x⟩ > 0` is cancelled.  Every
step is homogeneous in `x`, so no normalisation and no division by a norm appears.

## PROVENANCE — what this file adds, and what was ALREADY SHIPPED

The campaign brief bundles this average (its item B1) with four chart items A1,
A2, A3, A4.  **All four of those are already in the repository**, and are NOT
re-proved here.  Consumers should go to the shipped declarations:

  * **A1** — domination is the chart inequality `P_C ⪰ diag t_C`:
    `Gtz.dominates_iff_posSemidef_projectionBlock{,_finset}` and the congruence
    `Gtz.projectionBlock_sub_weightDiagonal` (`Gtz/LinAlg/ProjectionForm.lean`),
    with the field-generic copy `Gtz.fieldDominates_iff_posSemidef_chartBlock`
    (`Gtz/Design/ProjectionChart.lean`).  The chart's Hermitian-idempotent facts
    are `Gtz.projectionOfDesign_transpose`, `_mul_self`, `_diagonal` and
    `Gtz.trace_projectionOfDesign`.  The UNSHIFTED congruence — the brief's
    `Gram_C = D_C^{-1/2} P_C D_C^{-1/2}` in the division-free form
    `√t · Gram_C · √t = P_C` — is shipped too, as
    `Gtz.projectionBlock_eq_congruence` with its determinant companion
    `Gtz.det_projectionBlock_of_design`; note that those two are parked in
    `Gtz/Ties/StratumFirstOrder.lean` under a layering debt its own header records,
    NOT beside the rest of the chart, so a reader looking only in
    `Gtz/LinAlg/ProjectionForm.lean` will not find them.  Nothing about the chart
    is re-derived here; the only chart brick this file adds is the diagonal square
    `sqrtWeightDiagonal_mul_self`, which had no name.
  * **A2** — the two Rayleigh statements: `Gtz.chartGapRayleigh_pos_of_fixed` and
    `Gtz.chartGapRayleigh_neg_of_killed` (`Gtz/Design/ProjectionChart.lean`).  Note
    the shipped `2 ≤ size` hypothesis and the theorem
    `Gtz.degenerateSingleton_chartGap_eq_zero` showing it cannot be dropped.
  * **A3** — the inertia no-go, at the brief's own matrix `!![-1, 3; 3, -1]`:
    `Gtz.inertiaNoGoMatrix`, `_det = -8`, `_no_posSemidef_principal`, plus the
    rank-two strengthening `Gtz.inertiaNoGoMatrixThree` and the escape clause
    `Gtz.exists_chartGap_diagonal_nonneg`.  Its rank-one positive counterpart
    `Gtz.exists_one_le_fieldLeverage` is shipped too; this file finishes that
    thought with the two steps it does not take —
    `dominates_singleton_iff_one_le_leverage` and `gtzWeighted_rank_one`.
  * **A4** — corank one: `Gtz.jensenRatio` with `Gtz.sum_jensenRatio_mul_coWeight`
    (A4 i), `Gtz.fieldDominates_erase_iff_coParsevalPivot_le_one` (A4 ii in the
    pivot chart), `Gtz.exists_jensenRatio_ge_weightedAverage` and
    `Gtz.fieldGtzWeighted_corank_one` (A4 iii),
    `Gtz.jensenRatio_eq_inv_rank_iff_leverageIdentity` (A4 iv, agreeing verbatim
    with `Gtz.isTie_iff_leverage_identity`).  `GtzWeighted (rank+1) rank` is
    therefore a SHIPPED result; nothing here reproves it.

So the genuinely new mathematics in this file is B1 together with the Parseval
probe identity and the rank-one closure.  The weighted-Jensen wrapper is exported
because `Gtz/Quantitative/ExpectedCharPolynomial.lean` consumes it a second time,
for the expected-characteristic-polynomial coefficient bound `c₁ ≥ rank²`.

## What is NOT claimed here

The identification of `leverageWeightedAtomSum` with the volume-sampling
EXPECTATION `∑_{|C| = rank} det P_C · S_C` needs the DPP one-point inclusion
identity `∑_{C ∋ c} det P_C = P_cc`, which is not in Mathlib and not in this
repository.  It is named — `IsProjectionOnePointMarginal` — with its construction
plan, and the identification is proved CONDITIONALLY on it
(`expectedSubsetSum_eq_leverageWeightedAtomSum`).  **The headline B1 does not
depend on it**: `posSemidef_leverageWeightedAtomSum_sub_one` is unconditional.

Strictness is likewise honest.  `leverageWeightedAtomSum ≻ 1` for `2 ≤ rank` is
NOT proved: the shipped strict statement
`lt_leverageWeightedAtomSum_form_of_transverseAtom` carries the transversality
hypothesis its proof actually uses (one atom neither orthogonal nor parallel to
the probe), because discharging that hypothesis from `2 ≤ rank` alone needs the
frame to have rank `≥ 2`, an argument this file does not run.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.MarginTransfer
import Gtz.Design.ProjectionChart
import Gtz.LinAlg.ProjectionForm
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.Reduction.ExchangeInvariant

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The weighted-Jensen wrapper

Jensen for a probability weighting, in the only form the campaign needs.  This is
Mathlib's discrete Cauchy–Schwarz, not new mathematics: instantiate
`Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` at `r_c = t_c a_c`, `f_c = t_c`,
`g_c = t_c a_c²` — where the hypothesis `r_c² ≤ f_c g_c` holds with EQUALITY — and
the `∑ f = 1` side collapses by the design axiom.  Exported under a name that
says what it means to this campaign, because
`Gtz/Quantitative/ExpectedCharPolynomial.lean` uses it again for `c₁ ≥ rank²`. -/

/-- **Weighted Jensen / discrete Cauchy–Schwarz.**  For nonnegative weights
summing to one, the square of the weighted mean is at most the weighted mean of
the squares.  A four-line specialisation of Mathlib's
`Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` (the file it lives in is titled for
the Cauchy–Schwarz inequality); do not re-derive it. -/
theorem sq_weightedMean_le_weightedMean_sq {size : ℕ} (weight value : Fin size → ℝ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hmass : ∑ index, weight index = 1) :
    (∑ index, weight index * value index) ^ 2
      ≤ ∑ index, weight index * value index ^ 2 := by
  have hcauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ) Finset.univ
    (r := fun index => weight index * value index) (f := weight)
    (g := fun index => weight index * value index ^ 2)
    (fun index _ => hnonneg index)
    (fun index _ => mul_nonneg (hnonneg index) (sq_nonneg _))
    (fun index _ => by ring_nf; exact le_refl _)
  rw [hmass, one_mul] at hcauchy
  exact hcauchy

/-- Weighted Jensen for a design's own weights, which are positive and sum to
one by definition. -/
theorem sq_weightedMean_le_weightedMean_sq_design (D : WeightedDesign m k)
    (value : Fin m → ℝ) :
    (∑ atomIndex, D.weight atomIndex * value atomIndex) ^ 2
      ≤ ∑ atomIndex, D.weight atomIndex * value atomIndex ^ 2 :=
  sq_weightedMean_le_weightedMean_sq D.weight value
    (fun atomIndex => (D.weight_pos atomIndex).le) D.weight_sum_one

/-! ## Parseval, read on a probe

The design axiom is a matrix identity; every use below needs only its scalar
shadow on a single probe vector. -/

/-- **Parseval on a probe.**  `∑_c t_c ⟨g_c, x⟩² = ⟨x, x⟩`.  This is the design
axiom contracted against one vector, and it is the only place the axiom is
consumed in this file. -/
theorem sum_weight_mul_atomOverlap_sq (D : WeightedDesign m k) (probe : Fin k → ℝ) :
    ∑ atomIndex, D.weight atomIndex * (D.atom atomIndex ⬝ᵥ probe) ^ 2 = probe ⬝ᵥ probe := by
  have hcontract : probe ⬝ᵥ ((∑ atomIndex, D.weight atomIndex • atomMatrix (D.atom atomIndex))
        *ᵥ probe)
      = ∑ atomIndex, D.weight atomIndex * (D.atom atomIndex ⬝ᵥ probe) ^ 2 := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]
  rw [← hcontract, D.isParseval, Matrix.one_mulVec]

/-- **Cauchy–Schwarz per atom, in overlap form.**  `⟨g_c, x⟩² ≤ ℓ_c ⟨x, x⟩`.  This
is `Gtz.atom_form_le_leverage` read through `Gtz.atom_form_eq_sq`. -/
theorem atomOverlap_sq_le_leverage_mul_normSq (atomVector probe : Fin k → ℝ) :
    (atomVector ⬝ᵥ probe) ^ 2 ≤ leverageOf atomVector * (probe ⬝ᵥ probe) := by
  rw [← atom_form_eq_sq]
  exact atom_form_le_leverage atomVector probe

/-! ## The leverage-weighted atom sum, and B1 -/

/-- **The leverage-weighted atom sum** `∑_c (t_c · ℓ_c) g_c g_cᵀ`.  Its
coefficients are the shares `s_c = t_c ℓ_c`, whose sum is the rank
(`Gtz.sum_weight_mul_leverage`).  Under the DPP one-point marginal it is the
volume-sampling expectation of the subset atom sum; see
`expectedSubsetSum_eq_leverageWeightedAtomSum`. -/
noncomputable def leverageWeightedAtomSum (D : WeightedDesign m k) :
    Matrix (Fin k) (Fin k) ℝ :=
  ∑ atomIndex, (D.weight atomIndex * leverageOf (D.atom atomIndex))
    • atomMatrix (D.atom atomIndex)

/-- The leverage-weighted atom sum is symmetric: every summand is a scaled
rank-one atom. -/
theorem leverageWeightedAtomSum_transpose (D : WeightedDesign m k) :
    (leverageWeightedAtomSum D)ᵀ = leverageWeightedAtomSum D := by
  rw [leverageWeightedAtomSum, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [Matrix.transpose_smul, atomMatrix, Matrix.transpose_vecMulVec]

theorem leverageWeightedAtomSum_isHermitian (D : WeightedDesign m k) :
    (leverageWeightedAtomSum D).IsHermitian :=
  isHermitian_of_transpose_eq (leverageWeightedAtomSum_transpose D)

/-- **The Rayleigh form of the average**: `⟨x, M x⟩ = ∑_c t_c ℓ_c ⟨g_c, x⟩²`. -/
theorem leverageWeightedAtomSum_form (D : WeightedDesign m k) (probe : Fin k → ℝ) :
    probe ⬝ᵥ (leverageWeightedAtomSum D *ᵥ probe)
      = ∑ atomIndex, D.weight atomIndex * leverageOf (D.atom atomIndex)
          * (D.atom atomIndex ⬝ᵥ probe) ^ 2 := by
  rw [leverageWeightedAtomSum, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]

/-- **The trace of the average is the expected-characteristic-polynomial
coefficient `c₁`.**  `trace (∑_c t_c ℓ_c g_c g_cᵀ) = ∑_c t_c ℓ_c²` — the quantity
`Gtz/Quantitative/ExpectedCharPolynomial.lean` calls `expectedElementary D 1` and
bounds below by `rank²`. -/
theorem trace_leverageWeightedAtomSum (D : WeightedDesign m k) :
    Matrix.trace (leverageWeightedAtomSum D)
      = ∑ atomIndex, D.weight atomIndex * leverageOf (D.atom atomIndex) ^ 2 := by
  rw [leverageWeightedAtomSum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [Matrix.trace_smul, trace_atomMatrix, smul_eq_mul]
  ring

/-- **The homogeneous core of B1.**  `⟨x, x⟩ · ⟨x, M x⟩ ≥ ⟨x, x⟩²`, at every probe
including zero.  Cauchy–Schwarz upgrades each summand
`t_c ⟨g_c,x⟩² · ⟨g_c,x⟩² ≤ t_c ⟨g_c,x⟩² · ℓ_c ⟨x,x⟩`, and Jensen on the probability
weights `t` bounds `∑_c t_c ⟨g_c,x⟩⁴` below by `(∑_c t_c ⟨g_c,x⟩²)² = ⟨x,x⟩²`.  No
division and no normalisation: the statement is homogeneous of degree four. -/
theorem normSq_mul_leverageWeightedAtomSum_form_ge (D : WeightedDesign m k)
    (probe : Fin k → ℝ) :
    (probe ⬝ᵥ probe) ^ 2
      ≤ (probe ⬝ᵥ probe) * (probe ⬝ᵥ (leverageWeightedAtomSum D *ᵥ probe)) := by
  have hjensen : (∑ atomIndex, D.weight atomIndex * (D.atom atomIndex ⬝ᵥ probe) ^ 2) ^ 2
      ≤ ∑ atomIndex, D.weight atomIndex * ((D.atom atomIndex ⬝ᵥ probe) ^ 2) ^ 2 :=
    sq_weightedMean_le_weightedMean_sq_design D
      fun atomIndex => (D.atom atomIndex ⬝ᵥ probe) ^ 2
  rw [sum_weight_mul_atomOverlap_sq D probe] at hjensen
  have hcauchy : ∀ atomIndex : Fin m,
      D.weight atomIndex * ((D.atom atomIndex ⬝ᵥ probe) ^ 2) ^ 2
        ≤ (probe ⬝ᵥ probe) * (D.weight atomIndex * leverageOf (D.atom atomIndex)
            * (D.atom atomIndex ⬝ᵥ probe) ^ 2) := by
    intro atomIndex
    have hoverlap := atomOverlap_sq_le_leverage_mul_normSq (D.atom atomIndex) probe
    have hfactorNonneg : 0 ≤ D.weight atomIndex * (D.atom atomIndex ⬝ᵥ probe) ^ 2 :=
      mul_nonneg (D.weight_pos atomIndex).le (sq_nonneg _)
    nlinarith [hoverlap, hfactorNonneg]
  have hsummed : ∑ atomIndex, D.weight atomIndex * ((D.atom atomIndex ⬝ᵥ probe) ^ 2) ^ 2
      ≤ ∑ atomIndex, (probe ⬝ᵥ probe) * (D.weight atomIndex * leverageOf (D.atom atomIndex)
          * (D.atom atomIndex ⬝ᵥ probe) ^ 2) :=
    Finset.sum_le_sum fun atomIndex _ => hcauchy atomIndex
  rw [← Finset.mul_sum Finset.univ
      (fun atomIndex => D.weight atomIndex * leverageOf (D.atom atomIndex)
        * (D.atom atomIndex ⬝ᵥ probe) ^ 2) (probe ⬝ᵥ probe),
    ← leverageWeightedAtomSum_form D probe] at hsummed
  linarith [hjensen, hsummed]

/-- **B1, in Rayleigh form**: `⟨x, x⟩ ≤ ⟨x, M x⟩` for every probe.  The zero probe
is separated off (both sides vanish); on a nonzero probe `⟨x,x⟩ > 0` cancels from
`normSq_mul_leverageWeightedAtomSum_form_ge`. -/
theorem normSq_le_leverageWeightedAtomSum_form (D : WeightedDesign m k)
    (probe : Fin k → ℝ) :
    probe ⬝ᵥ probe ≤ probe ⬝ᵥ (leverageWeightedAtomSum D *ᵥ probe) := by
  rcases eq_or_ne probe 0 with rfl | hnonzero
  · rw [dotProduct_zero, Matrix.mulVec_zero, dotProduct_zero]
  · have hpositive : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hnonzero
    have hcore := normSq_mul_leverageWeightedAtomSum_form_ge D probe
    have hproduct : (probe ⬝ᵥ probe) * (probe ⬝ᵥ probe)
        ≤ (probe ⬝ᵥ probe) * (probe ⬝ᵥ (leverageWeightedAtomSum D *ᵥ probe)) := by
      nlinarith [hcore]
    exact le_of_mul_le_mul_left hproduct hpositive

/-- **B1 — THE HEADLINE.**  The leverage-weighted atom sum is Loewner-above the
identity:

    ∑_c (t_c · ℓ_c) · g_c g_cᵀ  ⪰  1,

at every size and every rank, for every weighted design.  GTZ asks for a single
`rank`-subset with `∑_{c ∈ C} g_c g_cᵀ ⪰ 1`; this says the volume-sampling AVERAGE
of those subset sums already is, so the conjecture is exactly the derandomisation
of this inequality.  Contrast `Gtz.not_mixedRootAtLeastOne_sixThree`: the same
average taken through `λ_min` instead of through the matrix is FALSE, which is why
the campaign's expected-polynomial instruments and not the matrix average are the
live route. -/
theorem posSemidef_leverageWeightedAtomSum_sub_one (D : WeightedDesign m k) :
    (leverageWeightedAtomSum D - 1).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq ?_, fun probe => ?_⟩
  · rw [Matrix.transpose_sub, Matrix.transpose_one, leverageWeightedAtomSum_transpose]
  · have hform : star probe ⬝ᵥ ((leverageWeightedAtomSum D - 1) *ᵥ probe)
        = (probe ⬝ᵥ (leverageWeightedAtomSum D *ᵥ probe)) - probe ⬝ᵥ probe := by
      rw [show (star probe : Fin k → ℝ) = probe from rfl, Matrix.sub_mulVec, dotProduct_sub,
        Matrix.one_mulVec]
    rw [hform, sub_nonneg]
    exact normSq_le_leverageWeightedAtomSum_form D probe

/-- **The trace consequence, and why B1 is weaker than the polynomial bound.**
B1 gives `trace M ≥ rank`, i.e. `∑_c t_c ℓ_c² ≥ rank`.  Jensen on the same shares
gives `∑_c t_c ℓ_c² ≥ rank²`
(`Gtz.sq_rank_le_expectedElementary_one`, `Gtz/Quantitative/ExpectedCharPolynomial.lean`),
which is STRICTLY stronger exactly when `2 ≤ rank` — at rank zero and rank one the
two bounds coincide, since `rank² = rank` there.  So for every rank the campaign
cares about, B1's trace shadow is NOT the sharpest thing the shares know, and the
matrix statement is what B1 is for. -/
theorem rank_le_sum_weight_mul_leverage_sq (D : WeightedDesign m k) :
    (k : ℝ) ≤ ∑ atomIndex, D.weight atomIndex * leverageOf (D.atom atomIndex) ^ 2 := by
  have htrace : Matrix.trace (leverageWeightedAtomSum D - 1)
      = (∑ atomIndex, D.weight atomIndex * leverageOf (D.atom atomIndex) ^ 2) - (k : ℝ) := by
    rw [Matrix.trace_sub, trace_leverageWeightedAtomSum, Matrix.trace_one, Fintype.card_fin]
  have hnonneg : 0 ≤ Matrix.trace (leverageWeightedAtomSum D - 1) :=
    (posSemidef_leverageWeightedAtomSum_sub_one D).trace_nonneg
  rw [htrace] at hnonneg
  linarith

/-! ### Strictness, with the hypothesis its proof uses

`M ≻ 1` for `2 ≤ rank` is NOT proved here.  What IS proved is the strict form with
the transversality that the Cauchy–Schwarz step actually consumes: one atom that
overlaps the probe (so its summand is live) but is not parallel to it (so its
Cauchy–Schwarz is strict).  Discharging that from `2 ≤ rank` alone would need the
frame's rank, which this file does not develop. -/

/-- **Strict B1 at a probe, conditionally.**  If some atom has strictly positive
overlap with the probe and strictly sub-Cauchy–Schwarz overlap — that is,
`0 < ⟨g_c,x⟩²` and `⟨g_c,x⟩² < ℓ_c ⟨x,x⟩`, so `g_c` is neither orthogonal nor
parallel to `x` — then the average's Rayleigh value at `x` STRICTLY exceeds
`⟨x, x⟩`. -/
theorem lt_leverageWeightedAtomSum_form_of_transverseAtom (D : WeightedDesign m k)
    (probe : Fin k → ℝ) (hnonzero : probe ≠ 0) {witness : Fin m}
    (hlive : 0 < (D.atom witness ⬝ᵥ probe) ^ 2)
    (htransverse : (D.atom witness ⬝ᵥ probe) ^ 2
      < leverageOf (D.atom witness) * (probe ⬝ᵥ probe)) :
    probe ⬝ᵥ probe < probe ⬝ᵥ (leverageWeightedAtomSum D *ᵥ probe) := by
  have hpositive : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hnonzero
  have hjensen : (∑ atomIndex, D.weight atomIndex * (D.atom atomIndex ⬝ᵥ probe) ^ 2) ^ 2
      ≤ ∑ atomIndex, D.weight atomIndex * ((D.atom atomIndex ⬝ᵥ probe) ^ 2) ^ 2 :=
    sq_weightedMean_le_weightedMean_sq_design D
      fun atomIndex => (D.atom atomIndex ⬝ᵥ probe) ^ 2
  rw [sum_weight_mul_atomOverlap_sq D probe] at hjensen
  have hcauchy : ∀ atomIndex : Fin m,
      D.weight atomIndex * ((D.atom atomIndex ⬝ᵥ probe) ^ 2) ^ 2
        ≤ (probe ⬝ᵥ probe) * (D.weight atomIndex * leverageOf (D.atom atomIndex)
            * (D.atom atomIndex ⬝ᵥ probe) ^ 2) := by
    intro atomIndex
    have hoverlap := atomOverlap_sq_le_leverage_mul_normSq (D.atom atomIndex) probe
    have hfactorNonneg : 0 ≤ D.weight atomIndex * (D.atom atomIndex ⬝ᵥ probe) ^ 2 :=
      mul_nonneg (D.weight_pos atomIndex).le (sq_nonneg _)
    nlinarith [hoverlap, hfactorNonneg]
  have hstrictWitness : D.weight witness * ((D.atom witness ⬝ᵥ probe) ^ 2) ^ 2
      < (probe ⬝ᵥ probe) * (D.weight witness * leverageOf (D.atom witness)
          * (D.atom witness ⬝ᵥ probe) ^ 2) := by
    have hfactorPos : 0 < D.weight witness * (D.atom witness ⬝ᵥ probe) ^ 2 :=
      mul_pos (D.weight_pos witness) hlive
    nlinarith [htransverse, hfactorPos]
  have hsummed : ∑ atomIndex, D.weight atomIndex * ((D.atom atomIndex ⬝ᵥ probe) ^ 2) ^ 2
      < ∑ atomIndex, (probe ⬝ᵥ probe) * (D.weight atomIndex * leverageOf (D.atom atomIndex)
          * (D.atom atomIndex ⬝ᵥ probe) ^ 2) :=
    Finset.sum_lt_sum (fun atomIndex _ => hcauchy atomIndex)
      ⟨witness, Finset.mem_univ witness, hstrictWitness⟩
  rw [← Finset.mul_sum Finset.univ
      (fun atomIndex => D.weight atomIndex * leverageOf (D.atom atomIndex)
        * (D.atom atomIndex ⬝ᵥ probe) ^ 2) (probe ⬝ᵥ probe),
    ← leverageWeightedAtomSum_form D probe] at hsummed
  have hproduct : (probe ⬝ᵥ probe) * (probe ⬝ᵥ probe)
      < (probe ⬝ᵥ probe) * (probe ⬝ᵥ (leverageWeightedAtomSum D *ᵥ probe)) := by
    nlinarith [hjensen, hsummed]
  exact lt_of_mul_lt_mul_left hproduct hpositive.le

/-! ## The volume-sampling expectation, and the marginal it needs

The average B1 bounds is the DPP expectation only after the one-point inclusion
identity.  That identity is stated as a `Prop` and used as a hypothesis; the
headline does not touch it. -/

/-- The volume-sampling expectation of the subset atom sum:
`∑_{|C| = rank} det P_C · S_C`, a genuine convex combination because the shadow
determinants are nonnegative and sum to one
(`Gtz.sum_shadowDeterminant_eq_one`). -/
noncomputable def expectedSubsetSum (D : WeightedDesign m k) : Matrix (Fin k) (Fin k) ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
    shadowDeterminant D selected • subsetSum D selected

/-- **The DPP one-point inclusion identity, NAMED not proved.**  For the
projection chart `P` of a design, `∑_{|C| = rank, c ∈ C} det P_C = P_cc = t_c ℓ_c`
— the first marginal of the projection determinantal point process.

Status: CITED as standard DPP theory (Borcea–Brändén–Liggett; Kulesza–Taskar
§2.4.3, `Pr[J ⊆ C] = det K_J`), NOT in Mathlib and NOT in this repository.  What
the repository does have is the total mass at each size,
`Gtz.sum_det_projectionMinors` / `Gtz.sum_shadowDeterminant_eq_one`, which is the
`J = ∅` case only.

Construction plan, recorded so the cost is visible.  Write `P = V Vᵀ` with
`VᵀV = 1` (`Gtz.transpose_mul_scaledAtomRows`), so `det P_C = det(V_C)²` by
Cauchy–Binet at full size and `P_cc = |v_c|²`.  Scale row and column `c` of `P` by
`√s`: the minors pick up `s^[c ∈ C]`, so
`det(1 + X · P · diag(1,…,s,…,1))` has `X^rank`-coefficient
`∑_{|C| = rank} s^[c ∈ C] det P_C`, and differentiating at `s = 1` extracts the
marginal.  Mechanising that needs a bivariate
`Matrix.coeff_det_one_add_X_smul_eq_sum_minors` argument; it is a standalone
build, not a step inside another proof.  Only the aggregate consequence
`∑_c (that marginal) = rank` is currently available, and it is strictly weaker. -/
def IsProjectionOnePointMarginal (D : WeightedDesign m k) : Prop :=
  ∀ atomIndex : Fin m,
    (∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      if atomIndex ∈ selected then shadowDeterminant D selected else 0)
      = D.weight atomIndex * leverageOf (D.atom atomIndex)

/-- **B1's title, CONDITIONALLY on the marginal.**  Given the DPP one-point
inclusion identity, the volume-sampling expectation of the subset atom sum IS the
leverage-weighted atom sum, so `posSemidef_leverageWeightedAtomSum_sub_one` reads
`E_π[S_C] ⪰ 1` verbatim.  The exchange of summation is the whole proof; the
marginal supplies the coefficient. -/
theorem expectedSubsetSum_eq_leverageWeightedAtomSum (D : WeightedDesign m k)
    (hmarginal : IsProjectionOnePointMarginal D) :
    expectedSubsetSum D = leverageWeightedAtomSum D := by
  classical
  have hexchange : expectedSubsetSum D
      = ∑ atomIndex, (∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          if atomIndex ∈ selected then shadowDeterminant D selected else 0)
        • atomMatrix (D.atom atomIndex) := by
    rw [expectedSubsetSum]
    have hinner : ∀ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        shadowDeterminant D selected • subsetSum D selected
          = ∑ atomIndex, (if atomIndex ∈ selected then shadowDeterminant D selected else 0)
            • atomMatrix (D.atom atomIndex) := by
      intro selected _
      rw [subsetSum, Finset.smul_sum, ← Finset.sum_filter_add_sum_filter_not
        Finset.univ (fun atomIndex => atomIndex ∈ selected)]
      have hleft : ∑ atomIndex ∈ Finset.univ.filter (fun atomIndex => atomIndex ∈ selected),
            (if atomIndex ∈ selected then shadowDeterminant D selected else 0)
              • atomMatrix (D.atom atomIndex)
          = ∑ atomIndex ∈ selected, shadowDeterminant D selected • atomMatrix (D.atom atomIndex) := by
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        exact Finset.sum_congr rfl fun atomIndex hmem => by rw [if_pos hmem]
      have hright : ∑ atomIndex ∈ Finset.univ.filter (fun atomIndex => atomIndex ∉ selected),
            (if atomIndex ∈ selected then shadowDeterminant D selected else 0)
              • atomMatrix (D.atom atomIndex)
          = 0 := by
        refine Finset.sum_eq_zero fun atomIndex hmem => ?_
        rw [if_neg (Finset.mem_filter.mp hmem).2, zero_smul]
      rw [hleft, hright, add_zero]
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    exact Finset.sum_congr rfl fun atomIndex _ => (Finset.sum_smul).symm
  rw [hexchange, leverageWeightedAtomSum]
  exact Finset.sum_congr rfl fun atomIndex _ => by rw [hmarginal atomIndex]

/-! ## One chart brick: the congruence basis squares to the weight diagonal

The unshifted congruence itself is NOT proved here — it is already shipped as
`Gtz.projectionBlock_eq_congruence` (`Gtz/Ties/StratumFirstOrder.lean`), whose own
header records that it is parked there under a layering debt rather than beside
`Gtz.projectionBlock_sub_weightDiagonal`.  What was missing is only the elementary
diagonal square it and every other positive-diagonal congruence step rest on. -/

/-- The congruence basis squares to the weight diagonal: `diag √t · diag √t =
diag t`.  Positive diagonal only; no matrix square root, no inverse. -/
theorem sqrtWeightDiagonal_mul_self (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) :
    sqrtWeightDiagonal D pick * sqrtWeightDiagonal D pick
      = Matrix.diagonal fun selectedIndex => D.weight (pick selectedIndex) := by
  rw [sqrtWeightDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext selectedIndex
  exact Real.mul_self_sqrt (D.weight_pos (pick selectedIndex)).le

/-- **The gap form and the unshifted form differ by exactly `diag t`.**  This is
the bridge between the shipped gap congruence
`Gtz.projectionBlock_sub_weightDiagonal` and the shipped unshifted congruence
`Gtz.projectionBlock_eq_congruence` (`Gtz/Ties/StratumFirstOrder.lean`), which
were proved independently of each other; the only content is
`sqrtWeightDiagonal_mul_self`.  Stated so that a reader who has one of the two
never has to redo the other. -/
theorem sqrtWeightCongruence_gap_eq_sub_weightDiagonal (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) :
    (sqrtWeightDiagonal D pick)ᵀ
        * (selectedAtomRows D pick * (selectedAtomRows D pick)ᵀ - 1)
        * sqrtWeightDiagonal D pick
      = (sqrtWeightDiagonal D pick)ᵀ
          * (selectedAtomRows D pick * (selectedAtomRows D pick)ᵀ)
          * sqrtWeightDiagonal D pick
        - Matrix.diagonal fun selectedIndex => D.weight (pick selectedIndex) := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, sqrtWeightDiagonal,
    Matrix.diagonal_transpose, ← sqrtWeightDiagonal, sqrtWeightDiagonal_mul_self]

/-! ## Rank one, closed

`Gtz.exists_one_le_fieldLeverage` supplies the atom whose leverage is at least
one and its docstring asserts that atom "already dominates", but the domination
step is not taken there.  It is taken here, and it closes `GtzWeighted m 1`
outright — the positive counterpart to A3's inertia no-go, which says the same
inertia data proves nothing at rank one. -/

/-- At rank one a singleton's atom sum is the leverage, as a `1 × 1` matrix. -/
theorem subsetSum_singleton_apply (D : WeightedDesign m 1) (atomIndex : Fin m)
    (rowCoord colCoord : Fin 1) :
    subsetSum D {atomIndex} rowCoord colCoord = leverageOf (D.atom atomIndex) := by
  have hrow : rowCoord = 0 := Subsingleton.elim rowCoord 0
  have hcol : colCoord = 0 := Subsingleton.elim colCoord 0
  subst hrow; subst hcol
  rw [subsetSum, Finset.sum_singleton, atomMatrix, Matrix.vecMulVec_apply, leverageOf,
    Fin.sum_univ_one]
  ring

/-- **Rank one: a singleton dominates exactly when its leverage reaches one.**  At
rank one the gap `S_{c} − 1` is the `1 × 1` matrix `[ℓ_c − 1]`, whose positive
semidefiniteness is the scalar inequality. -/
theorem dominates_singleton_iff_one_le_leverage (D : WeightedDesign m 1) (atomIndex : Fin m) :
    Dominates D {atomIndex} ↔ 1 ≤ leverageOf (D.atom atomIndex) := by
  have hentry : ∀ rowCoord colCoord : Fin 1,
      (subsetSum D {atomIndex} - 1) rowCoord colCoord
        = leverageOf (D.atom atomIndex) - 1 := by
    intro rowCoord colCoord
    have hrow : rowCoord = 0 := Subsingleton.elim rowCoord 0
    have hcol : colCoord = 0 := Subsingleton.elim colCoord 0
    subst hrow; subst hcol
    rw [Matrix.sub_apply, subsetSum_singleton_apply, Matrix.one_apply_eq]
  refine ⟨fun hdominates => ?_, fun hleverage => ?_⟩
  · have hdiag := hdominates.diag_nonneg (i := (0 : Fin 1))
    rw [hentry] at hdiag
    linarith
  · refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨isHermitian_of_transpose_eq ?_, ?_⟩
    · ext rowCoord colCoord
      rw [Matrix.transpose_apply, hentry, hentry]
    · intro probe
      have hform : star probe ⬝ᵥ ((subsetSum D {atomIndex} - 1) *ᵥ probe)
          = (leverageOf (D.atom atomIndex) - 1) * probe 0 ^ 2 := by
        rw [show (star probe : Fin 1 → ℝ) = probe from rfl, dotProduct, Fin.sum_univ_one,
          Matrix.mulVec, dotProduct, Fin.sum_univ_one, hentry]
        ring
      rw [hform]
      exact mul_nonneg (by linarith) (sq_nonneg _)

/-- A weighted design over an empty atom index does not exist: its weights would
have to sum to one over an empty sum.  So every size hypothesis of the form
`0 < m` is discardable once a design is in hand, and the rank-one theorem below
needs no such side condition. -/
theorem pos_of_weightedDesign (D : WeightedDesign m k) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with hzero | hpos
  · exfalso
    have hsum := D.weight_sum_one
    subst hzero
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact absurd hsum (by norm_num)
  · exact hpos

/-- **RANK ONE IS A THEOREM.**  Every weighted `(m, 1)`-design has a dominating
singleton: the weighted leverages sum to the rank, which at rank one is the total
weight, so the maximum leverage is at least one
(`Gtz.exists_one_le_fieldLeverage`) and
`dominates_singleton_iff_one_le_leverage` converts that into domination.  This is
the rank-one entry of the size axis, and the positive fact A3's inertia no-go is
contrasted against.

Unconditional: `exists_one_le_fieldLeverage` wants `0 < m`, but `pos_of_weightedDesign`
supplies it from the design itself, so no size hypothesis is carried.  (At `m = 0`
the statement is vacuously true because `WeightedDesign 0 1` is uninhabited.) -/
theorem gtzWeighted_rank_one : GtzWeighted m 1 := by
  intro D
  obtain ⟨atomIndex, hleverage⟩ :=
    exists_one_le_fieldLeverage (ofRealDesign D) (pos_of_weightedDesign D)
  rw [fieldLeverageOf_eq_leverageOf] at hleverage
  exact ⟨{atomIndex}, Finset.card_singleton atomIndex,
    (dominates_singleton_iff_one_le_leverage D atomIndex).mpr hleverage⟩

end Gtz

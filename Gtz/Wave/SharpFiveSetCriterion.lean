/-
# The total gap, the co-atom reading, and the five-set criterion

Every weighted design carries one distinguished positive definite form: the gap of
its WHOLE atom set,

    `G := S_all - 1`,   `S_all = Sum_c g_c g_c^T` .

Positivity is one line of Parseval and the tree already owns it
(`Gtz.posDef_subsetSum_univ_sub_one`), but the form itself has never been given a
name or a calculus.  This module builds that calculus and reads the CO-ATOM sets
-- the `m-1` element sets `univ.erase c` -- through it.

## 1. The reading, and the co-atom dichotomy

Put `rho_c := g_c . G^{-1} g_c` (`Gtz.totalGapReading`).  The co-atom gap is a
rank-one downdate of `G`,

    `S_{univ.erase c} - 1 = G - g_c g_c^T`   (`Gtz.gap_erase_eq_totalGap_sub`),

so the whole Schur calculus applies and the dichotomy is exact:

* `det (S_{erase c} - 1) = det G * (1 - rho_c)`  (`Gtz.det_gap_erase_eq`)
* the co-atom set dominates STRICTLY iff `rho_c < 1`  (`Gtz.posDef_gap_erase_iff`)
* it dominates WEAKLY iff `rho_c <= 1`  (`Gtz.posSemidef_gap_erase_iff`)
* it is a corank-one weak dominator exactly at `rho_c = 1`.

## 2. The reading budget, and a free counting theorem

Parseval prices the whole reading vector.  Two moment laws, both general in
`(m,k)`:

    `Sum_c t_c * (g_c . A g_c) = tr A`          (`Gtz.sum_weight_mul_reading_eq_trace_gen`)
    `Sum_c (g_c . A g_c) = tr (A * S_all)`      (`Gtz.sum_reading_eq_trace_mul_total`)

Subtracting at `A = G^{-1}` telescopes onto `tr (G^{-1} G) = tr 1`:

    **`Sum_c (1 - t_c) * rho_c = k`**   (`Gtz.sum_one_sub_weight_mul_totalGapReading`).

As a BUDGET this is exact and it is the reason the naive trace attack on the
co-atom stratum is vacuous: the total is `k` at EVERY design, so it never
separates one design from another.  As a COUNT it is not vacuous at all.  The
weights `1 - t_c` sum to `m - 1`, so the labels that fail `rho_c < 1` carry at
most `k` of that mass, and since each carries more than `1 - t_c`,

    **at least `m - k - 1` co-atom sets of every design dominate STRICTLY**
    (`Gtz.card_le_of_forall_one_le_totalGapReading`,
     `Gtz.exists_posDef_gap_erase`).

At `(6,3)` that is two of the six five-sets, with no hypothesis whatever.  The
`(6,3)` reading of the budget is `Sum_c (1 - t_c) rho_c = 3` against
`Sum_c (1 - t_c) = 5`, so the average reading is `3/5`.

## 3. The metric transfer

`G^{-1}` is positive definite, so it is an inner product, and Cauchy-Schwarz
equality in ANY inner product says the same thing about the two vectors.  The
general statement is `Gtz.gramDefect_eq_zero_iff`: for `N` positive definite the
defect `(u.Nu)(v.Nv) - (u.Nv)^2` vanishes exactly when `u` and `v` are dependent.
Reading it at `N = 1` and at `N = G^{-1}` gives

    **`rho_p rho_q - (g_p . G^{-1} g_q)^2 = 0`  iff  `l_p l_q - p_pq^2 = 0`**
    (`Gtz.totalGapDefect_eq_zero_iff_leverageDefect_eq_zero`),

both being `g_p` parallel to `g_q` (`Gtz.hasParallelPair_of_totalGapDefect_eq_zero`).
So the parallel pairs of a design are visible in the `G^{-1}` metric, unchanged.

## 4. The co-share pair form

The complementary quantity of a pair is the CO-SHARE product against the weighted
pairing, `u_p u_q - t_p t_q p_pq^2` with `u_c = 1 - t_c l_c`
(`Gtz.coSharePairForm`).  It is the two by two determinant of the complementary
projection of the design's chart, and this file lands its determinant form and its
symmetry.  The campaign's pairing cap is exactly the statement that it is
nonnegative.

## What is measured and NOT proved here

Three statements were verified numerically in `scratchpad/fiveset` and are NOT
landed, because each needs the EXPLICIT sharp design and `Gtz.NaimarkSharpDesign`
exports existence only.  They are recorded so a successor does not re-derive them:

* `1 - shat_c = (1 - t_c) * rho_c`, the sharp share against the co-atom reading.
  Verified to `1.9e-14` at ten cells `(6,3) (5,3) (7,3) (5,2) (4,2) (7,4) (8,4)
  (6,4) (4,3) (9,5)`.  Proof in hand: `shat` is the leverage-score vector of
  `diag(sqrt(t/(1-t))) U`, whose orthogonal complement is spanned by
  `diag(sqrt(1-t)) V`, and that matrix has Gram exactly `G` and rows
  `sqrt(1-t_c) g_c`.
* `Phat = 1 - R` with `R` the projection onto the column space of
  `diag(sqrt(1-t)) V`; verified to `2.4e-14`.  Hence `D` has a parallel pair at
  `{p,q}` iff the sharp dual has four coplanar atoms at the complementary set --
  BOTH conditions reduce to `g_p` parallel to `g_q`, by section 3 above.
* At a `(6,3)` TIE all four conditions coincide: parallel pair in `D`, four
  coplanar in `D`, parallel pair in the dual, four coplanar in the dual.  Checked
  on the split diamond, where the coplanar four-sets are exactly the two triangles
  of `K4 - e` through the split edge, lifted by the parallel pair.

Also measured: the trace attack on the co-atom stratum is EXACTLY vacuous, at
`2.7e-15` over sixty designs, which section 2 explains.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Design.CapSlack
import Gtz.Design.LeverageBound
import Gtz.Design.StratumTieFreeClasses
import Gtz.Reduction.DescentLadder
import Gtz.Reduction.SplitTransfer
import Gtz.LinAlg.SchurRankOne
import Gtz.Quantitative.GlobalMinimumRankThree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1 — the total gap -/

/-- **THE TOTAL GAP** of a design: the gap matrix of its whole atom set. -/
noncomputable def totalGap (D : WeightedDesign m k) : Matrix (Fin k) (Fin k) ℝ :=
  subsetSum D Finset.univ - 1

/-- The total gap is positive definite once the design has two atoms. -/
theorem posDef_totalGap (D : WeightedDesign m k) (hm : 2 ≤ m) : (totalGap D).PosDef :=
  posDef_subsetSum_univ_sub_one D hm

theorem isUnit_det_totalGap (D : WeightedDesign m k) (hm : 2 ≤ m) :
    IsUnit (totalGap D).det :=
  isUnit_iff_ne_zero.mpr (ne_of_gt (posDef_totalGap D hm).det_pos)

theorem totalGap_transpose (D : WeightedDesign m k) : (totalGap D)ᵀ = totalGap D := by
  rw [totalGap, Matrix.transpose_sub, Matrix.transpose_one, subsetSum, Matrix.transpose_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by
    simp only [atomMatrix, Matrix.transpose_vecMulVec]

/-- **THE QUADRATIC FORM OF THE TOTAL GAP.**  Parseval turns it into a sum of
CO-WEIGHTED squares, one per atom.  Positivity is immediate from this shape and
the reading of Parseval at the probe. -/
theorem quadForm_totalGap (D : WeightedDesign m k) (probe : Fin k → ℝ) :
    probe ⬝ᵥ (totalGap D *ᵥ probe)
      = ∑ label, (1 - D.weight label) * (D.atom label ⬝ᵥ probe) ^ 2 := by
  have hsum : probe ⬝ᵥ (subsetSum D Finset.univ *ᵥ probe)
      = ∑ label, (D.atom label ⬝ᵥ probe) ^ 2 := by
    rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun label _ => dotProduct_atomMatrix_mulVec (D.atom label) probe
  have hpars : ∑ label, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2 = probe ⬝ᵥ probe := by
    rw [← sum_weighted_atomPairing D probe probe]
    exact Finset.sum_congr rfl fun label _ => by ring
  rw [totalGap, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hsum, ← hpars,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun label _ => by ring

/-! ## Part 2 — the co-atom reading -/

/-- **THE CO-ATOM READING** `rho_c = g_c . G^{-1} g_c`: the atom read in the metric
of the total gap.  It decides the co-atom set `univ.erase c` outright. -/
noncomputable def totalGapReading (D : WeightedDesign m k) (label : Fin m) : ℝ :=
  D.atom label ⬝ᵥ ((totalGap D)⁻¹ *ᵥ D.atom label)

/-- The inverse of the total gap is positive definite. -/
theorem posDef_totalGap_inv (D : WeightedDesign m k) (hm : 2 ≤ m) :
    ((totalGap D)⁻¹).PosDef :=
  (posDef_totalGap D hm).inv

theorem totalGapReading_nonneg (D : WeightedDesign m k) (hm : 2 ≤ m) (label : Fin m) :
    0 ≤ totalGapReading D label := by
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
    (posDef_totalGap_inv D hm).posSemidef).2 (D.atom label)
  rw [star_trivial] at h
  exact h

theorem totalGapReading_pos_of_atom_ne_zero (D : WeightedDesign m k) (hm : 2 ≤ m)
    {label : Fin m} (hne : D.atom label ≠ 0) : 0 < totalGapReading D label := by
  have h := (Matrix.posDef_iff_dotProduct_mulVec.mp (posDef_totalGap_inv D hm)).2 hne
  rw [star_trivial] at h
  exact h

/-- **THE CO-ATOM GAP IS A RANK-ONE DOWNDATE OF THE TOTAL GAP.**  Erasing one label
removes exactly that label's atom matrix. -/
theorem gap_erase_eq_totalGap_sub (D : WeightedDesign m k) (label : Fin m) :
    subsetSum D (Finset.univ.erase label) - 1
      = totalGap D - atomMatrix (D.atom label) := by
  have hsplit : subsetSum D Finset.univ
      = subsetSum D (Finset.univ.erase label) + atomMatrix (D.atom label) := by
    rw [subsetSum, subsetSum, Finset.sum_erase_add _ _ (Finset.mem_univ label)]
  rw [totalGap, hsplit]
  abel

/-- **THE CO-ATOM DETERMINANT.**  The rank-one determinant lemma in the metric of
the total gap. -/
theorem det_gap_erase_eq (D : WeightedDesign m k) (hm : 2 ≤ m) (label : Fin m) :
    (subsetSum D (Finset.univ.erase label) - 1).det
      = (totalGap D).det * (1 - totalGapReading D label) := by
  rw [gap_erase_eq_totalGap_sub D label,
    det_sub_atomMatrix (isUnit_det_totalGap D hm) (D.atom label), totalGapReading]

/-- **THE CO-ATOM SET DOMINATES STRICTLY EXACTLY WHEN ITS READING IS BELOW ONE.** -/
theorem posDef_gap_erase_iff (D : WeightedDesign m k) (hm : 2 ≤ m) (label : Fin m) :
    (subsetSum D (Finset.univ.erase label) - 1).PosDef ↔ totalGapReading D label < 1 := by
  rw [gap_erase_eq_totalGap_sub D label, atomMatrix]
  exact posDef_sub_vecMulVec_iff (totalGap D) (posDef_totalGap D hm) (D.atom label)

/-- **THE CO-ATOM SET DOMINATES WEAKLY EXACTLY WHEN ITS READING IS AT MOST ONE.** -/
theorem posSemidef_gap_erase_iff (D : WeightedDesign m k) (hm : 2 ≤ m) (label : Fin m) :
    (subsetSum D (Finset.univ.erase label) - 1).PosSemidef ↔ totalGapReading D label ≤ 1 := by
  rw [gap_erase_eq_totalGap_sub D label, atomMatrix]
  exact posSemidef_sub_vecMulVec_iff (totalGap D) (posDef_totalGap D hm) (D.atom label)

/-- **THE CORANK-ONE CO-ATOM.**  Reading exactly one is exactly a weak dominator
that is not a strict one: a corank-one weak dominator of size `m - 1`. -/
theorem gap_erase_corankOne_iff (D : WeightedDesign m k) (hm : 2 ≤ m) (label : Fin m) :
    ((subsetSum D (Finset.univ.erase label) - 1).PosSemidef
        ∧ ¬ (subsetSum D (Finset.univ.erase label) - 1).PosDef)
      ↔ totalGapReading D label = 1 := by
  rw [posSemidef_gap_erase_iff D hm label, posDef_gap_erase_iff D hm label]
  constructor
  · rintro ⟨hle, hnot⟩
    exact le_antisymm hle (not_lt.mp hnot)
  · intro heq
    exact ⟨le_of_eq heq, by rw [heq]; exact lt_irrefl 1⟩

/-- Reading one makes the co-atom gap singular. -/
theorem det_gap_erase_eq_zero_of_reading_eq_one (D : WeightedDesign m k) (hm : 2 ≤ m)
    {label : Fin m} (hread : totalGapReading D label = 1) :
    (subsetSum D (Finset.univ.erase label) - 1).det = 0 := by
  rw [det_gap_erase_eq D hm label, hread, sub_self, mul_zero]

/-! ## Part 3 — the reading budget

Two moment laws price every quadratic reading of the design against an arbitrary
form.  Both are the same double-sum swap, once against the weights and once
against one. -/

/-- A rank-one reading is a trace against the atom matrix, at every rank. -/
theorem dotProduct_mulVec_eq_trace_mul_atomMatrix_gen (form : Matrix (Fin k) (Fin k) ℝ)
    (vec : Fin k → ℝ) :
    vec ⬝ᵥ (form *ᵥ vec) = Matrix.trace (form * atomMatrix vec) := by
  rw [Matrix.trace, dotProduct]
  refine Finset.sum_congr rfl fun rowIndex _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun colIndex _ => ?_
  rw [atomMatrix, Matrix.vecMulVec_apply]
  ring

/-- The shared core: a weighted total of readings is the trace against the
correspondingly weighted atom total. -/
theorem sum_smul_reading_eq_trace (D : WeightedDesign m k)
    (form : Matrix (Fin k) (Fin k) ℝ) (coeff : Fin m → ℝ) :
    ∑ label, coeff label * (D.atom label ⬝ᵥ (form *ᵥ D.atom label))
      = Matrix.trace (form * ∑ label, coeff label • atomMatrix (D.atom label)) := by
  have hstep : ∀ label : Fin m,
      coeff label * (D.atom label ⬝ᵥ (form *ᵥ D.atom label))
        = Matrix.trace (form * (coeff label • atomMatrix (D.atom label))) := by
    intro label
    rw [dotProduct_mulVec_eq_trace_mul_atomMatrix_gen, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul]
  rw [Finset.sum_congr rfl fun label _ => hstep label, Finset.mul_sum, Matrix.trace_sum]

/-- **PARSEVAL PRICES A READING TOTAL.**  Weighted by the design, every reading
totals the trace of the form.  General in `(m,k)`. -/
theorem sum_weight_mul_reading_eq_trace_gen (D : WeightedDesign m k)
    (form : Matrix (Fin k) (Fin k) ℝ) :
    ∑ label, D.weight label * (D.atom label ⬝ᵥ (form *ᵥ D.atom label))
      = Matrix.trace form := by
  rw [sum_smul_reading_eq_trace D form D.weight, D.isParseval, Matrix.mul_one]

/-- **THE UNWEIGHTED READING TOTAL** is the trace against the whole atom sum. -/
theorem sum_reading_eq_trace_mul_total (D : WeightedDesign m k)
    (form : Matrix (Fin k) (Fin k) ℝ) :
    ∑ label, (D.atom label ⬝ᵥ (form *ᵥ D.atom label))
      = Matrix.trace (form * subsetSum D Finset.univ) := by
  have hone := sum_smul_reading_eq_trace D form (fun _ => (1 : ℝ))
  simp only [one_mul, one_smul] at hone
  rw [hone, subsetSum]

/-- **THE READING BUDGET.**  The co-weighted total of the co-atom readings is the
RANK, at every design.  Two moment laws telescope onto `tr (G^{-1} G)`.

As a separating instrument this is vacuous — the total is `k` at every design, so
no descent on it can distinguish one design from another.  Its value is the COUNT
below. -/
theorem sum_one_sub_weight_mul_totalGapReading (D : WeightedDesign m k) (hm : 2 ≤ m) :
    ∑ label, (1 - D.weight label) * totalGapReading D label = (k : ℝ) := by
  have hsplit : ∀ label : Fin m,
      (1 - D.weight label) * totalGapReading D label
        = (D.atom label ⬝ᵥ ((totalGap D)⁻¹ *ᵥ D.atom label))
          - D.weight label * (D.atom label ⬝ᵥ ((totalGap D)⁻¹ *ᵥ D.atom label)) := by
    intro label
    rw [totalGapReading]
    ring
  rw [Finset.sum_congr rfl fun label _ => hsplit label, Finset.sum_sub_distrib,
    sum_reading_eq_trace_mul_total D (totalGap D)⁻¹,
    sum_weight_mul_reading_eq_trace_gen D (totalGap D)⁻¹]
  have hshift : subsetSum D Finset.univ = totalGap D + 1 := by
    rw [totalGap]; abel
  rw [hshift, Matrix.mul_add, Matrix.mul_one, Matrix.trace_add,
    Matrix.nonsing_inv_mul _ (isUnit_det_totalGap D hm), Matrix.trace_one]
  simp

-- `Gtz.sum_one_sub_weight` (Gtz/Reduction/DescentLadder.lean) already states that the
-- co-weights total `m - 1`.  It is imported, not re-derived.

/-- **THE COUNTING THEOREM.**  The labels whose co-atom set fails to dominate
strictly carry at most `k` of the co-weight, so there are at most `k + 1` of them.
The budget spends `k`, each failing label spends more than `1 - t_c`, and the
weights themselves total one. -/
theorem card_le_of_forall_one_le_totalGapReading (D : WeightedDesign m k) (hm : 2 ≤ m)
    (failing : Finset (Fin m)) (hfail : ∀ label ∈ failing, 1 ≤ totalGapReading D label) :
    (failing.card : ℝ) ≤ (k : ℝ) + 1 := by
  classical
  have hnonneg : ∀ label : Fin m, 0 ≤ (1 - D.weight label) * totalGapReading D label := by
    intro label
    exact mul_nonneg (by linarith [weight_lt_one D hm label])
      (totalGapReading_nonneg D hm label)
  have hpart : ∑ label ∈ failing, (1 - D.weight label) * totalGapReading D label
      ≤ ∑ label, (1 - D.weight label) * totalGapReading D label :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ failing)
      fun label _ _ => hnonneg label
  have hfloor : ∑ label ∈ failing, (1 - D.weight label)
      ≤ ∑ label ∈ failing, (1 - D.weight label) * totalGapReading D label := by
    refine Finset.sum_le_sum fun label hlabel => ?_
    have hco : (0 : ℝ) < 1 - D.weight label := by linarith [weight_lt_one D hm label]
    nlinarith [hfail label hlabel, hco]
  have hcard : (failing.card : ℝ) - ∑ label ∈ failing, D.weight label
      = ∑ label ∈ failing, (1 - D.weight label) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hweightLe : ∑ label ∈ failing, D.weight label ≤ 1 := by
    rw [← D.weight_sum_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ failing)
      fun label _ _ => (D.weight_pos label).le
  rw [sum_one_sub_weight_mul_totalGapReading D hm] at hpart
  linarith [hfloor, hpart, hcard, hweightLe]

/-- **SOME CO-ATOM SET DOMINATES STRICTLY**, at every design with more than
`k + 1` atoms and no hypothesis at all.  At `(6,3)` this fires on the nose: six
atoms against a ceiling of four. -/
theorem exists_posDef_gap_erase (D : WeightedDesign m k) (hm : 2 ≤ m) (hsize : k + 1 < m) :
    ∃ label : Fin m, (subsetSum D (Finset.univ.erase label) - 1).PosDef := by
  classical
  by_contra hnone
  push Not at hnone
  have hfail : ∀ label ∈ (Finset.univ : Finset (Fin m)), 1 ≤ totalGapReading D label := by
    intro label _
    exact not_lt.mp fun hlt => hnone label ((posDef_gap_erase_iff D hm label).mpr hlt)
  have hbound := card_le_of_forall_one_le_totalGapReading D hm Finset.univ hfail
  rw [Finset.card_univ, Fintype.card_fin] at hbound
  have hcast : (k : ℝ) + 1 < (m : ℝ) := by exact_mod_cast hsize
  linarith

/-- The `(6,3)` reading of the counting theorem. -/
theorem exists_posDef_gap_erase_sixThree (D : WeightedDesign 6 3) :
    ∃ label : Fin 6, (subsetSum D (Finset.univ.erase label) - 1).PosDef :=
  exists_posDef_gap_erase D (by norm_num) (by norm_num)

/-- The budget at `(6,3)`: the five readings total three against a co-weight total
of five. -/
theorem sum_totalGapReading_sixThree (D : WeightedDesign 6 3) :
    ∑ label, (1 - D.weight label) * totalGapReading D label = 3 := by
  have h := sum_one_sub_weight_mul_totalGapReading D (by norm_num)
  norm_num at h
  exact h

/-! ## Part 4 — the metric transfer

`G^{-1}` is positive definite, hence an inner product.  Cauchy-Schwarz equality in
an inner product is a statement about the two VECTORS and not about the metric, so
it transfers between the Euclidean metric and the total-gap metric unchanged. -/

/-- **CAUCHY-SCHWARZ EQUALITY IN A POSITIVE DEFINITE METRIC.**  The Gram defect of
two vectors vanishes exactly when they are dependent.  The witness is the explicit
combination `a v - b u` with `a` the first diagonal reading and `b` the cross
reading, whose own reading is `a` times the defect. -/
theorem gramDefect_eq_zero_iff {form : Matrix (Fin k) (Fin k) ℝ} (hform : form.PosDef)
    (leftVec rightVec : Fin k → ℝ) :
    (leftVec ⬝ᵥ (form *ᵥ leftVec)) * (rightVec ⬝ᵥ (form *ᵥ rightVec))
        - (leftVec ⬝ᵥ (form *ᵥ rightVec)) ^ 2 = 0
      ↔ (leftVec = 0 ∨ ∃ scale : ℝ, rightVec = scale • leftVec) := by
  have hsymm : formᵀ = form := PosDef.transpose_eq hform
  have hswap : ∀ u v : Fin k → ℝ, u ⬝ᵥ (form *ᵥ v) = v ⬝ᵥ (form *ᵥ u) := by
    intro u v
    rw [dotProduct_mulVec, ← Matrix.vecMul_transpose, hsymm, dotProduct_comm]
  have hquad : ∀ leftScale rightScale : ℝ,
      (leftScale • leftVec + rightScale • rightVec)
          ⬝ᵥ (form *ᵥ (leftScale • leftVec + rightScale • rightVec))
        = leftScale ^ 2 * (leftVec ⬝ᵥ (form *ᵥ leftVec))
          + 2 * (leftScale * rightScale) * (leftVec ⬝ᵥ (form *ᵥ rightVec))
          + rightScale ^ 2 * (rightVec ⬝ᵥ (form *ᵥ rightVec)) := by
    intro leftScale rightScale
    have hpush : form *ᵥ (leftScale • leftVec + rightScale • rightVec)
        = leftScale • (form *ᵥ leftVec) + rightScale • (form *ᵥ rightVec) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    rw [hpush]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hswap rightVec leftVec]
    ring
  constructor
  · intro hzero
    by_cases hleft : leftVec = 0
    · exact Or.inl hleft
    set diag := leftVec ⬝ᵥ (form *ᵥ leftVec) with hdiagDef
    set cross := leftVec ⬝ᵥ (form *ᵥ rightVec) with hcrossDef
    have hdiagPos : 0 < diag := by
      have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hform).2 hleft
      rwa [star_trivial] at h
    have hdiagNe : diag ≠ 0 := ne_of_gt hdiagPos
    refine Or.inr ⟨cross / diag, ?_⟩
    have hwitness := hquad (-cross) diag
    have hvalue : ((-cross) • leftVec + diag • rightVec)
        ⬝ᵥ (form *ᵥ ((-cross) • leftVec + diag • rightVec)) = 0 := by
      rw [hwitness]
      linear_combination diag * hzero
    have hnull : (-cross) • leftVec + diag • rightVec = 0 := by
      by_contra hne
      have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hform).2 hne
      rw [star_trivial, hvalue] at h
      exact lt_irrefl 0 h
    funext coord
    have hentry := congrFun hnull coord
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hentry
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith [hentry]
  · rintro (rfl | ⟨scale, rfl⟩)
    · simp
    · rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul]
      ring

/-- The Euclidean instance: the leverage defect of a pair. -/
theorem leverageDefect_eq_zero_iff (leftVec rightVec : Fin k → ℝ) :
    leverageOf leftVec * leverageOf rightVec - (leftVec ⬝ᵥ rightVec) ^ 2 = 0
      ↔ (leftVec = 0 ∨ ∃ scale : ℝ, rightVec = scale • leftVec) := by
  have hone : ∀ u v : Fin k → ℝ, u ⬝ᵥ ((1 : Matrix (Fin k) (Fin k) ℝ) *ᵥ v) = u ⬝ᵥ v := by
    intro u v; rw [Matrix.one_mulVec]
  have hlev : ∀ u : Fin k → ℝ, leverageOf u = u ⬝ᵥ u := fun u => leverageOf_eq_dotProduct u
  rw [hlev, hlev, ← hone leftVec leftVec, ← hone rightVec rightVec, ← hone leftVec rightVec]
  exact gramDefect_eq_zero_iff Matrix.PosDef.one leftVec rightVec

/-- **THE METRIC TRANSFER.**  A pair is at Cauchy-Schwarz equality in the metric of
the total gap exactly when it is at Cauchy-Schwarz equality in the Euclidean
metric.  Both say the two atoms are dependent, and the total gap has dropped out
of the statement. -/
theorem totalGapDefect_eq_zero_iff_leverageDefect_eq_zero (D : WeightedDesign m k)
    (hm : 2 ≤ m) (leftLabel rightLabel : Fin m) :
    (totalGapReading D leftLabel * totalGapReading D rightLabel
        - (D.atom leftLabel ⬝ᵥ ((totalGap D)⁻¹ *ᵥ D.atom rightLabel)) ^ 2 = 0)
      ↔ (leverageOf (D.atom leftLabel) * leverageOf (D.atom rightLabel)
        - (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2 = 0) := by
  rw [totalGapReading, totalGapReading,
    gramDefect_eq_zero_iff (posDef_totalGap_inv D hm) (D.atom leftLabel) (D.atom rightLabel),
    leverageDefect_eq_zero_iff]

/-- **A VANISHING TOTAL-GAP DEFECT IS A PARALLEL PAIR.**  Two distinct labels whose
Gram defect vanishes in the total-gap metric are a parallel pair of the design, in
the tree's own sense. -/
theorem hasParallelPair_of_totalGapDefect_eq_zero (D : WeightedDesign m k) (hm : 2 ≤ m)
    {leftLabel rightLabel : Fin m} (hdistinct : leftLabel ≠ rightLabel)
    (hdefect : totalGapReading D leftLabel * totalGapReading D rightLabel
      - (D.atom leftLabel ⬝ᵥ ((totalGap D)⁻¹ *ᵥ D.atom rightLabel)) ^ 2 = 0) :
    HasParallelPair D := by
  have htransfer :=
    (totalGapDefect_eq_zero_iff_leverageDefect_eq_zero D hm leftLabel rightLabel).mp hdefect
  rcases (leverageDefect_eq_zero_iff (D.atom leftLabel) (D.atom rightLabel)).mp htransfer with
    hzero | ⟨scale, hscale⟩
  · exact ⟨rightLabel, leftLabel, 0, Ne.symm hdistinct, by rw [hzero, zero_smul]⟩
  · exact ⟨leftLabel, rightLabel, scale, hdistinct, hscale⟩

/-- The converse: a parallel pair has a vanishing defect in the total-gap metric. -/
theorem totalGapDefect_eq_zero_of_parallel (D : WeightedDesign m k) (hm : 2 ≤ m)
    {leftLabel rightLabel : Fin m} {scale : ℝ}
    (hscale : D.atom rightLabel = scale • D.atom leftLabel) :
    totalGapReading D leftLabel * totalGapReading D rightLabel
      - (D.atom leftLabel ⬝ᵥ ((totalGap D)⁻¹ *ᵥ D.atom rightLabel)) ^ 2 = 0 := by
  rw [totalGapReading, totalGapReading]
  exact (gramDefect_eq_zero_iff (posDef_totalGap_inv D hm) (D.atom leftLabel)
    (D.atom rightLabel)).mpr (Or.inr ⟨scale, hscale⟩)

/-! ## Part 5 — the co-share pair form

The complementary quantity of a pair.  With `u_c = 1 - t_c l_c` the co-share, the
form `u_p u_q - t_p t_q p_pq^2` is the two by two determinant of the complementary
projection of the design's chart at that pair, and the campaign's pairing cap is
exactly its nonnegativity. -/

/-- The co-share of an atom. -/
noncomputable def coShareOf (D : WeightedDesign m k) (label : Fin m) : ℝ :=
  1 - D.weight label * leverageOf (D.atom label)

/-- **THE CO-SHARE PAIR FORM.** -/
noncomputable def coSharePairForm (D : WeightedDesign m k) (leftLabel rightLabel : Fin m) : ℝ :=
  coShareOf D leftLabel * coShareOf D rightLabel
    - D.weight leftLabel * D.weight rightLabel
      * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2

theorem coSharePairForm_comm (D : WeightedDesign m k) (leftLabel rightLabel : Fin m) :
    coSharePairForm D leftLabel rightLabel = coSharePairForm D rightLabel leftLabel := by
  rw [coSharePairForm, coSharePairForm, dotProduct_comm (D.atom leftLabel) (D.atom rightLabel)]
  ring

/-- **THE CO-SHARE PAIR FORM IS A TWO BY TWO DETERMINANT.**  It is the determinant
of the complementary chart block of the pair, whose diagonal carries the two
co-shares and whose off-diagonal carries the weighted pairing. -/
theorem coSharePairForm_eq_det (D : WeightedDesign m k) (leftLabel rightLabel : Fin m) :
    coSharePairForm D leftLabel rightLabel
      = (Matrix.of ![![coShareOf D leftLabel,
              -(Real.sqrt (D.weight leftLabel * D.weight rightLabel)
                * (D.atom leftLabel ⬝ᵥ D.atom rightLabel))],
            ![-(Real.sqrt (D.weight leftLabel * D.weight rightLabel)
                * (D.atom leftLabel ⬝ᵥ D.atom rightLabel)),
              coShareOf D rightLabel]] : Matrix (Fin 2) (Fin 2) ℝ).det := by
  have hroot : Real.sqrt (D.weight leftLabel * D.weight rightLabel)
      * Real.sqrt (D.weight leftLabel * D.weight rightLabel)
      = D.weight leftLabel * D.weight rightLabel :=
    Real.mul_self_sqrt (mul_nonneg (D.weight_pos leftLabel).le (D.weight_pos rightLabel).le)
  rw [Matrix.det_fin_two, coSharePairForm]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [hroot]

/-- The co-shares of a design total `m - k`. -/
theorem sum_coShareOf (D : WeightedDesign m k) :
    ∑ label, coShareOf D label = (m : ℝ) - (k : ℝ) := by
  simp only [coShareOf]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sum_weighted_leverage D]

/-! ## Part 6 — the two readings of the `(6,3)` cell together

The co-atom dichotomy and the metric transfer meet at `(6,3)`.  A tie whose five
readings are all below one has every five-set strictly dominating, which is the
one stratum the campaign's sharp duality sends to an all-heavy dual. -/

/-- **THE FIVE-SET PROFILE OF A `(6,3)` DESIGN.**  Every label is one of three
kinds, decided by one scalar. -/
theorem gap_erase_trichotomy (D : WeightedDesign m k) (hm : 2 ≤ m) (label : Fin m) :
    (subsetSum D (Finset.univ.erase label) - 1).PosDef
      ∨ ((subsetSum D (Finset.univ.erase label) - 1).PosSemidef
          ∧ (subsetSum D (Finset.univ.erase label) - 1).det = 0)
      ∨ ¬ (subsetSum D (Finset.univ.erase label) - 1).PosSemidef := by
  rcases lt_trichotomy (totalGapReading D label) 1 with hlt | heq | hgt
  · exact Or.inl ((posDef_gap_erase_iff D hm label).mpr hlt)
  · exact Or.inr (Or.inl ⟨(posSemidef_gap_erase_iff D hm label).mpr (le_of_eq heq),
      det_gap_erase_eq_zero_of_reading_eq_one D hm heq⟩)
  · exact Or.inr (Or.inr fun hpsd =>
      absurd ((posSemidef_gap_erase_iff D hm label).mp hpsd) (not_le.mpr hgt))

/-- **EVERY FIVE-SET OF A `(6,3)` DESIGN DOMINATES STRICTLY EXACTLY WHEN EVERY
READING IS BELOW ONE.**  This is the condition the sharp duality reads as
all-heaviness of the dual design. -/
theorem forall_posDef_gap_erase_iff (D : WeightedDesign m k) (hm : 2 ≤ m) :
    (∀ label : Fin m, (subsetSum D (Finset.univ.erase label) - 1).PosDef)
      ↔ ∀ label : Fin m, totalGapReading D label < 1 := by
  constructor
  · intro hall label
    exact (posDef_gap_erase_iff D hm label).mp (hall label)
  · intro hall label
    exact (posDef_gap_erase_iff D hm label).mpr (hall label)

/-- **A SINGULAR FIVE-SET IS A CORANK-ONE WEAK DOMINATOR OF SIZE FIVE.**  At
`(6,3)` the failure of the all-strict condition at a label is exactly a weak
dominator of size five that is not strict, and it carries a null direction. -/
theorem exists_null_of_gap_erase_reading_eq_one (D : WeightedDesign m k) (hm : 2 ≤ m)
    {label : Fin m} (hread : totalGapReading D label = 1) :
    ∃ probe : Fin k → ℝ, probe ≠ 0
      ∧ (subsetSum D (Finset.univ.erase label) - 1) *ᵥ probe = 0 := by
  have hdet := det_gap_erase_eq_zero_of_reading_eq_one D hm hread
  exact (Matrix.exists_mulVec_eq_zero_iff).mpr hdet

end Gtz

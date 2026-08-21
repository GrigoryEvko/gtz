/-
# The star ledger, the zero-axis frame, and the free half of cell H

Cell H of the corank-two `Z1` corner is the branch in which the four-set through
the axis-reading inside atom `z` FAILS while the four-set through `y` survives.
The landed statement of its residual, `Gtz.OneAxisZeroHeavyInsideResidual`, is a
Prop with four universally quantified clause families written in matrix inverses,
adjugate traces and an odds parameter.  This module replaces it by SIX positive
definiteness refusals on named triples, and supplies the three ledgers that price
them.

## 1. The star ledger

Fix a form `A` and read Parseval in its inverse.  For every subset `K`,

  `∑_{d ∈ K} t_d·(1 − g_d·A⁻¹g_d) = 1 − tr A⁻¹ + ∑_{c ∉ K} t_c·(g_c·A⁻¹g_c − 1)`

(`Gtz.star_ledger_weighted`).  When `A` is the gap of `K` together with one more
atom `y`, the UNWEIGHTED total is computable too,

  `∑_{d ∈ K} g_d·A⁻¹g_d = 3 + tr A⁻¹ − g_y·A⁻¹g_y`

(`Gtz.star_reading_total`), so at `K.card = 3` the unweighted star total is
`g_y·A⁻¹g_y − tr A⁻¹` (`Gtz.star_ledger_unweighted`).  The difference of the two
is the co-weighted ledger.  Either sign produces a strictly dominating triple,
because a positive total forces one summand positive and a positive downdate
determinant promotes to positive definiteness.

The weighted ledger is the one that carries the weights, which is what every lane
of this campaign discovered it needs: the obstruction degenerates linearly at a
zero weight and no strict certificate can exist.

## 2. The zero-axis frame

At a corank-two corner `S_C − 1 = lam·u uᵀ` with `g_x·u = 0` the landed inside
Gram law pins `x` completely: `|g_x|² = 1` and `g_x·g_e = 0` for the other two
inside atoms.  So `g_x` is a UNIT vector orthogonal to the corner plane, its
leverage sits exactly on the tie-necessary floor, and Parseval transfers through
it: for every probe `v`,

  `∑_{d ∉ C} t_d·(g_d·g_x)(g_d·v) = (1 − t_x)·(g_x·v)`

(`Gtz.zeroAxis_parseval_transfer`).  At `v = g_x` this is the outside mass of the
zero-axis atom.

## 3. The free half of the tie

A refusal survives a rank-one downdate, so a failed four-set poisons its whole
star: `A_z` not positive definite refuses the three triples `{z} ∪ K \ {d}` AND
the outside triple `K` itself, with nothing computed.  Ten of the twenty triples
are already refused by the landed corner census.  Hence at a cell-H corner a tie
is exactly SIX refusals — the `y`-star and the `x`-star — and
`Gtz.oneAxisZeroHeavyInsideResidual_of_starRefusals` discharges the landed
residual from them.

## 4. The adjugate separation

The same two hypotheses separate the two inside atoms in the adjugate of the
OUTSIDE gap `W := S_K − 1`, with no inverse anywhere:

  `g_z·adj(W)·g_z ≤ −det W < g_y·adj(W)·g_y`

(`Gtz.cellH_adjugate_separation`).  This is the cell-H dichotomy as a polynomial
sign, and through the landed corner adjugate contraction it prices the axis.

## 5. The corner ladder

A corner gap is positive semidefinite, so every superset of a corner dominates
weakly.  The four-set determinants vanish (landed); the FIVE-set determinants are
the adjugate reading of a corner-plus-one form and are nonnegative
(`Gtz.corner_fiveSet_gapDet_nonneg`), and a five-set is positive definite exactly
when that reading is nonzero.  At `(6,3)` a five-set is the universe less one
atom, so this is a law about erasing a single label.

[MEASURED before proving, in a chart that makes the corner exact — inside atoms
`g_x = (1,0,0)`, `g_y = (0,c,mu·sn)`, `g_z = (0,−sn,mu·c)` with `c² + sn² = 1`,
`mu > 1`, outside atoms `N^{1/2}R` scaled by the weights, Parseval residual
`3e-34` in quad precision: on 59368 cell-H inhabitants the `y`-star fires at
every one, the unweighted star total fires at 99.01 percent, the weighted at
96.78 and the co-weighted at 99.94.  The star margin has infimum ZERO over the
cell, attained only as the weight vector runs to a vertex of the simplex, so no
strict certificate exists and the ledgers are the correct instruments.]
-/
import Gtz.Wave.CellHDowndatePromotion
import Gtz.Wave.CornerRefusalCensus
import Gtz.Wave.CorankTwoNonplanarSystem
import Gtz.Wave.OneAxisZeroDowndateOdds
import Gtz.Wave.FourSetFloorPackage
import Gtz.Wave.WeightedHalfPlane
import Gtz.Design.CapSlack
import Gtz.Design.PlaneBranchComplementSelector

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The star ledger -/

/-- **THE WEIGHTED STAR LEDGER.**  Parseval read in the inverse of any form `A`
splits along any subset `K`: the weighted star total of `K` is one minus the
trace of `A⁻¹` corrected by the weighted excess readings of the complement.
Hypothesis-free beyond Parseval, and it carries the weights. -/
theorem star_ledger_weighted (D : WeightedDesign m 3) (K : Finset (Fin m))
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ d ∈ K, D.weight d * (1 - D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d))
      = 1 - Matrix.trace A⁻¹
        + ∑ c ∈ Kᶜ, D.weight c * (D.atom c ⬝ᵥ (A⁻¹ *ᵥ D.atom c) - 1) := by
  have htr : ∑ c, D.weight c * (D.atom c ⬝ᵥ (A⁻¹ *ᵥ D.atom c)) = Matrix.trace A⁻¹ :=
    sum_weight_mul_reading_eq_trace D A⁻¹
  have hsplit : ∑ d ∈ K, D.weight d * (D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d))
      + ∑ c ∈ Kᶜ, D.weight c * (D.atom c ⬝ᵥ (A⁻¹ *ᵥ D.atom c))
      = Matrix.trace A⁻¹ := by
    rw [Finset.sum_add_sum_compl]
    exact htr
  have hw : ∑ d ∈ K, D.weight d + ∑ c ∈ Kᶜ, D.weight c = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact D.weight_sum_one
  have hL : ∑ d ∈ K, D.weight d * (1 - D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d))
      = ∑ d ∈ K, D.weight d
        - ∑ d ∈ K, D.weight d * (D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  have hR : ∑ c ∈ Kᶜ, D.weight c * (D.atom c ⬝ᵥ (A⁻¹ *ᵥ D.atom c) - 1)
      = ∑ c ∈ Kᶜ, D.weight c * (D.atom c ⬝ᵥ (A⁻¹ *ᵥ D.atom c))
        - ∑ c ∈ Kᶜ, D.weight c := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hL, hR]
  linarith

/-- The gap of `insert y K` is the gap of `K` plus the atom of `y`. -/
theorem gap_insert_eq_add_atomMatrix (D : WeightedDesign m 3) {K : Finset (Fin m)}
    {y : Fin m} (hy : y ∉ K) :
    subsetSum D (insert y K) - 1 = (subsetSum D K - 1) + atomMatrix (D.atom y) := by
  rw [subsetSum, Finset.sum_insert hy, ← subsetSum]
  abel

/-- The gap of `insert y (K.erase d)` is the gap of `insert y K` less the atom
of `d`. -/
theorem gap_insert_erase_eq_sub_atomMatrix (D : WeightedDesign m 3)
    {K : Finset (Fin m)} {y d : Fin m} (hy : y ∉ K) (hd : d ∈ K) :
    subsetSum D (insert y (K.erase d)) - 1
      = (subsetSum D (insert y K) - 1) - atomMatrix (D.atom d) := by
  have hyE : y ∉ K.erase d := fun hmem => hy (Finset.mem_of_mem_erase hmem)
  have hK : subsetSum D K = subsetSum D (K.erase d) + atomMatrix (D.atom d) := by
    rw [subsetSum, subsetSum, ← Finset.sum_erase_add _ _ hd]
  rw [gap_insert_eq_add_atomMatrix D hyE, gap_insert_eq_add_atomMatrix D hy, hK]
  abel

/-- **THE UNWEIGHTED STAR TOTAL.**  When `A` is the gap of `insert y K` and is
invertible, the readings of the members of `K` in `A⁻¹` total `3 + tr A⁻¹` less
the reading of `y`.  No cardinality hypothesis. -/
theorem star_reading_total (D : WeightedDesign m 3) {K : Finset (Fin m)} {y : Fin m}
    (hy : y ∉ K) (hdet : IsUnit (subsetSum D (insert y K) - 1).det) :
    ∑ d ∈ K, D.atom d ⬝ᵥ ((subsetSum D (insert y K) - 1)⁻¹ *ᵥ D.atom d)
      = 3 + Matrix.trace (subsetSum D (insert y K) - 1)⁻¹
        - D.atom y ⬝ᵥ ((subsetSum D (insert y K) - 1)⁻¹ *ᵥ D.atom y) := by
  set A := subsetSum D (insert y K) - 1 with hAdef
  have hK : subsetSum D K = A + 1 - atomMatrix (D.atom y) := by
    rw [hAdef, gap_insert_eq_add_atomMatrix D hy]
    abel
  have hsum : ∑ d ∈ K, D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d)
      = Matrix.trace (A⁻¹ * subsetSum D K) := by
    rw [subsetSum, Matrix.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun d _ =>
      dotProduct_mulVec_eq_trace_mul_atomMatrix A⁻¹ (D.atom d)
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdet
  have hy' : Matrix.trace (A⁻¹ * atomMatrix (D.atom y))
      = D.atom y ⬝ᵥ (A⁻¹ *ᵥ D.atom y) :=
    (dotProduct_mulVec_eq_trace_mul_atomMatrix A⁻¹ (D.atom y)).symm
  rw [hsum, hK, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, hinv,
    Matrix.trace_sub, Matrix.trace_add, hy']
  have hone : Matrix.trace (1 : Matrix (Fin 3) (Fin 3) ℝ) = 3 := by
    simp [Matrix.trace_one]
  rw [hone]

/-- **THE UNWEIGHTED STAR LEDGER at a triple.**  For `K.card = 3` the star total
of `K` in the gap of `insert y K` is the reading of `y` less the trace. -/
theorem star_ledger_unweighted (D : WeightedDesign m 3) {K : Finset (Fin m)}
    (hcard : K.card = 3) {y : Fin m} (hy : y ∉ K)
    (hdet : IsUnit (subsetSum D (insert y K) - 1).det) :
    ∑ d ∈ K, (1 - D.atom d ⬝ᵥ ((subsetSum D (insert y K) - 1)⁻¹ *ᵥ D.atom d))
      = D.atom y ⬝ᵥ ((subsetSum D (insert y K) - 1)⁻¹ *ᵥ D.atom y)
        - Matrix.trace (subsetSum D (insert y K) - 1)⁻¹ := by
  have htotal := star_reading_total D hy hdet
  have hsplit : ∑ d ∈ K,
        (1 - D.atom d ⬝ᵥ ((subsetSum D (insert y K) - 1)⁻¹ *ᵥ D.atom d))
      = (K.card : ℝ)
        - ∑ d ∈ K, D.atom d ⬝ᵥ ((subsetSum D (insert y K) - 1)⁻¹ *ᵥ D.atom d) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsplit, hcard, htotal]
  push_cast
  ring

/-! ## 2. Producers from the ledger -/

/-- A positive weighted star total forces one member of the star to read the
inverse strictly below one. -/
theorem exists_reading_lt_one_of_weighted_total_pos (D : WeightedDesign m 3)
    {K : Finset (Fin m)} {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hpos : 0 < ∑ d ∈ K, D.weight d * (1 - D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d))) :
    ∃ d ∈ K, D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d) < 1 := by
  by_contra hcon
  push_neg at hcon
  have hnonpos : ∑ d ∈ K, D.weight d * (1 - D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d)) ≤ 0 := by
    refine Finset.sum_nonpos fun d hd => ?_
    have h1 : 1 ≤ D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d) := hcon d hd
    nlinarith [D.weight_pos d]
  linarith

/-- A positive unweighted star total forces the same conclusion. -/
theorem exists_reading_lt_one_of_total_pos (D : WeightedDesign m 3)
    {K : Finset (Fin m)} {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hpos : 0 < ∑ d ∈ K, (1 - D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d))) :
    ∃ d ∈ K, D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d) < 1 := by
  by_contra hcon
  push_neg at hcon
  have hnonpos : ∑ d ∈ K, (1 - D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d)) ≤ 0 :=
    Finset.sum_nonpos fun d hd => by linarith [hcon d hd]
  linarith

/-- **THE STAR PRODUCER.**  A member of the star that reads the inverse below one
gives a strictly dominating triple: the downdate determinant is positive and a
positive determinant promotes a downdate of a positive definite form. -/
theorem star_posDef_of_reading_lt_one (D : WeightedDesign m 3)
    {K : Finset (Fin m)} {y d : Fin m} (hy : y ∉ K) (hd : d ∈ K)
    (hPD : (subsetSum D (insert y K) - 1).PosDef)
    (hread : D.atom d ⬝ᵥ ((subsetSum D (insert y K) - 1)⁻¹ *ᵥ D.atom d) < 1) :
    (subsetSum D (insert y (K.erase d)) - 1).PosDef := by
  set A := subsetSum D (insert y K) - 1 with hAdef
  have hdet : IsUnit A.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (Matrix.PosDef.det_pos hPD))
  have hdown : (A - atomMatrix (D.atom d)).det
      = A.det * (1 - D.atom d ⬝ᵥ (A⁻¹ *ᵥ D.atom d)) := det_sub_atomMatrix hdet (D.atom d)
  have hpos : 0 < (A - atomMatrix (D.atom d)).det := by
    rw [hdown]
    have := hPD.det_pos
    nlinarith
  rw [gap_insert_erase_eq_sub_atomMatrix D hy hd]
  exact posDef_sub_atomMatrix_of_det_pos hPD hpos

/-- **THE WEIGHTED LEDGER KILL.**  If the weighted excess of the complement
outruns the trace deficit, the star of `y` carries a strictly dominating
triple. -/
theorem exists_star_posDef_of_weighted_ledger (D : WeightedDesign m 3)
    {K : Finset (Fin m)} {y : Fin m} (hy : y ∉ K)
    (hPD : (subsetSum D (insert y K) - 1).PosDef)
    (hpos : 0 < 1 - Matrix.trace (subsetSum D (insert y K) - 1)⁻¹
      + ∑ c ∈ Kᶜ, D.weight c
          * (D.atom c ⬝ᵥ ((subsetSum D (insert y K) - 1)⁻¹ *ᵥ D.atom c) - 1)) :
    ∃ d ∈ K, (subsetSum D (insert y (K.erase d)) - 1).PosDef := by
  have hledger := star_ledger_weighted D K (subsetSum D (insert y K) - 1)
  have htotal : 0 < ∑ d ∈ K, D.weight d
      * (1 - D.atom d ⬝ᵥ ((subsetSum D (insert y K) - 1)⁻¹ *ᵥ D.atom d)) := by
    rw [hledger]
    exact hpos
  obtain ⟨d, hd, hread⟩ := exists_reading_lt_one_of_weighted_total_pos D htotal
  exact ⟨d, hd, star_posDef_of_reading_lt_one D hy hd hPD hread⟩

/-- **THE UNWEIGHTED LEDGER KILL.**  If the anchor `y` reads its own gap above
the trace of the inverse, the star of `y` carries a strictly dominating
triple. -/
theorem exists_star_posDef_of_unweighted_ledger (D : WeightedDesign m 3)
    {K : Finset (Fin m)} (hcard : K.card = 3) {y : Fin m} (hy : y ∉ K)
    (hPD : (subsetSum D (insert y K) - 1).PosDef)
    (hgt : Matrix.trace (subsetSum D (insert y K) - 1)⁻¹
      < D.atom y ⬝ᵥ ((subsetSum D (insert y K) - 1)⁻¹ *ᵥ D.atom y)) :
    ∃ d ∈ K, (subsetSum D (insert y (K.erase d)) - 1).PosDef := by
  have hledger := star_ledger_unweighted D hcard hy
    (isUnit_iff_ne_zero.mpr (ne_of_gt (Matrix.PosDef.det_pos hPD)))
  have htotal : 0 < ∑ d ∈ K,
      (1 - D.atom d ⬝ᵥ ((subsetSum D (insert y K) - 1)⁻¹ *ᵥ D.atom d)) := by
    rw [hledger]
    linarith
  obtain ⟨d, hd, hread⟩ := exists_reading_lt_one_of_total_pos D htotal
  exact ⟨d, hd, star_posDef_of_reading_lt_one D hy hd hPD hread⟩

/-! ## 3. The zero-axis frame -/

/-- **THE ZERO-AXIS ATOM IS A UNIT VECTOR.**  An inside atom of a corank-two
corner that reads the axis at zero has leverage exactly one — the tie-necessary
leverage floor, saturated. -/
theorem zeroAxis_leverage_eq_one (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x : Fin m} (hx : x ∈ C) (hax : D.atom x ⬝ᵥ u = 0) :
    D.atom x ⬝ᵥ D.atom x = 1 := by
  have h := insideGram_self_of_rankOneGap D C hcard hlam hunit hgap hx
  rw [hax] at h
  have hpos : (0 : ℝ) < 1 + lam := by linarith
  nlinarith [h]

/-- **THE ZERO-AXIS ATOM IS ORTHOGONAL TO THE CORNER PLANE.**  It is orthogonal
to every other inside atom. -/
theorem zeroAxis_orthogonal (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x e : Fin m} (hx : x ∈ C) (he : e ∈ C) (hxe : x ≠ e)
    (hax : D.atom x ⬝ᵥ u = 0) :
    D.atom x ⬝ᵥ D.atom e = 0 := by
  have h := insideGram_offDiag_of_rankOneGap D C hcard hlam hunit hgap hx he hxe
  rw [hax] at h
  have hpos : (0 : ℝ) < 1 + lam := by linarith
  nlinarith [h]

/-- **PARSEVAL TRANSFERS THROUGH THE ZERO-AXIS ATOM.**  Because `g_x` is a unit
vector orthogonal to the other two inside atoms, the whole inside contribution to
the Parseval pairing at `(g_x, v)` is the single term `t_x·(g_x·v)`.  What is
left is an identity on the OUTSIDE atoms alone. -/
theorem zeroAxis_parseval_transfer (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x : Fin m} (hx : x ∈ C) (hax : D.atom x ⬝ᵥ u = 0) (v : Fin 3 → ℝ) :
    ∑ d ∈ Cᶜ, D.weight d * ((D.atom d ⬝ᵥ D.atom x) * (D.atom d ⬝ᵥ v))
      = (1 - D.weight x) * (D.atom x ⬝ᵥ v) := by
  have hall : D.atom x ⬝ᵥ v
      = ∑ c, D.weight c * (D.atom c ⬝ᵥ D.atom x) * (D.atom c ⬝ᵥ v) :=
    dotProduct_eq_sum_weight_mul_dotProduct D (D.atom x) v
  have hinside : ∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ D.atom x) * (D.atom c ⬝ᵥ v)
      = D.weight x * (D.atom x ⬝ᵥ v) := by
    rw [← Finset.sum_erase_add _ _ hx]
    have hzero : ∑ c ∈ C.erase x,
        D.weight c * (D.atom c ⬝ᵥ D.atom x) * (D.atom c ⬝ᵥ v) = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      have hcC : c ∈ C := Finset.mem_of_mem_erase hc
      have hne : x ≠ c := fun h => (Finset.ne_of_mem_erase hc) h.symm
      have h0 : D.atom c ⬝ᵥ D.atom x = 0 := by
        rw [dotProduct_comm]
        exact zeroAxis_orthogonal D C hcard hlam hunit hgap hx hcC hne hax
      rw [h0]
      ring
    have hself : D.atom x ⬝ᵥ D.atom x = 1 :=
      zeroAxis_leverage_eq_one D C hcard hlam hunit hgap hx hax
    rw [hzero, hself]
    ring
  have hsplitAll : ∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ D.atom x) * (D.atom c ⬝ᵥ v)
      + ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ D.atom x) * (D.atom d ⬝ᵥ v)
      = ∑ c, D.weight c * (D.atom c ⬝ᵥ D.atom x) * (D.atom c ⬝ᵥ v) :=
    Finset.sum_add_sum_compl C _
  have hout : ∑ d ∈ Cᶜ, D.weight d * ((D.atom d ⬝ᵥ D.atom x) * (D.atom d ⬝ᵥ v))
      = ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ D.atom x) * (D.atom d ⬝ᵥ v) :=
    Finset.sum_congr rfl fun d _ => by ring
  rw [hout]
  rw [hinside] at hsplitAll
  linarith [hall, hsplitAll]

/-- **THE OUTSIDE MASS OF THE ZERO-AXIS ATOM.**  The `v = g_x` instance. -/
theorem zeroAxis_outside_mass (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x : Fin m} (hx : x ∈ C) (hax : D.atom x ⬝ᵥ u = 0) :
    ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ D.atom x) ^ 2 = 1 - D.weight x := by
  have h := zeroAxis_parseval_transfer D C hcard hlam hunit hgap hx hax (D.atom x)
  have hself : D.atom x ⬝ᵥ D.atom x = 1 :=
    zeroAxis_leverage_eq_one D C hcard hlam hunit hgap hx hax
  rw [hself, mul_one] at h
  rw [← h]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- **THE ZERO-AXIS ATOM IS BLIND TO THE AXIS IN THE OUTSIDE MASS.**  The
`v = u` instance: the outside atoms pair the zero-axis atom against the axis at
exactly zero. -/
theorem zeroAxis_outside_axis_cross (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x : Fin m} (hx : x ∈ C) (hax : D.atom x ⬝ᵥ u = 0) :
    ∑ d ∈ Cᶜ, D.weight d * ((D.atom d ⬝ᵥ D.atom x) * (D.atom d ⬝ᵥ u)) = 0 := by
  have h := zeroAxis_parseval_transfer D C hcard hlam hunit hgap hx hax u
  rw [hax, mul_zero] at h
  exact h

/-! ## 4. A refusal poisons its whole star -/

/-- **A FAILED FOUR-SET REFUSES ITS OWN STAR.**  Every triple obtained from a
failed four-set by dropping one member fails too, because a rank-one downdate
cannot repair a refusal.  Nothing is computed. -/
theorem star_not_posDef_of_fourSet_not_posDef (D : WeightedDesign m 3)
    {K : Finset (Fin m)} {z : Fin m} (hz : z ∉ K)
    (hfail : ¬ (subsetSum D (insert z K) - 1).PosDef) {d : Fin m} (hd : d ∈ K) :
    ¬ (subsetSum D (insert z (K.erase d)) - 1).PosDef := by
  rw [gap_insert_erase_eq_sub_atomMatrix D hz hd]
  exact not_posDef_sub_vecMulVec_of_not_posDef hfail (D.atom d)

/-- **A FAILED FOUR-SET REFUSES ITS OWN CORE.**  The subset itself fails. -/
theorem core_not_posDef_of_fourSet_not_posDef (D : WeightedDesign m 3)
    {K : Finset (Fin m)} {z : Fin m} (hz : z ∉ K)
    (hfail : ¬ (subsetSum D (insert z K) - 1).PosDef) :
    ¬ (subsetSum D K - 1).PosDef := by
  have hsub : subsetSum D K - 1
      = (subsetSum D (insert z K) - 1) - atomMatrix (D.atom z) := by
    rw [gap_insert_eq_add_atomMatrix D hz]
    abel
  rw [hsub]
  exact not_posDef_sub_vecMulVec_of_not_posDef hfail (D.atom z)

/-! ## 5. The adjugate separation of the two inside atoms -/

/-- **THE FAILED FOUR-SET HAS NONPOSITIVE DETERMINANT.**  If the four-set through
`z` fails while the four-set through `y` survives, the failed one is singular or
worse: its own determinant is nonpositive, because adding the atom of `y` to it
gives a positive definite form. -/
theorem fourSet_det_nonpos_of_sibling_posDef (D : WeightedDesign m 3)
    {K : Finset (Fin m)} {y z : Fin m} (hy : y ∉ K) (hz : z ∉ K)
    (hAy : (subsetSum D (insert y K) - 1).PosDef)
    (hAz : ¬ (subsetSum D (insert z K) - 1).PosDef) :
    (subsetSum D (insert z K) - 1).det ≤ 0 := by
  refine det_nonpos_of_not_posDef_of_add_atomMatrix_posDef (p := D.atom y) ?_ hAz
  have hsum : (subsetSum D (insert z K) - 1) + atomMatrix (D.atom y)
      = (subsetSum D (insert y K) - 1) + atomMatrix (D.atom z) := by
    rw [gap_insert_eq_add_atomMatrix D hy, gap_insert_eq_add_atomMatrix D hz]
    abel
  rw [hsum]
  exact hAy.add_posSemidef (posSemidef_atomMatrix (D.atom z))

/-- **THE ADJUGATE SEPARATION.**  At a cell-H four-set pair the two inside atoms
are separated in the adjugate of the OUTSIDE gap `W := S_K − 1`, with no inverse
and no chart:

  `g_z·adj(W)·g_z ≤ −det W < g_y·adj(W)·g_y`.

Both sides are polynomials in the atoms. -/
theorem cellH_adjugate_separation (D : WeightedDesign m 3)
    {K : Finset (Fin m)} {y z : Fin m} (hy : y ∉ K) (hz : z ∉ K)
    (hAy : (subsetSum D (insert y K) - 1).PosDef)
    (hAz : ¬ (subsetSum D (insert z K) - 1).PosDef) :
    D.atom z ⬝ᵥ ((subsetSum D K - 1).adjugate *ᵥ D.atom z)
        ≤ -(subsetSum D K - 1).det
      ∧ -(subsetSum D K - 1).det
        < D.atom y ⬝ᵥ ((subsetSum D K - 1).adjugate *ᵥ D.atom y) := by
  have hy' : (subsetSum D (insert y K) - 1).det
      = (subsetSum D K - 1).det
        + D.atom y ⬝ᵥ ((subsetSum D K - 1).adjugate *ᵥ D.atom y) := by
    rw [gap_insert_eq_add_atomMatrix D hy]
    exact det_add_atomMatrix_fin_three (subsetSum D K - 1) (D.atom y)
  have hz' : (subsetSum D (insert z K) - 1).det
      = (subsetSum D K - 1).det
        + D.atom z ⬝ᵥ ((subsetSum D K - 1).adjugate *ᵥ D.atom z) := by
    rw [gap_insert_eq_add_atomMatrix D hz]
    exact det_add_atomMatrix_fin_three (subsetSum D K - 1) (D.atom z)
  have hypos : 0 < (subsetSum D (insert y K) - 1).det := hAy.det_pos
  have hznon : (subsetSum D (insert z K) - 1).det ≤ 0 :=
    fourSet_det_nonpos_of_sibling_posDef D hy hz hAy hAz
  constructor
  · rw [hz'] at hznon
    linarith
  · rw [hy'] at hypos
    linarith

/-- **THE STRICT ORDER OF THE TWO INSIDE ATOMS.**  A corollary of the separation:
the surviving atom reads the outside adjugate strictly above the failed one. -/
theorem cellH_adjugate_strict_order (D : WeightedDesign m 3)
    {K : Finset (Fin m)} {y z : Fin m} (hy : y ∉ K) (hz : z ∉ K)
    (hAy : (subsetSum D (insert y K) - 1).PosDef)
    (hAz : ¬ (subsetSum D (insert z K) - 1).PosDef) :
    D.atom z ⬝ᵥ ((subsetSum D K - 1).adjugate *ᵥ D.atom z)
      < D.atom y ⬝ᵥ ((subsetSum D K - 1).adjugate *ᵥ D.atom y) := by
  obtain ⟨h1, h2⟩ := cellH_adjugate_separation D hy hz hAy hAz
  linarith

/-! ## 6. The corner ladder -/

/-- A corner gap is positive semidefinite. -/
theorem corner_gap_posSemidef (D : WeightedDesign m 3) {C : Finset (Fin m)}
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    (subsetSum D C - 1).PosSemidef := by
  rw [hgap]
  exact (posSemidef_atomMatrix u).smul hlam

/-- **EVERY SUPERSET OF A CORNER DOMINATES WEAKLY.** -/
theorem corner_superset_gap_posSemidef (D : WeightedDesign m 3)
    {C T : Finset (Fin m)} (hsub : C ⊆ T) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    (subsetSum D T - 1).PosSemidef := by
  have hsplit : subsetSum D T - 1
      = (subsetSum D C - 1) + ∑ c ∈ T \ C, atomMatrix (D.atom c) := by
    rw [subsetSum, subsetSum, ← Finset.sum_sdiff hsub]
    abel
  rw [hsplit]
  refine (corner_gap_posSemidef D hlam hgap).add ?_
  exact Finset.sum_induction _ Matrix.PosSemidef (fun _ _ ha hb => ha.add hb)
    (Matrix.PosSemidef.zero) (fun c _ => posSemidef_atomMatrix (D.atom c))

/-- **THE FIVE-SET DETERMINANT AT A CORNER.**  Adjoining two labels to a corner
leaves a determinant that is the adjugate reading of the corner-plus-one form.
The four-set determinant vanishes, so this is the first determinant a corner can
carry. -/
theorem corner_fiveSet_gapDet_eq_adjugate_reading (D : WeightedDesign m 3)
    {C : Finset (Fin m)} {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {d e : Fin m} (hd : d ∉ C) (he : e ∉ insert d C) :
    (subsetSum D (insert e (insert d C)) - 1).det
      = D.atom e ⬝ᵥ
          ((lam • atomMatrix u + atomMatrix (D.atom d)).adjugate *ᵥ D.atom e) := by
  have hstep : subsetSum D (insert e (insert d C)) - 1
      = (lam • atomMatrix u + atomMatrix (D.atom d)) + atomMatrix (D.atom e) := by
    rw [gap_insert_eq_add_atomMatrix D he, gap_insert_eq_add_atomMatrix D hd, hgap]
  rw [hstep, det_add_atomMatrix_fin_three,
    det_smul_atomMatrix_add_atomMatrix lam u (D.atom d)]
  ring

/-- **THE FIVE-SET DETERMINANT AT A CORNER IS NONNEGATIVE.**  The five-set gap is
positive semidefinite, so its determinant cannot be negative.  At `(6,3)` a
five-set is the universe less one label. -/
theorem corner_fiveSet_gapDet_nonneg (D : WeightedDesign m 3)
    {C : Finset (Fin m)} {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) (d e : Fin m) :
    0 ≤ (subsetSum D (insert e (insert d C)) - 1).det := by
  have hsub : C ⊆ insert e (insert d C) :=
    (Finset.subset_insert d C).trans (Finset.subset_insert e _)
  exact (corner_superset_gap_posSemidef D hsub hlam hgap).det_nonneg

/-- **A FIVE-SET AT A CORNER DOMINATES STRICTLY EXACTLY WHEN ITS DETERMINANT IS
NONZERO.**  Positive semidefinite plus a nonzero determinant is positive
definite. -/
theorem corner_fiveSet_posDef_of_det_ne_zero (D : WeightedDesign m 3)
    {C : Finset (Fin m)} {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) {d e : Fin m}
    (hne : (subsetSum D (insert e (insert d C)) - 1).det ≠ 0) :
    (subsetSum D (insert e (insert d C)) - 1).PosDef := by
  have hsub : C ⊆ insert e (insert d C) :=
    (Finset.subset_insert d C).trans (Finset.subset_insert e _)
  have hpsd := corner_superset_gap_posSemidef D hsub hlam hgap
  exact hpsd.posDef_iff_det_ne_zero.mpr hne

/-! ## 7. The star aggregate in corner currency -/

/-- **THE CORNER READS ANY INVERSE.**  The three inside atoms of a corank-two
corner total, in the inverse of any form, the trace plus `lam` times the axis
reading.  This is the corner equation transported into an arbitrary metric. -/
theorem corner_inverse_reading_total (D : WeightedDesign m 3) {C : Finset (Fin m)}
    {lam : ℝ} {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ c ∈ C, D.atom c ⬝ᵥ (A⁻¹ *ᵥ D.atom c)
      = Matrix.trace A⁻¹ + lam * (u ⬝ᵥ (A⁻¹ *ᵥ u)) := by
  have hC : subsetSum D C = 1 + lam • atomMatrix u := by
    rw [← hgap]; abel
  have hsum : ∑ c ∈ C, D.atom c ⬝ᵥ (A⁻¹ *ᵥ D.atom c)
      = Matrix.trace (A⁻¹ * subsetSum D C) := by
    rw [subsetSum, Matrix.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun c _ =>
      dotProduct_mulVec_eq_trace_mul_atomMatrix A⁻¹ (D.atom c)
  have hu : Matrix.trace (A⁻¹ * atomMatrix u) = u ⬝ᵥ (A⁻¹ *ᵥ u) :=
    (dotProduct_mulVec_eq_trace_mul_atomMatrix A⁻¹ u).symm
  rw [hsum, hC, Matrix.mul_add, Matrix.mul_one, Matrix.trace_add,
    Matrix.mul_smul, Matrix.trace_smul, hu, smul_eq_mul]

/-- **THE STAR AGGREGATE IN CORNER CURRENCY.**  At a corner, the unweighted star
total of the complement in the gap of `insert y Cᶜ` is the axis reading of that
gap, weighted by `lam`, less the readings of the two OTHER inside atoms.  The
anchor `y` has disappeared: the whole aggregate is priced by the axis and by the
two atoms that are not the anchor. -/
theorem star_aggregate_corner_form (D : WeightedDesign m 3) {C : Finset (Fin m)}
    (hC : C.card = 3) (hcompl : (Cᶜ : Finset (Fin m)).card = 3)
    {lam : ℝ} {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {y : Fin m} (hy : y ∈ C)
    (hdet : IsUnit (subsetSum D (insert y (Cᶜ : Finset (Fin m))) - 1).det) :
    ∑ d ∈ (Cᶜ : Finset (Fin m)),
        (1 - D.atom d ⬝ᵥ
          ((subsetSum D (insert y (Cᶜ : Finset (Fin m))) - 1)⁻¹ *ᵥ D.atom d))
      = lam * (u ⬝ᵥ ((subsetSum D (insert y (Cᶜ : Finset (Fin m))) - 1)⁻¹ *ᵥ u))
        - ∑ c ∈ C.erase y, D.atom c ⬝ᵥ
            ((subsetSum D (insert y (Cᶜ : Finset (Fin m))) - 1)⁻¹ *ᵥ D.atom c) := by
  set A := subsetSum D (insert y (Cᶜ : Finset (Fin m))) - 1 with hAdef
  have hyc : y ∉ (Cᶜ : Finset (Fin m)) := by
    simp only [Finset.mem_compl, not_not]
    exact hy
  have hled := star_ledger_unweighted D hcompl hyc hdet
  have hcorner := corner_inverse_reading_total D hgap A
  have hsplit : ∑ c ∈ C.erase y, D.atom c ⬝ᵥ (A⁻¹ *ᵥ D.atom c)
      + D.atom y ⬝ᵥ (A⁻¹ *ᵥ D.atom y)
      = ∑ c ∈ C, D.atom c ⬝ᵥ (A⁻¹ *ᵥ D.atom c) :=
    Finset.sum_erase_add _ _ hy
  rw [hled]
  rw [hcorner] at hsplit
  linarith

/-- **THE AXIS PRODUCER.**  If the axis outreads the two non-anchor inside atoms
in the gap of `insert y Cᶜ`, the star of `y` carries a strictly dominating
triple.  Scale free, and with the promotion to positive definiteness built in. -/
theorem exists_star_posDef_of_axis_reading_gt (D : WeightedDesign m 3)
    {C : Finset (Fin m)} (hC : C.card = 3)
    (hcompl : (Cᶜ : Finset (Fin m)).card = 3)
    {lam : ℝ} {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {y : Fin m} (hy : y ∈ C)
    (hPD : (subsetSum D (insert y (Cᶜ : Finset (Fin m))) - 1).PosDef)
    (hgt : ∑ c ∈ C.erase y, D.atom c ⬝ᵥ
          ((subsetSum D (insert y (Cᶜ : Finset (Fin m))) - 1)⁻¹ *ᵥ D.atom c)
        < lam * (u ⬝ᵥ
          ((subsetSum D (insert y (Cᶜ : Finset (Fin m))) - 1)⁻¹ *ᵥ u))) :
    ∃ d ∈ (Cᶜ : Finset (Fin m)),
      (subsetSum D (insert y ((Cᶜ : Finset (Fin m)).erase d)) - 1).PosDef := by
  have hyc : y ∉ (Cᶜ : Finset (Fin m)) := by
    simp only [Finset.mem_compl, not_not]
    exact hy
  have hdet : IsUnit (subsetSum D (insert y (Cᶜ : Finset (Fin m))) - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (Matrix.PosDef.det_pos hPD))
  have hagg := star_aggregate_corner_form D hC hcompl hgap hy hdet
  have htotal : 0 < ∑ d ∈ (Cᶜ : Finset (Fin m)),
      (1 - D.atom d ⬝ᵥ
        ((subsetSum D (insert y (Cᶜ : Finset (Fin m))) - 1)⁻¹ *ᵥ D.atom d)) := by
    rw [hagg]
    linarith
  obtain ⟨d, hd, hread⟩ := exists_reading_lt_one_of_total_pos D htotal
  exact ⟨d, hd, star_posDef_of_reading_lt_one D hyc hd hPD hread⟩

/-! ## 8. The refusals of a star, in determinant currency -/

/-- **A STAR REFUSES EXACTLY WHEN ITS DOWNDATE DETERMINANTS ARE NONPOSITIVE.**
At a positive definite four-set the two vocabularies agree. -/
theorem star_refusals_iff_downdate_det_nonpos (D : WeightedDesign m 3)
    {K : Finset (Fin m)} {y : Fin m} (hy : y ∉ K)
    (hPD : (subsetSum D (insert y K) - 1).PosDef) :
    (∀ d ∈ K, ¬ (subsetSum D (insert y (K.erase d)) - 1).PosDef)
      ↔ (∀ d ∈ K,
        ((subsetSum D (insert y K) - 1) - atomMatrix (D.atom d)).det ≤ 0) := by
  constructor
  · intro href d hd
    by_contra hcon
    push_neg at hcon
    refine href d hd ?_
    rw [gap_insert_erase_eq_sub_atomMatrix D hy hd]
    exact posDef_sub_atomMatrix_of_det_pos hPD hcon
  · intro hdet d hd hPDd
    have hd' : ((subsetSum D (insert y K) - 1) - atomMatrix (D.atom d)).det ≤ 0 :=
      hdet d hd
    rw [gap_insert_erase_eq_sub_atomMatrix D hy hd] at hPDd
    exact absurd (Matrix.PosDef.det_pos hPDd) (not_lt.mpr hd')

/-! ## 9. Cell H at `(6,3)`: the tie is six refusals -/

/-- A triple built from one inside atom and two outside atoms has three
members. -/
theorem oneInside_triple_card {C : Finset (Fin m)}
    (hcompl : (Cᶜ : Finset (Fin m)).card = 3) {e d : Fin m} (he : e ∈ C)
    (hd : d ∈ (Cᶜ : Finset (Fin m))) :
    (insert e ((Cᶜ : Finset (Fin m)).erase d)).card = 3 := by
  have hnot : e ∉ (Cᶜ : Finset (Fin m)).erase d := fun hmem =>
    (Finset.mem_compl.mp (Finset.mem_of_mem_erase hmem)) he
  rw [Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem hd, hcompl]

/-- A triple built from one inside atom and two outside atoms meets the corner in
at most one label. -/
theorem oneInside_triple_inter_card {C : Finset (Fin m)} {e d : Fin m} (he : e ∈ C) :
    ((insert e ((Cᶜ : Finset (Fin m)).erase d)) ∩ C).card ≤ 1 := by
  have hsub : (insert e ((Cᶜ : Finset (Fin m)).erase d)) ∩ C ⊆ {e} := by
    intro a ha
    rcases Finset.mem_inter.mp ha with ⟨hain, haC⟩
    rcases Finset.mem_insert.mp hain with rfl | hae
    · exact Finset.mem_singleton_self a
    · exact absurd haC (Finset.mem_compl.mp (Finset.mem_of_mem_erase hae))
  calc ((insert e ((Cᶜ : Finset (Fin m)).erase d)) ∩ C).card
      ≤ ({e} : Finset (Fin m)).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton e

/-- **THE TIE REFUSES EVERY ONE-INSIDE TRIPLE.**  At a corner, a tie refuses
every triple made of one inside atom and two outside atoms. -/
theorem isTie_oneInside_not_posDef (D : WeightedDesign m 3) {C : Finset (Fin m)}
    (hC : C.card = 3) (hcompl : (Cᶜ : Finset (Fin m)).card = 3)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) (htie : IsTie D)
    {e d : Fin m} (he : e ∈ C) (hd : d ∈ (Cᶜ : Finset (Fin m))) :
    ¬ (subsetSum D (insert e ((Cᶜ : Finset (Fin m)).erase d)) - 1).PosDef := by
  refine (isTie_iff_corner_refusals D C hC hlam hgap).mp htie _
    (oneInside_triple_card hcompl he hd) (oneInside_triple_inter_card he)

/-- **THE `Z1` CELL-H STAR SYSTEM.**  Six positive definiteness refusals: the
star of the surviving inside atom `y` and the star of the zero-axis atom `x`.
Nothing else is asked, and neither an inverse nor an odds parameter occurs. -/
def CellHStarRefusalSystem : Prop :=
  ∀ (D : WeightedDesign 6 3) (x y z : Fin 6), x ≠ y → x ≠ z → y ≠ z →
    ∀ lam : ℝ, 0 < lam → ∀ u : Fin 3 → ℝ, u ⬝ᵥ u = 1 →
    subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u →
    D.atom x ⬝ᵥ u = 0 → D.atom y ⬝ᵥ u ≠ 0 → D.atom z ⬝ᵥ u ≠ 0 →
    ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef →
    (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      ¬ (subsetSum D
          (insert y ((({x, y, z} : Finset (Fin 6))ᶜ).erase d)) - 1).PosDef) →
    (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      ¬ (subsetSum D
          (insert x ((({x, y, z} : Finset (Fin 6))ᶜ).erase d)) - 1).PosDef) →
    False

/-- The corner triple of a `Z1` cell has three labels. -/
theorem cornerTriple_card {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : ({x, y, z} : Finset (Fin 6)).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
    Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]

/-- The complement of a corner triple in `Fin 6` has three labels. -/
theorem cornerTriple_compl_card {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : ((({x, y, z} : Finset (Fin 6))ᶜ) : Finset (Fin 6)).card = 3 := by
  rw [Finset.card_compl, cornerTriple_card hxy hxz hyz]
  simp

/-- **THE CELL-H RESIDUAL IS SIX REFUSALS.**  The landed
`Gtz.OneAxisZeroHeavyInsideResidual` — four universally quantified clause
families in matrix inverses, adjugate traces and an odds parameter — follows from
the six star refusals.  The four clause families rebuild the tie through the
landed downdate-odds equivalence, the corner census refuses ten of the twenty
triples for free, the failed four-set through `z` refuses its own star and its
own core for free, and what is left is exactly the two stars. -/
theorem oneAxisZeroHeavyInsideResidual_of_starRefusals :
    CellHStarRefusalSystem → OneAxisZeroHeavyInsideResidual := by
  intro hsys D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz hnotz
    hfloors hodds hdown htrace
  have hC : ({x, y, z} : Finset (Fin 6)).card = 3 := cornerTriple_card hxy hxz hyz
  have hcompl : ((({x, y, z} : Finset (Fin 6))ᶜ) : Finset (Fin 6)).card = 3 :=
    cornerTriple_compl_card hxy hxz hyz
  have htie : IsTie D :=
    (corner_oneAxisZero_heavyInside_isTie_iff_downdateOdds D hxy hxz hyz hlam
      hunit hgap hax haz hnotz).mpr ⟨hfloors, hodds, hdown, htrace⟩
  have hyC : y ∈ ({x, y, z} : Finset (Fin 6)) := by simp
  have hxC : x ∈ ({x, y, z} : Finset (Fin 6)) := by simp
  exact hsys D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz hnotz
    (fun d hd =>
      isTie_oneInside_not_posDef D hC hcompl hlam.le hgap htie hyC hd)
    (fun d hd =>
      isTie_oneInside_not_posDef D hC hcompl hlam.le hgap htie hxC hd)

/-- **THE FREE HALF OF THE CELL-H TIE.**  At a `Z1` cell-H corner the four
refusals that involve the failed inside atom `z` — the outside triple itself and
the three triples `{z} ∪ Cᶜ \ {d}` — hold with nothing computed, because a
refusal survives a rank-one downdate. -/
theorem cellH_zSide_refusals_free (D : WeightedDesign m 3) {C : Finset (Fin m)}
    {z : Fin m} (hz : z ∈ C)
    (hnotz : ¬ (subsetSum D (insert z (Cᶜ : Finset (Fin m))) - 1).PosDef) :
    ¬ (subsetSum D (Cᶜ : Finset (Fin m)) - 1).PosDef
      ∧ ∀ d ∈ (Cᶜ : Finset (Fin m)),
        ¬ (subsetSum D (insert z ((Cᶜ : Finset (Fin m)).erase d)) - 1).PosDef := by
  have hzc : z ∉ (Cᶜ : Finset (Fin m)) := by
    simp only [Finset.mem_compl, not_not]
    exact hz
  exact ⟨core_not_posDef_of_fourSet_not_posDef D hzc hnotz,
    fun d hd => star_not_posDef_of_fourSet_not_posDef D hzc hnotz hd⟩

end Gtz

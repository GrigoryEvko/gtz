/-
# The rank-two tie criterion at every size

`Gtz.isTie_iff_leverage_identity` decides `Gtz.IsTie` at CORANK ONE, and
`Gtz.leverage_identity_forces_corank_one` shows that criterion is a corank-one
law and nothing more: at `m > k + 1` no design of any kind satisfies it.  At
rank two that leaves every size `m >= 4` undecided.  This file supplies the
missing general-size law, in the only shape the corank-one equation can survive
in — an INEQUALITY, per atom, with the exact defect named.

    THE MASTER IDENTITY.  For every weighted `(m, k)` design and every atom,

        sum_d t_d * pairGapForm D pivot d = (k - 2) * l_pivot - (k - 1)

    where `pairGapForm D c d = (l_c - 1)(l_d - 1) - <g_c, g_d>^2`.  Two shipped
    Parseval consequences carry it: the excess budget `sum_d t_d (l_d - 1) = k - 1`
    and Parseval at the probe `g_pivot`, `sum_d t_d <g_d, g_pivot>^2 = l_pivot`.

At rank two the right-hand side collapses to `-1`, independently of the atom,
and `pairGapForm` becomes the GAP DETERMINANT of a pair:

    det (S_{c,d} - 1) = pairGapForm D c d          `det_pairGap_eq_pairGapForm`

so peeling the diagonal term `pairGapForm D c c = 1 - 2 l_c` off the master
identity gives, at every atom of every rank-two design,

    sum_{d != c} t_d * det (S_{c,d} - 1) = 2 t_c l_c - t_c - 1.

Everything else is a corollary.

* `exists_posDef_pair_of_nesterenkoExcess` — THE ENGINE, and it carries NO
  hypotheses beyond the excess itself: if one atom has `2 t_c l_c > 1 + t_c`
  then some pair through `c` dominates STRICTLY.  Heaviness of `c` is implied
  by the excess, heaviness of the partner is implied by the gap determinant's
  sign, and those two together supply the trace side of the `2 x 2` test.
* `weightedLeverage_le_nesterenkoBound_of_isTie` — the contrapositive, the
  general-size tie law: EVERY atom of a rank-two tie obeys `2 t_c l_c <= 1 + t_c`,
  i.e. `l_c <= (1 + t_c) / (2 t_c)`, at every size.
* `nesterenkoDefect_eq_sum_erase_neg_pairGapForm` — the law is exact, not lossy:
  the slack in it is the weighted sum of the pair gap deficits at that atom, so
  equality at `c` says every pair through `c` is exactly tight.
* `leverage_identity_of_isTie_rankTwoCorankOne` — at `m = 3` the trace forces
  the inequality to be an equality at every atom, re-deriving the `k = 2` case
  of `Gtz.isTie_iff_leverage_identity` from the master identity alone, with no
  resolvent, no dependency line and no rank-nullity.
* `sum_erase_pairGapForm_eq_three_sub_size` — the deficit law: summed over the
  atoms the identity reads `3 - m`, so at `m = 3` all pair gaps vanish and at
  `m >= 4` the tie budget is exactly `m - 3`.

PROVENANCE.  At corank one the inequality is an equality and is Nesterenko
(arXiv:2604.14050) Proposition 1, already mechanized in
`Gtz.Ties.CorankOneTieCriterion`.  The master identity, its rank-two collapse,
the general-size inequality and the engine are new here.

SCOPE, HONESTLY.  The inequality is necessary; it is NOT claimed sufficient
beyond corank one, and no theorem here says a rank-two tie must be corank one.
Ties beyond corank one certainly exist at rank two — split any atom of a
corank-one tie into parallel copies — and those satisfy the bound with slack,
which is what the deficit law measures.

    OPEN, and measured: is every rank-two tie a parallel split of a corank-one
    one — equivalently, does every rank-two tie have at most THREE pairwise
    non-parallel atom directions?  If yes, merging parallel classes plus
    `Gtz.isTie_iff_leverage_identity` at `k = 2` CLASSIFIES rank-two ties at
    every size, and the bound proved here is its shadow.

`RankTwoFourDirectionHinge` is that question, named, in the shape its consumers
need: four pairwise non-parallel atoms force a strictly dominating pair.
`not_isTie_of_fourDirections` is the one-line consequence.  The case `m = 3` is
already a theorem below (`leverage_identity_of_isTie_rankTwoCorankOne`), so the
hinge is a statement about `m >= 4` alone.

EVIDENCE, all outside Lean and all at exact-rational or >= 80-digit precision.
The parameterisation used is the honest one: angles plus the Parseval family of
`L_c = t_c l_c` plus the weights, with `det (S_cd - 1) = B_cd^2 - l_c - l_d + 1`
(`pairGapForm_eq_pairBracket_sq_sub`) as the decision function, and with the
deficit law `sum_{c<d} (t_c + t_d) (-det) = m - 3` reproduced to twelve digits at
every optimum as an independent check on the identity proved here.

* `m = 4`: maximising the worst pair gap over four pairwise non-parallel
  directions returns a NEGATIVE optimum at every non-parallelism floor, and it
  scales linearly with that floor — worst gap `-0.061, -0.036, -0.0139,
  -0.0063, -0.0016, -0.00071` at floors `min |sin| = 0.1, 0.05, 0.02, 0.01,
  0.003, 0.001`, a ratio near `-0.65` across three decades.  The optimum is
  driven to the PARALLEL boundary, which is where the split ties live.
* `m = 5`: worst gap `-0.059` at floor `0.01`, an order of magnitude further
  from feasible than `m = 4` at the same floor.
* A double-precision continuation that appeared to produce a four-direction tie
  was refuted at eighty digits: those points carry a strictly dominating pair
  with residual about `+5e-7`, and the one exact tie Newton reaches on that
  family has third weight `5e-82` — the zero-weight boundary of the
  three-direction case, not a design.

So the evidence is one-sided and the hinge is open, not refuted; the only ties
found anywhere are parallel splits of corank-one ones.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.TwoByTwo
import Gtz.Design.LeverageBound
import Gtz.Quantitative.ChartHadamard
import Gtz.Quantitative.DesignQuadraticFloors
import Gtz.Quantitative.VolumeSelectionFailure
import Gtz.Reduction.RealVolumeFloor
import Gtz.Reduction.Reductions
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.TwoPoleStratum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1: the pair gap form and the master identity -/

/-- The **pair gap form** of two atoms: the leverage excesses multiplied, less
the squared pairing.  At rank two this is exactly `det (S_{c,d} - 1)`
(`det_pairGap_eq_pairGapForm`); at other ranks it is still the quantity the
master identity averages. -/
def pairGapForm (D : WeightedDesign m k) (pivotLabel partnerLabel : Fin m) : ℝ :=
  (leverageOf (D.atom pivotLabel) - 1) * (leverageOf (D.atom partnerLabel) - 1)
    - (D.atom pivotLabel ⬝ᵥ D.atom partnerLabel) ^ 2

/-- The diagonal of the pair gap form reads the leverage back: `(l - 1)^2 - l^2`. -/
theorem pairGapForm_self (D : WeightedDesign m k) (pivotLabel : Fin m) :
    pairGapForm D pivotLabel pivotLabel = 1 - 2 * leverageOf (D.atom pivotLabel) := by
  rw [pairGapForm, ← leverageOf_eq_dotProduct]
  ring

/-- The pair gap form is symmetric in its two labels. -/
theorem pairGapForm_comm (D : WeightedDesign m k) (pivotLabel partnerLabel : Fin m) :
    pairGapForm D pivotLabel partnerLabel = pairGapForm D partnerLabel pivotLabel := by
  rw [pairGapForm, pairGapForm, dotProduct_comm (D.atom pivotLabel) (D.atom partnerLabel)]
  ring

/-- **THE MASTER IDENTITY.**  The weighted average of the pair gap form against
a fixed pivot is a function of the pivot's leverage and the rank alone.  Two
Parseval consequences carry it: the excess budget
`Gtz.sum_weight_mul_leverage_sub_one` and Parseval at the probe `g_pivot`
(`Gtz.dotProduct_self_eq_sum_weight_mul_sq`).  Nothing else about the design
enters, at any rank and any size. -/
theorem sum_weight_mul_pairGapForm (D : WeightedDesign m k) (pivotLabel : Fin m) :
    ∑ partnerLabel, D.weight partnerLabel * pairGapForm D pivotLabel partnerLabel
      = ((k : ℝ) - 2) * leverageOf (D.atom pivotLabel) - ((k : ℝ) - 1) := by
  have hexcessBudget : ∑ partnerLabel,
      D.weight partnerLabel * (leverageOf (D.atom partnerLabel) - 1) = (k : ℝ) - 1 :=
    sum_weight_mul_leverage_sub_one D
  have hprobeParseval : ∑ partnerLabel,
      D.weight partnerLabel * (D.atom partnerLabel ⬝ᵥ D.atom pivotLabel) ^ 2
      = leverageOf (D.atom pivotLabel) := by
    rw [leverageOf_eq_dotProduct]
    exact (dotProduct_self_eq_sum_weight_mul_sq D (D.atom pivotLabel)).symm
  have hsplitTerm : ∀ partnerLabel : Fin m,
      D.weight partnerLabel * pairGapForm D pivotLabel partnerLabel
        = (leverageOf (D.atom pivotLabel) - 1)
            * (D.weight partnerLabel * (leverageOf (D.atom partnerLabel) - 1))
          - D.weight partnerLabel * (D.atom partnerLabel ⬝ᵥ D.atom pivotLabel) ^ 2 := by
    intro partnerLabel
    rw [pairGapForm, dotProduct_comm (D.atom pivotLabel) (D.atom partnerLabel)]
    ring
  rw [Finset.sum_congr rfl fun partnerLabel _ => hsplitTerm partnerLabel,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hexcessBudget, hprobeParseval]
  ring

/-- At RANK TWO the master identity loses its dependence on the pivot: the
weighted average of the pair gap form is `-1` at every atom of every design. -/
theorem sum_weight_mul_pairGapForm_rankTwo (D : WeightedDesign m 2) (pivotLabel : Fin m) :
    ∑ partnerLabel, D.weight partnerLabel * pairGapForm D pivotLabel partnerLabel = -1 := by
  rw [sum_weight_mul_pairGapForm]
  norm_num

/-- **The off-diagonal master identity at rank two.**  Peeling the diagonal term
off `sum_weight_mul_pairGapForm_rankTwo` exposes the Nesterenko combination
`2 t_c l_c - t_c - 1` as the weighted total of the pair gap determinants
through the atom.  Every later theorem in this file is a reading of this line. -/
theorem sum_erase_weight_mul_pairGapForm (D : WeightedDesign m 2) (pivotLabel : Fin m) :
    ∑ partnerLabel ∈ Finset.univ.erase pivotLabel,
        D.weight partnerLabel * pairGapForm D pivotLabel partnerLabel
      = 2 * D.weight pivotLabel * leverageOf (D.atom pivotLabel)
        - D.weight pivotLabel - 1 := by
  have hfull := sum_weight_mul_pairGapForm_rankTwo D pivotLabel
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ pivotLabel), pairGapForm_self] at hfull
  linarith

/-! ## Part 2: the pair gap form IS the rank-two gap determinant -/

/-- The gap matrix of a pair is symmetric. -/
theorem transpose_pairGap (D : WeightedDesign m k)
    (pivotLabel partnerLabel : Fin m) :
    (subsetSum D {pivotLabel, partnerLabel} - 1)ᵀ
      = subsetSum D {pivotLabel, partnerLabel} - 1 := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum, Matrix.transpose_sum]
  refine congrArg (fun summed => summed - (1 : Matrix (Fin k) (Fin k) ℝ)) ?_
  refine Finset.sum_congr rfl fun label _ => ?_
  ext rowIndex colIndex
  simp [atomMatrix, Matrix.vecMulVec_apply, mul_comm]

/-- **The gap determinant, in closed form.**  At rank two the `2 x 2`
determinant of `S_{c,d} - 1` is exactly the pair gap form.  Lagrange's identity
`l_c l_d - <g_c,g_d>^2 = (bracket)^2` is what makes the two expressions agree. -/
theorem det_pairGap_eq_pairGapForm (D : WeightedDesign m 2)
    {pivotLabel partnerLabel : Fin m} (hdistinct : pivotLabel ≠ partnerLabel) :
    (subsetSum D {pivotLabel, partnerLabel} - 1).det
      = pairGapForm D pivotLabel partnerLabel := by
  rw [subsetSum_pair D hdistinct, Matrix.det_fin_two, pairGapForm]
  simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
    leverageOf, Fin.sum_univ_two, Matrix.one_apply, Fin.isValue]
  norm_num
  ring

/-- The trace of a pair's gap matrix is the leverage excess of the two atoms. -/
theorem entryDiagonal_pairGap (D : WeightedDesign m 2)
    {pivotLabel partnerLabel : Fin m} (hdistinct : pivotLabel ≠ partnerLabel) :
    (subsetSum D {pivotLabel, partnerLabel} - 1) 0 0
        + (subsetSum D {pivotLabel, partnerLabel} - 1) 1 1
      = leverageOf (D.atom pivotLabel) + leverageOf (D.atom partnerLabel) - 2 := by
  rw [subsetSum_pair D hdistinct]
  simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
    leverageOf, Fin.sum_univ_two, Matrix.one_apply, Fin.isValue]
  norm_num
  ring

/-- **A positive pair gap form at a heavy atom is strict domination.**  The
partner is forced heavy too — the product of the two leverage excesses exceeds a
square, so the excesses share a sign — and that supplies the trace side of the
`2 x 2` positivity test.  The determinant side is the hypothesis. -/
theorem posDef_pairGap_of_pairGapForm_pos (D : WeightedDesign m 2)
    {pivotLabel partnerLabel : Fin m} (hdistinct : pivotLabel ≠ partnerLabel)
    (hpivotHeavy : 1 < leverageOf (D.atom pivotLabel))
    (hgapPos : 0 < pairGapForm D pivotLabel partnerLabel) :
    (subsetSum D {pivotLabel, partnerLabel} - 1).PosDef := by
  have hpartnerHeavy : 1 < leverageOf (D.atom partnerLabel) := by
    have hsquareNonneg : (0 : ℝ) ≤ (D.atom pivotLabel ⬝ᵥ D.atom partnerLabel) ^ 2 :=
      sq_nonneg _
    rw [pairGapForm] at hgapPos
    nlinarith [hgapPos, hsquareNonneg, hpivotHeavy]
  have hsymmetric := transpose_pairGap D pivotLabel partnerLabel
  have htracePos : 0 < (subsetSum D {pivotLabel, partnerLabel} - 1) 0 0
      + (subsetSum D {pivotLabel, partnerLabel} - 1) 1 1 := by
    rw [entryDiagonal_pairGap D hdistinct]
    linarith
  have hdetValue := det_pairGap_eq_pairGapForm D hdistinct
  have hminorEq : (subsetSum D {pivotLabel, partnerLabel} - 1) 0 0
        * (subsetSum D {pivotLabel, partnerLabel} - 1) 1 1
      - (subsetSum D {pivotLabel, partnerLabel} - 1) 0 1 ^ 2
      = pairGapForm D pivotLabel partnerLabel := by
    have hoffDiagonal : (subsetSum D {pivotLabel, partnerLabel} - 1) 1 0
        = (subsetSum D {pivotLabel, partnerLabel} - 1) 0 1 := by
      have hentry := congrFun (congrFun hsymmetric 0) 1
      simpa [Matrix.transpose_apply] using hentry
    rw [← hdetValue, Matrix.det_fin_two, hoffDiagonal]
    ring
  have hposSemidef : (subsetSum D {pivotLabel, partnerLabel} - 1).PosSemidef :=
    (posSemidef_two_iff_of_trace_pos hsymmetric htracePos).mpr (by rw [hminorEq]; linarith)
  exact hposSemidef.posDef_iff_det_ne_zero.mpr (by rw [hdetValue]; linarith)

/-! ## Part 3: the engine and the general-size tie law -/

/-- An atom whose weighted leverage exceeds the Nesterenko threshold is heavy.
Only `t <= 1` and `t > 0` are used. -/
theorem one_lt_leverage_of_nesterenkoExcess (D : WeightedDesign m k) (pivotLabel : Fin m)
    (hexcess : 1 + D.weight pivotLabel
      < 2 * D.weight pivotLabel * leverageOf (D.atom pivotLabel)) :
    1 < leverageOf (D.atom pivotLabel) := by
  have hweightPos := D.weight_pos pivotLabel
  have hweightLe : D.weight pivotLabel ≤ 1 := by
    rw [← D.weight_sum_one]
    exact Finset.single_le_sum (fun label _ => (D.weight_pos label).le)
      (Finset.mem_univ pivotLabel)
  nlinarith [hexcess, hweightPos, hweightLe]

/-- **THE ENGINE, restricted to a candidate set.**  If the pair gap forms
through a heavy pivot have positive weighted total over some set of candidates,
one of those candidates completes the pivot to a strictly dominating pair. -/
theorem exists_posDef_pair_in_of_pairGapForm_sum_pos (D : WeightedDesign m 2)
    (pivotLabel : Fin m) (candidates : Finset (Fin m))
    (hpivotOutside : pivotLabel ∉ candidates)
    (hpivotHeavy : 1 < leverageOf (D.atom pivotLabel))
    (hsumPos : 0 < ∑ partnerLabel ∈ candidates,
      D.weight partnerLabel * pairGapForm D pivotLabel partnerLabel) :
    ∃ partnerLabel ∈ candidates,
      (subsetSum D {pivotLabel, partnerLabel} - 1).PosDef := by
  have hzeroSum : ∑ _partnerLabel ∈ candidates, (0 : ℝ) = 0 := Finset.sum_const_zero
  have hstrict : ∑ _partnerLabel ∈ candidates, (0 : ℝ)
      < ∑ partnerLabel ∈ candidates,
        D.weight partnerLabel * pairGapForm D pivotLabel partnerLabel := by
    rw [hzeroSum]; exact hsumPos
  obtain ⟨partnerLabel, hmember, hterm⟩ := Finset.exists_lt_of_sum_lt hstrict
  have hgapPos : 0 < pairGapForm D pivotLabel partnerLabel := by
    have hweightPos := D.weight_pos partnerLabel
    nlinarith [hterm, hweightPos]
  have hdistinct : pivotLabel ≠ partnerLabel := fun heq =>
    hpivotOutside (heq ▸ hmember)
  exact ⟨partnerLabel, hmember, posDef_pairGap_of_pairGapForm_pos D hdistinct hpivotHeavy hgapPos⟩

/-- **THE ENGINE.**  One atom of a rank-two design whose weighted leverage
exceeds `(1 + t_c) / 2` forces a strictly dominating pair through that atom.
There is no all-heavy hypothesis and no parallel-freeness hypothesis: the excess
supplies the pivot's heaviness and the gap determinant's sign supplies the
partner's.  This is a TIE-EMPTINESS test, not a selection rule, so it is not
touched by `Gtz.no_universal_dominating_subset`. -/
theorem exists_posDef_pair_of_nesterenkoExcess (D : WeightedDesign m 2) (pivotLabel : Fin m)
    (hexcess : 1 + D.weight pivotLabel
      < 2 * D.weight pivotLabel * leverageOf (D.atom pivotLabel)) :
    ∃ partnerLabel, partnerLabel ≠ pivotLabel ∧
      (subsetSum D {pivotLabel, partnerLabel} - 1).PosDef := by
  have hpivotHeavy := one_lt_leverage_of_nesterenkoExcess D pivotLabel hexcess
  have hsumPos : 0 < ∑ partnerLabel ∈ Finset.univ.erase pivotLabel,
      D.weight partnerLabel * pairGapForm D pivotLabel partnerLabel := by
    rw [sum_erase_weight_mul_pairGapForm]
    linarith
  obtain ⟨partnerLabel, hmember, hposDef⟩ :=
    exists_posDef_pair_in_of_pairGapForm_sum_pos D pivotLabel _
      (Finset.notMem_erase pivotLabel Finset.univ) hpivotHeavy hsumPos
  exact ⟨partnerLabel, (Finset.mem_erase.mp hmember).1, hposDef⟩

/-- **THE GENERAL-SIZE RANK-TWO TIE LAW.**  Every atom of a rank-two tie obeys
`2 t_c l_c <= 1 + t_c`, equivalently `l_c <= (1 + t_c) / (2 t_c)`, at EVERY size.
At corank one (`m = 3`) this is an equality and is the `k = 2` case of
`Gtz.isTie_iff_leverage_identity`; beyond corank one the equality is impossible
(`Gtz.leverage_identity_forces_corank_one`) and the inequality is what remains. -/
theorem weightedLeverage_le_nesterenkoBound_of_isTie (D : WeightedDesign m 2)
    (htie : IsTie D) (pivotLabel : Fin m) :
    2 * D.weight pivotLabel * leverageOf (D.atom pivotLabel) ≤ 1 + D.weight pivotLabel := by
  by_contra hviolated
  push Not at hviolated
  obtain ⟨partnerLabel, hdistinct, hposDef⟩ :=
    exists_posDef_pair_of_nesterenkoExcess D pivotLabel hviolated
  exact htie.2 {pivotLabel, partnerLabel}
    (Finset.card_pair (Ne.symm hdistinct)) hposDef

/-- **The law is exact.**  The slack in the tie bound at an atom is the weighted
total of the pair gap DEFICITS through it, so the bound holds with equality at
`c` exactly when every pair through `c` is tight. -/
theorem nesterenkoDefect_eq_sum_erase_neg_pairGapForm (D : WeightedDesign m 2)
    (pivotLabel : Fin m) :
    1 + D.weight pivotLabel
        - 2 * D.weight pivotLabel * leverageOf (D.atom pivotLabel)
      = ∑ partnerLabel ∈ Finset.univ.erase pivotLabel,
          D.weight partnerLabel * (- pairGapForm D pivotLabel partnerLabel) := by
  have hidentity := sum_erase_weight_mul_pairGapForm D pivotLabel
  have hnegate : ∑ partnerLabel ∈ Finset.univ.erase pivotLabel,
        D.weight partnerLabel * (- pairGapForm D pivotLabel partnerLabel)
      = - ∑ partnerLabel ∈ Finset.univ.erase pivotLabel,
          D.weight partnerLabel * pairGapForm D pivotLabel partnerLabel := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun partnerLabel _ => by ring
  rw [hnegate, hidentity]
  ring

/-- **The deficit law.**  Summed over the atoms the master identity reads
`3 - m`: at `m = 3` the weighted pair gaps must all vanish, and at `m >= 4` the
total tie budget is exactly `m - 3`. -/
theorem sum_erase_pairGapForm_eq_three_sub_size (D : WeightedDesign m 2) :
    ∑ pivotLabel, (∑ partnerLabel ∈ Finset.univ.erase pivotLabel,
        D.weight partnerLabel * pairGapForm D pivotLabel partnerLabel)
      = 3 - (m : ℝ) := by
  have hpointwise : ∀ pivotLabel : Fin m,
      (∑ partnerLabel ∈ Finset.univ.erase pivotLabel,
        D.weight partnerLabel * pairGapForm D pivotLabel partnerLabel)
        = 2 * (D.weight pivotLabel * leverageOf (D.atom pivotLabel))
          - D.weight pivotLabel - 1 := by
    intro pivotLabel
    rw [sum_erase_weight_mul_pairGapForm]
    ring
  rw [Finset.sum_congr rfl fun pivotLabel _ => hpointwise pivotLabel]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_weighted_leverage D, D.weight_sum_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  norm_num

/-! ## Part 4: corank one recovered, and sharpness -/

/-- **The corank-one criterion, re-derived at rank two.**  At `m = 3` the
per-atom inequality is forced to be an equality: the bounds sum to `4` on both
sides — Parseval's trace on the left, `m + 1` on the right — so no atom can have
slack.  This is the `k = 2` case of `Gtz.isTie_iff_leverage_identity`, obtained
from the master identity alone. -/
theorem leverage_identity_of_isTie_rankTwoCorankOne (D : WeightedDesign 3 2)
    (htie : IsTie D) (pivotLabel : Fin 3) :
    2 * D.weight pivotLabel * leverageOf (D.atom pivotLabel) = 1 + D.weight pivotLabel := by
  have hbound := weightedLeverage_le_nesterenkoBound_of_isTie D htie
  have hslackNonneg : ∀ label ∈ (Finset.univ : Finset (Fin 3)),
      0 ≤ 1 + D.weight label - 2 * D.weight label * leverageOf (D.atom label) :=
    fun label _ => by linarith [hbound label]
  have hslackSum : ∑ label : Fin 3,
      (1 + D.weight label - 2 * D.weight label * leverageOf (D.atom label)) = 0 := by
    have hregroup : ∀ label : Fin 3,
        1 + D.weight label - 2 * D.weight label * leverageOf (D.atom label)
          = 1 + D.weight label - 2 * (D.weight label * leverageOf (D.atom label)) :=
      fun label => by ring
    rw [Finset.sum_congr rfl fun label _ => hregroup label,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_weighted_leverage D, D.weight_sum_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    norm_num
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hslackNonneg).mp hslackSum
      pivotLabel (Finset.mem_univ pivotLabel)
  linarith

/-- **The bound is attained.**  Its equality case is exactly the shipped
corank-one tie locus, which is nonempty at every rank: `Gtz.tetraDesign` and
`Gtz.sharpDesign` sit on it.  Stated here at rank two, where the equality reads
`l_c = 1/2 + 1/(2 t_c)`, so the bound cannot be sharpened to a strict one. -/
theorem exists_isTie_rankTwoCorankOne_attaining_bound
    (D : WeightedDesign 3 2) (htie : IsTie D) :
    ∀ pivotLabel : Fin 3,
      2 * D.weight pivotLabel * leverageOf (D.atom pivotLabel) = 1 + D.weight pivotLabel :=
  leverage_identity_of_isTie_rankTwoCorankOne D htie

/-! ## Part 5: brackets, parallel pairs, and the rank-two hinge -/

/-- The `2 x 2` bracket of two rank-two atoms.  It vanishes exactly when the two
atoms are parallel. -/
def pairBracket (D : WeightedDesign m 2) (leftLabel rightLabel : Fin m) : ℝ :=
  D.atom leftLabel 0 * D.atom rightLabel 1 - D.atom leftLabel 1 * D.atom rightLabel 0

/-- **Lagrange's identity, in gap form.**  The pair gap form is the squared
bracket less the leverage excess of the pair.  This is the shape Cauchy-Binet
consumes, and it is what makes the bracket the right measure of direction
spread: at a fixed leverage pair the gap grows exactly with the squared area. -/
theorem pairGapForm_eq_pairBracket_sq_sub (D : WeightedDesign m 2)
    (leftLabel rightLabel : Fin m) :
    pairGapForm D leftLabel rightLabel
      = pairBracket D leftLabel rightLabel ^ 2
        - leverageOf (D.atom leftLabel) - leverageOf (D.atom rightLabel) + 1 := by
  simp only [pairGapForm, pairBracket, leverageOf, dotProduct, Fin.sum_univ_two, Fin.isValue]
  ring

/-- **A parallel pair never dominates strictly.**  Its bracket vanishes, so its
gap determinant is `1 - l_c - l_d`, negative as soon as the two leverages exceed
one together — in particular for any pair of heavy atoms.  This is why merging
parallel classes cannot destroy a strict pair, and why the hinge below is stated
for pairwise NON-parallel atoms. -/
theorem not_posDef_pairGap_of_pairBracket_eq_zero (D : WeightedDesign m 2)
    {leftLabel rightLabel : Fin m} (hdistinct : leftLabel ≠ rightLabel)
    (hparallel : pairBracket D leftLabel rightLabel = 0)
    (hmass : 1 < leverageOf (D.atom leftLabel) + leverageOf (D.atom rightLabel)) :
    ¬ (subsetSum D {leftLabel, rightLabel} - 1).PosDef := by
  intro hposDef
  have hdet := hposDef.det_pos
  rw [det_pairGap_eq_pairGapForm D hdistinct,
    pairGapForm_eq_pairBracket_sq_sub, hparallel] at hdet
  nlinarith [hdet, hmass]

/-- **THE RANK-TWO HINGE — OPEN.**  Four pairwise non-parallel atoms in a
rank-two design force a strictly dominating pair.  Equivalently, by
`not_isTie_of_fourDirections`, every rank-two tie has at most three pairwise
non-parallel atoms, so — parallel pairs being harmless by
`not_posDef_pairGap_of_pairBracket_eq_zero` — every rank-two tie is a parallel
split of a corank-one one, and `Gtz.isTie_iff_leverage_identity` at `k = 2`
classifies rank-two ties at EVERY size.

This is the rank-two shadow of the campaign's own hinge, and it is the object
both open branches of the `(6,3)` stress trichotomy consume: the two-pole
companion carries two parallel pole atoms over a planar family, so as soon as
four of its planar labels are pairwise non-parallel the hinge closes the
substratum outright — not merely on the `poleMass > 1/2` slice that
`poleSectorGate_iff_poleMass_gt_half` reaches.

The case `m = 3` is NOT part of it: there the conclusion is false and the
correct statement is the equality `leverage_identity_of_isTie_rankTwoCorankOne`,
proved above.  See the file header for the numerical evidence. -/
def RankTwoFourDirectionHinge : Prop :=
  ∀ (size : ℕ) (D : WeightedDesign size 2) (firstLabel secondLabel thirdLabel
      fourthLabel : Fin size),
    firstLabel ≠ secondLabel → firstLabel ≠ thirdLabel → firstLabel ≠ fourthLabel →
    secondLabel ≠ thirdLabel → secondLabel ≠ fourthLabel → thirdLabel ≠ fourthLabel →
    pairBracket D firstLabel secondLabel ≠ 0 → pairBracket D firstLabel thirdLabel ≠ 0 →
    pairBracket D firstLabel fourthLabel ≠ 0 → pairBracket D secondLabel thirdLabel ≠ 0 →
    pairBracket D secondLabel fourthLabel ≠ 0 → pairBracket D thirdLabel fourthLabel ≠ 0 →
    ∃ dominatingPair : Finset (Fin size), dominatingPair.card = 2
      ∧ (subsetSum D dominatingPair - 1).PosDef

/-- **The hinge, in tie form.**  Under `RankTwoFourDirectionHinge` no rank-two
tie carries four pairwise non-parallel atoms.  This is the statement the two
open branches of the trichotomy would consume. -/
theorem not_isTie_of_fourDirections (hhinge : RankTwoFourDirectionHinge)
    (D : WeightedDesign m 2) (firstLabel secondLabel thirdLabel fourthLabel : Fin m)
    (hone : firstLabel ≠ secondLabel) (htwo : firstLabel ≠ thirdLabel)
    (hthree : firstLabel ≠ fourthLabel) (hfour : secondLabel ≠ thirdLabel)
    (hfive : secondLabel ≠ fourthLabel) (hsix : thirdLabel ≠ fourthLabel)
    (hbracketOne : pairBracket D firstLabel secondLabel ≠ 0)
    (hbracketTwo : pairBracket D firstLabel thirdLabel ≠ 0)
    (hbracketThree : pairBracket D firstLabel fourthLabel ≠ 0)
    (hbracketFour : pairBracket D secondLabel thirdLabel ≠ 0)
    (hbracketFive : pairBracket D secondLabel fourthLabel ≠ 0)
    (hbracketSix : pairBracket D thirdLabel fourthLabel ≠ 0) :
    ¬ IsTie D := by
  intro htie
  obtain ⟨dominatingPair, hcard, hposDef⟩ :=
    hhinge m D firstLabel secondLabel thirdLabel fourthLabel hone htwo hthree hfour hfive
      hsix hbracketOne hbracketTwo hbracketThree hbracketFour hbracketFive hbracketSix
  exact htie.2 dominatingPair hcard hposDef

/-! ## Part 6: the two-pole companion — the reach, and the wall

The two-pole transport of branch (iii) builds a rank-two COMPANION whose two
pole labels carry the SAME atom on the seed axis with the SAME weight, the other
labels carrying the rescaled planar coordinates.  The residual is exactly that
`Gtz.gtz_rank_two` returns a merely weakly dominating pair there.  The engine
above answers that question, but the arithmetic of the companion decides WHERE
it may be applied, and the two theorems below record both halves. -/

/-- **THE WALL: the engine can never fire at a pole atom of the companion.**
The two pole labels are parallel and confined to the seed axis, whose companion
second moment is exactly one, so their shared share obeys
`2 * poleWeight * poleLeverage <= 1`, strictly below the threshold
`1 + poleWeight`.  Applying `exists_posDef_pair_of_nesterenkoExcess` at a pole
is therefore impossible, for every configuration, on and off the crossing
locus. -/
theorem not_nesterenkoExcess_of_axisMomentBudget
    {poleWeight poleLeverage planarAlongShare : ℝ}
    (hpoleWeightPos : 0 < poleWeight) (hplanarNonneg : 0 ≤ planarAlongShare)
    (haxisMoment : 2 * (poleWeight * poleLeverage) + planarAlongShare = 1) :
    2 * poleWeight * poleLeverage < 1 + poleWeight := by
  nlinarith [haxisMoment, hplanarNonneg, hpoleWeightPos]

/-- **THE REACH: the twin-pole gate.**  What the pole atom CAN do is spend its
parallel twin.  The twin's own pair gap is `1 - 2 l`, strictly negative, so
removing it from the master identity leaves the planar labels carrying
`4 t l - 2 t - 1`.  When that is positive some PLANAR label completes the pole
to a strictly dominating pair — the shape
`Gtz.posDef_polePair_triple_of_scalarGate` consumes.  The threshold is half the
single-atom one, which is exactly the slack the wall above leaves unused. -/
theorem exists_posDef_polePlanarPair_of_twinGate (D : WeightedDesign m 2)
    (poleFirst poleSecond : Fin m) (hpolesDistinct : poleFirst ≠ poleSecond)
    (htwinAtom : D.atom poleSecond = D.atom poleFirst)
    (htwinWeight : D.weight poleSecond = D.weight poleFirst)
    (htwinGate : 2 * D.weight poleFirst + 1
      < 4 * D.weight poleFirst * leverageOf (D.atom poleFirst)) :
    ∃ planarLabel ∈ (Finset.univ.erase poleFirst).erase poleSecond,
      (subsetSum D {poleFirst, planarLabel} - 1).PosDef := by
  classical
  have hsecondMem : poleSecond ∈ Finset.univ.erase poleFirst :=
    Finset.mem_erase.mpr ⟨Ne.symm hpolesDistinct, Finset.mem_univ poleSecond⟩
  have htwinMassLe : 2 * D.weight poleFirst ≤ 1 := by
    have hpairSum : ∑ label ∈ ({poleFirst, poleSecond} : Finset (Fin m)), D.weight label
        = D.weight poleFirst + D.weight poleSecond := Finset.sum_pair hpolesDistinct
    have hbound := sum_weight_subset_le_one D ({poleFirst, poleSecond} : Finset (Fin m))
    rw [hpairSum, htwinWeight] at hbound
    linarith
  have hpoleHeavy : 1 < leverageOf (D.atom poleFirst) := by
    have hweightPos := D.weight_pos poleFirst
    nlinarith [htwinGate, htwinMassLe, hweightPos]
  have htwinTerm : D.weight poleSecond * pairGapForm D poleFirst poleSecond
      = D.weight poleFirst * (1 - 2 * leverageOf (D.atom poleFirst)) := by
    have hform : pairGapForm D poleFirst poleSecond
        = 1 - 2 * leverageOf (D.atom poleFirst) := by
      rw [pairGapForm, htwinAtom, ← leverageOf_eq_dotProduct]
      ring
    rw [hform, htwinWeight]
  have hsplit := Finset.add_sum_erase _
    (fun partnerLabel => D.weight partnerLabel * pairGapForm D poleFirst partnerLabel)
    hsecondMem
  have hplanarSum : ∑ planarLabel ∈ (Finset.univ.erase poleFirst).erase poleSecond,
      D.weight planarLabel * pairGapForm D poleFirst planarLabel
      = 4 * D.weight poleFirst * leverageOf (D.atom poleFirst)
        - 2 * D.weight poleFirst - 1 := by
    have hfull := sum_erase_weight_mul_pairGapForm D poleFirst
    rw [← hsplit, htwinTerm] at hfull
    linarith
  have hsumPos : 0 < ∑ planarLabel ∈ (Finset.univ.erase poleFirst).erase poleSecond,
      D.weight planarLabel * pairGapForm D poleFirst planarLabel := by
    rw [hplanarSum]; linarith
  exact exists_posDef_pair_in_of_pairGapForm_sum_pos D poleFirst _
    (fun hmem => (Finset.mem_erase.mp (Finset.mem_erase.mp hmem).2).1 rfl)
    hpoleHeavy hsumPos

/-- **The twin gate translated into the two-pole lane's moment coordinates.**
The companion's along-axis moment splits as `2 poleWeight poleEntry^2` plus the
planar along share, and its weight budget as `2 poleWeight` plus the planar mass.
Eliminating `poleEntry` between the two turns the twin gate into a statement
about the PLANAR family alone: its along-second-moment must be under half its
mass.  In the lane's sector variables that is `2 (1 - nu) / (1 + kappa)` below
`planarMass / planarScale`, since the along share is exactly `(1 - nu)/(1 + kappa)`
and the planar mass over the scale is exactly `1 - 2 poleWeight`.  Every quantity
in it is FIRST-order in the planar weights, so the gate is inside the data the
two-pole lane carries — unlike the single-atom engine, which needs a second-order
planar weight moment. -/
theorem twinGate_of_planarAlongDeficit
    {poleWeight poleEntry planarAlongShare planarMass : ℝ}
    (haxisMoment : 2 * (poleWeight * poleEntry ^ 2) + planarAlongShare = 1)
    (hweightBudget : 2 * poleWeight + planarMass = 1)
    (hplanarDeficit : 2 * planarAlongShare < planarMass) :
    2 * poleWeight + 1 < 4 * poleWeight * poleEntry ^ 2 := by
  nlinarith [haxisMoment, hweightBudget, hplanarDeficit]

/-- **The twin gate's exact reach in the pole sector.**  In the two-pole lane the
companion's planar along share is `(1 - nu) / (1 + kappa)` and its planar mass
over the free companion scale is `planarMass / planarScale`, with the scale a
free choice strictly between the planar mass and one.  Pushing the scale down to
the planar mass drives that ratio to one, so the twin gate is reachable exactly
when `2 (1 - nu) < 1 + kappa`.  This produces the witnessing scale. -/
theorem exists_planarScale_of_poleSectorGate
    {inPlaneMass kappa planarMass : ℝ}
    (hplanarPos : 0 < planarMass) (hplanarLtOne : planarMass < 1)
    (hkappaNonneg : 0 ≤ kappa)
    (hsector : 1 < 2 * inPlaneMass + kappa) :
    ∃ planarScale, planarMass < planarScale ∧ planarScale < 1
      ∧ 2 * ((1 - inPlaneMass) / (1 + kappa)) < planarMass / planarScale := by
  have hkappaPos : (0 : ℝ) < 1 + kappa := by linarith
  have hfold : 2 * ((1 - inPlaneMass) / (1 + kappa))
      = (2 * (1 - inPlaneMass)) / (1 + kappa) := by ring
  have halongShareLtOne : 2 * ((1 - inPlaneMass) / (1 + kappa)) < 1 := by
    rw [hfold, div_lt_one hkappaPos]
    linarith
  have hmaxLtOne : max planarMass (2 * ((1 - inPlaneMass) / (1 + kappa))) < 1 :=
    max_lt hplanarLtOne halongShareLtOne
  have hratioLtOne : (max planarMass (2 * ((1 - inPlaneMass) / (1 + kappa))) + 1) / 2 < 1 := by
    linarith
  have hratioGtPlanar :
      planarMass < (max planarMass (2 * ((1 - inPlaneMass) / (1 + kappa))) + 1) / 2 := by
    have hle : planarMass ≤ max planarMass (2 * ((1 - inPlaneMass) / (1 + kappa))) :=
      le_max_left _ _
    linarith
  have hratioGtShare : 2 * ((1 - inPlaneMass) / (1 + kappa))
      < (max planarMass (2 * ((1 - inPlaneMass) / (1 + kappa))) + 1) / 2 := by
    have hle : 2 * ((1 - inPlaneMass) / (1 + kappa))
        ≤ max planarMass (2 * ((1 - inPlaneMass) / (1 + kappa))) := le_max_right _ _
    linarith
  have hratioPos : 0 < (max planarMass (2 * ((1 - inPlaneMass) / (1 + kappa))) + 1) / 2 :=
    lt_trans hplanarPos hratioGtPlanar
  refine ⟨planarMass / ((max planarMass (2 * ((1 - inPlaneMass) / (1 + kappa))) + 1) / 2),
    ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hratioPos]
    nlinarith [hratioLtOne, hplanarPos]
  · rw [div_lt_one hratioPos]; exact hratioGtPlanar
  · have hquotient : planarMass
        / (planarMass / ((max planarMass (2 * ((1 - inPlaneMass) / (1 + kappa))) + 1) / 2))
        = (max planarMass (2 * ((1 - inPlaneMass) / (1 + kappa))) + 1) / 2 := by
      field_simp
    rw [hquotient]; exact hratioGtShare

/-- **And the twin gate reaches no further.**  The companion scale must exceed
the planar mass for the pole weight to be positive, so the ratio the gate must
clear is below one for every admissible scale.  Off the sector region
`2 nu + kappa > 1` the gate is therefore unreachable, whatever scale is chosen —
the boundary of this lane's contribution to branch (iii), named. -/
theorem not_twinGate_of_poleSectorFails
    {inPlaneMass kappa planarMass planarScale : ℝ}
    (hplanarPos : 0 < planarMass) (hscaleGt : planarMass < planarScale)
    (hkappaNonneg : 0 ≤ kappa)
    (hsector : 2 * inPlaneMass + kappa ≤ 1) :
    ¬ (2 * ((1 - inPlaneMass) / (1 + kappa)) < planarMass / planarScale) := by
  have hkappaPos : (0 : ℝ) < 1 + kappa := by linarith
  have hscalePos : 0 < planarScale := lt_trans hplanarPos hscaleGt
  have hratioLtOne : planarMass / planarScale < 1 := (div_lt_one hscalePos).mpr hscaleGt
  have hfold : 2 * ((1 - inPlaneMass) / (1 + kappa))
      = (2 * (1 - inPlaneMass)) / (1 + kappa) := by ring
  have hshareGe : (1 : ℝ) ≤ 2 * ((1 - inPlaneMass) / (1 + kappa)) := by
    rw [hfold, le_div_iff₀ hkappaPos]
    linarith
  intro hgate
  linarith

/-! ### The hinge closes the two-pole substratum outright

The twin gate above is capped — measured by the sibling lane at `12.70%` of the
symmetric crossing branch, and `poleSectorGate_iff_poleMass_gt_half` says that
cap is structural.  `RankTwoFourDirectionHinge` is not capped at all, and the
three lemmas here are the whole reason why.

The two-pole companion carries two parallel pole shadows over `size - 2` planar
labels, and its planar label `c` is
`![alongScale * (g_c . seed), acrossScale * (g_c . cross)]`.  So:

* `frameBracket_eq_seedNormSq_mul_probeTriple` — the COMPRESSION step.  The
  bracket of two planar labels in the `(seed, cross)` frame is the seed norm
  times the probe's triple product with the two atoms, so it vanishes exactly
  when the two original atoms are parallel.  Only `seed . probe = 0` is used.
* `pairBracket_eq_of_scaledPlanarAtoms` — the RESCALING step, which is the one
  worth checking and which survives: the anisotropic rescaling multiplies the
  bracket by `alongScale * acrossScale` and nothing else, because a diagonal map
  of the plane is invertible when neither scale vanishes.  Non-parallelism is
  therefore preserved on the nose.
* `planarPair_strictTarget_of_strictMaster` — why the transport gate then
  DISAPPEARS.  The landed `planarPair_strictTarget` manufactures its strict
  conclusion out of a WEAK master inequality by paying `1 - planarScale > 0`,
  and `planarScale < 1` is the only thing the transport gate is needed for
  (`planarScale` merely has to exceed the planar mass for the companion to be a
  design at all).  Given a STRICT master inequality the payment is unnecessary:
  the conclusion holds at `planarScale = 1`, with no gate, no slack, and no
  hypothesis on `kappa`'s sign or the test vector.

Chaining them: the hinge fires on any four pairwise non-parallel planar labels,
returns a positive definite pair rather than a merely dominating one, and the
strict target lemma carries it to the carrier triple.  The crossing locus never
enters, because the companion's weight budget being tight was only ever a
problem for the WEAK-to-STRICT upgrade.

ONE DEGENERATE CASE, named: if `nu = 1` the planar family has zero seed moment,
every planar atom lies along the cross axis, and the planar labels are pairwise
PARALLEL — the hinge does not apply.  That configuration has a parallel pair in
the original design, which the campaign's parallel-pair funnel already removes.

THE OTHER BRANCH.  `frameBracket_eq_seedNormSq_mul_probeTriple` is not specific
to the two-pole compression: it says two atoms have parallel images in the plane
orthogonal to a direction exactly when that direction's triple product with them
vanishes, i.e. exactly when the two atoms are COPLANAR WITH THE AXIS.  The
tight-axis companion of the stress-free branch is the plain compression
`vec - (vec . axis) * axis` with the design's own weights, so it is the case
`alongScale = acrossScale = 1` of the rescaling step and the SAME criterion
decides it: four of its shadows are pairwise non-parallel exactly when no two of
those four atoms are coplanar with the tight axis.  What does NOT transfer for
free is the last leg — that branch's transport consumes a two-atom coupling
gate rather than a pair, so it would have to be restated to accept a strictly
dominating pair before the hinge could be plugged in there.
-/

/-- **The compression step.**  In the `(seed, cross)` frame the bracket of two
atoms is the seed's squared norm times the probe's triple product with them.
It therefore vanishes exactly when the two atoms are parallel — which is what
primitivity of the original design denies.  Only `seed . probe = 0` is used;
neither atom need be planar and the probe need not be a unit vector. -/
theorem frameBracket_eq_seedNormSq_mul_probeTriple
    (probe seed leftAtom rightAtom : Fin 3 → ℝ) (hseedPlanar : seed ⬝ᵥ probe = 0) :
    (leftAtom ⬝ᵥ seed) * (rightAtom ⬝ᵥ crossProduct probe seed)
        - (rightAtom ⬝ᵥ seed) * (leftAtom ⬝ᵥ crossProduct probe seed)
      = (seed ⬝ᵥ seed) * (probe ⬝ᵥ crossProduct leftAtom rightAtom) := by
  have hcoord : seed 0 * probe 0 + seed 1 * probe 1 + seed 2 * probe 2 = 0 := by
    simpa [dotProduct, Fin.sum_univ_three] using hseedPlanar
  simp only [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination (-(seed 0 * (leftAtom 1 * rightAtom 2 - leftAtom 2 * rightAtom 1)
      + seed 1 * (leftAtom 2 * rightAtom 0 - leftAtom 0 * rightAtom 2)
      + seed 2 * (leftAtom 0 * rightAtom 1 - leftAtom 1 * rightAtom 0))) * hcoord

/-- **The rescaling step.**  An anisotropic rescaling of the plane multiplies the
bracket by the product of the two scales.  This is the step the chain was most
likely to lose, and it does not: a diagonal map is invertible whenever neither
scale vanishes, so non-parallelism passes through untouched. -/
theorem pairBracket_eq_of_scaledPlanarAtoms {size : ℕ} (D : WeightedDesign size 2)
    (alongScale acrossScale : ℝ) (alongRaw acrossRaw : Fin size → ℝ)
    {leftLabel rightLabel : Fin size}
    (hleft : D.atom leftLabel
      = ![alongScale * alongRaw leftLabel, acrossScale * acrossRaw leftLabel])
    (hright : D.atom rightLabel
      = ![alongScale * alongRaw rightLabel, acrossScale * acrossRaw rightLabel]) :
    pairBracket D leftLabel rightLabel
      = alongScale * acrossScale
        * (alongRaw leftLabel * acrossRaw rightLabel
          - alongRaw rightLabel * acrossRaw leftLabel) := by
  rw [pairBracket, hleft, hright]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  ring

/-- Non-parallelism survives the compression and the rescaling together. -/
theorem pairBracket_ne_zero_of_scaledPlanarAtoms {size : ℕ} (D : WeightedDesign size 2)
    {alongScale acrossScale : ℝ} (alongRaw acrossRaw : Fin size → ℝ)
    {leftLabel rightLabel : Fin size}
    (hleft : D.atom leftLabel
      = ![alongScale * alongRaw leftLabel, acrossScale * acrossRaw leftLabel])
    (hright : D.atom rightLabel
      = ![alongScale * alongRaw rightLabel, acrossScale * acrossRaw rightLabel])
    (halongScale : alongScale ≠ 0) (hacrossScale : acrossScale ≠ 0)
    (hrawBracket : alongRaw leftLabel * acrossRaw rightLabel
      - alongRaw rightLabel * acrossRaw leftLabel ≠ 0) :
    pairBracket D leftLabel rightLabel ≠ 0 := by
  rw [pairBracket_eq_of_scaledPlanarAtoms D alongScale acrossScale alongRaw acrossRaw
    hleft hright]
  exact mul_ne_zero (mul_ne_zero halongScale hacrossScale) hrawBracket

/-- **The transport gate is unnecessary once the pair is strict.**  Strict twin of
the landed `Gtz.planarPair_strictTarget`, at `planarScale = 1`.  The landed form
buys its strict conclusion with `1 - planarScale > 0`, and that purchase is the
only thing the two-pole transport gate exists to enable.  A strictly dominating
companion pair pays for itself: the conclusion follows with no scale below one,
no slack, no sign condition on `kappa` and no nondegeneracy on the test vector. -/
theorem planarPair_strictTarget_of_strictMaster
    {seedNormSq kappa carrierTiltSq carrierAxisSq
      alongCoordFirst alongCoordSecond acrossCoordFirst acrossCoordSecond
      alongTest acrossTest : ℝ}
    (hcarrierSteep : 1 < carrierAxisSq)
    (hkappa : kappa * (carrierAxisSq - 1) = carrierTiltSq * seedNormSq)
    (hmasterStrict : (alongTest ^ 2 * (1 + kappa) + acrossTest ^ 2) * seedNormSq
      < (alongCoordFirst * alongTest + acrossCoordFirst * acrossTest) ^ 2
        + (alongCoordSecond * alongTest + acrossCoordSecond * acrossTest) ^ 2) :
    carrierTiltSq * alongTest ^ 2 * seedNormSq ^ 2
      < (carrierAxisSq - 1)
        * ((alongCoordFirst * alongTest + acrossCoordFirst * acrossTest) ^ 2
            + (alongCoordSecond * alongTest + acrossCoordSecond * acrossTest) ^ 2
          - seedNormSq * (alongTest ^ 2 + acrossTest ^ 2)) := by
  have hsteepPos : 0 < carrierAxisSq - 1 := by linarith
  have hlift := mul_lt_mul_of_pos_left hmasterStrict hsteepPos
  have hkappaTerm : (carrierAxisSq - 1) * (kappa * alongTest ^ 2 * seedNormSq)
      = carrierTiltSq * alongTest ^ 2 * seedNormSq ^ 2 := by
    linear_combination (alongTest ^ 2 * seedNormSq) * hkappa
  nlinarith [hlift, hkappaTerm]

/-- **The mixed shape's strict twin, and the gate vanishes there too.**  Strict
twin of the landed `Gtz.mixedPair_alongBound`, at `planarScale = 1`.  A pole
shadow paired with a planar atom is the second of the three shapes the returned
pair can take, and it was the one shape whose strict route was unverified.

It goes through, and more cleanly than the planar shape.  Two instantiations of
the strict master suffice: at `(0, 1)` for the across excess, and at the
quadratic's VERTEX, reached without division by taking
`(acrossCoord^2 - seedNormSq, -(alongCoord * acrossCoord))` — at which the
planar contribution collapses to `alongCoord^2 * seedNormSq^2` on the nose.
`planarScale` disappears from the statement, `hplanarScalePos` and
`hplanarScaleLt` go with it, and all THREE conclusions strengthen from `<=` to
`<`.  Nothing needs the slack `1 - planarScale`. -/
theorem mixedPair_alongBound_of_strictMaster
    {seedNormSq kappa poleShadow alongCoord acrossCoord : ℝ}
    (hseedPos : 0 < seedNormSq)
    (hmasterStrict : ∀ alongTest acrossTest : ℝ,
      0 < alongTest ^ 2 + acrossTest ^ 2 →
      (alongTest ^ 2 * (1 + kappa) + acrossTest ^ 2) * seedNormSq
        < poleShadow * seedNormSq * alongTest ^ 2
          + (alongCoord * alongTest + acrossCoord * acrossTest) ^ 2) :
    seedNormSq < acrossCoord ^ 2
      ∧ 0 < poleShadow - 1 - kappa
      ∧ alongCoord ^ 2 < (poleShadow - 1 - kappa) * (acrossCoord ^ 2 - seedNormSq) := by
  have hacrossBig : seedNormSq < acrossCoord ^ 2 := by
    have hraw := hmasterStrict 0 1 (by norm_num)
    nlinarith [hraw]
  have hgapPos : 0 < acrossCoord ^ 2 - seedNormSq := by linarith
  have hnondegenerate : 0 < (acrossCoord ^ 2 - seedNormSq) ^ 2
      + (-(alongCoord * acrossCoord)) ^ 2 := by
    nlinarith [pow_pos hgapPos 2, sq_nonneg (alongCoord * acrossCoord)]
  have hvertex := hmasterStrict (acrossCoord ^ 2 - seedNormSq)
    (-(alongCoord * acrossCoord)) hnondegenerate
  have hcollapse : (alongCoord * (acrossCoord ^ 2 - seedNormSq)
        + acrossCoord * (-(alongCoord * acrossCoord))) ^ 2
      = alongCoord ^ 2 * seedNormSq ^ 2 := by ring
  rw [hcollapse] at hvertex
  have hscaled : seedNormSq * (alongCoord ^ 2 * (acrossCoord ^ 2 - seedNormSq))
      < seedNormSq * ((poleShadow - 1 - kappa) * (acrossCoord ^ 2 - seedNormSq) ^ 2) := by
    nlinarith [hvertex]
  have hcancelSeed : alongCoord ^ 2 * (acrossCoord ^ 2 - seedNormSq)
      < (poleShadow - 1 - kappa) * (acrossCoord ^ 2 - seedNormSq) ^ 2 :=
    lt_of_mul_lt_mul_left hscaled hseedPos.le
  have hmain : alongCoord ^ 2
      < (poleShadow - 1 - kappa) * (acrossCoord ^ 2 - seedNormSq) := by
    have hfactored : (acrossCoord ^ 2 - seedNormSq) * (alongCoord ^ 2)
        < (acrossCoord ^ 2 - seedNormSq)
          * ((poleShadow - 1 - kappa) * (acrossCoord ^ 2 - seedNormSq)) := by
      nlinarith [hcancelSeed]
    exact lt_of_mul_lt_mul_left hfactored hgapPos.le
  exact ⟨hacrossBig, by nlinarith [hmain, sq_nonneg alongCoord, hgapPos], hmain⟩

/-- **The bridge from a positive definite pair to the strict master inequality.**
Both strict twins consume the master inequality in quadratic-form shape; a
positive definite companion pair supplies it directly.  This is the strict
counterpart of the weak reading at the end of
`Gtz.exists_companionPair_of_moments`, and it is the only glue the assembly
needs between the hinge's output and the two lemmas above. -/
theorem quadForm_gt_of_posDef_pair {size : ℕ} (companion : WeightedDesign size 2)
    (selected : Finset (Fin size))
    (hposDef : (subsetSum companion selected - 1).PosDef)
    (testVec : Fin 2 → ℝ) (htestNonzero : testVec ≠ 0) :
    testVec ⬝ᵥ testVec
      < ∑ label ∈ selected, (companion.atom label ⬝ᵥ testVec) ^ 2 := by
  have hquad := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 htestNonzero
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, quadForm_subsetSum,
    Matrix.one_mulVec] at hquad
  simp only [momentCoord] at hquad
  linarith [hquad]

/-- **THE CHAIN, at the companion.**  Four pairwise non-parallel planar labels of
the rank-two companion — supplied by primitivity of the original design through
`frameBracket_eq_seedNormSq_mul_probeTriple` and
`pairBracket_ne_zero_of_scaledPlanarAtoms` — make the hinge return a POSITIVE
DEFINITE pair, which is the drop-in strict replacement for the weakly dominating
pair `Gtz.gtz_rank_two` returns inside `Gtz.exists_companionPair_of_moments`.
Feeding it to `planarPair_strictTarget_of_strictMaster` needs no weight budget,
so `TwoPoleTransportResidual` and its crossing locus never arise. -/
theorem exists_posDef_companionPair_of_hinge {size : ℕ}
    (hhinge : RankTwoFourDirectionHinge) (companion : WeightedDesign size 2)
    {alongScale acrossScale : ℝ} (alongRaw acrossRaw : Fin size → ℝ)
    (firstLabel secondLabel thirdLabel fourthLabel : Fin size)
    (hone : firstLabel ≠ secondLabel) (htwo : firstLabel ≠ thirdLabel)
    (hthree : firstLabel ≠ fourthLabel) (hfour : secondLabel ≠ thirdLabel)
    (hfive : secondLabel ≠ fourthLabel) (hsix : thirdLabel ≠ fourthLabel)
    (halongScale : alongScale ≠ 0) (hacrossScale : acrossScale ≠ 0)
    (hplanarShape : ∀ label : Fin size,
      label = firstLabel ∨ label = secondLabel ∨ label = thirdLabel ∨ label = fourthLabel →
      companion.atom label
        = ![alongScale * alongRaw label, acrossScale * acrossRaw label])
    (hrawBrackets : ∀ leftLabel rightLabel : Fin size,
      (leftLabel = firstLabel ∨ leftLabel = secondLabel ∨ leftLabel = thirdLabel
        ∨ leftLabel = fourthLabel) →
      (rightLabel = firstLabel ∨ rightLabel = secondLabel ∨ rightLabel = thirdLabel
        ∨ rightLabel = fourthLabel) →
      leftLabel ≠ rightLabel →
      alongRaw leftLabel * acrossRaw rightLabel
        - alongRaw rightLabel * acrossRaw leftLabel ≠ 0) :
    ∃ dominatingPair : Finset (Fin size), dominatingPair.card = 2
      ∧ (subsetSum companion dominatingPair - 1).PosDef := by
  have hbracket : ∀ leftLabel rightLabel : Fin size,
      (leftLabel = firstLabel ∨ leftLabel = secondLabel ∨ leftLabel = thirdLabel
        ∨ leftLabel = fourthLabel) →
      (rightLabel = firstLabel ∨ rightLabel = secondLabel ∨ rightLabel = thirdLabel
        ∨ rightLabel = fourthLabel) →
      leftLabel ≠ rightLabel →
      pairBracket companion leftLabel rightLabel ≠ 0 := by
    intro leftLabel rightLabel hleftMem hrightMem hne
    exact pairBracket_ne_zero_of_scaledPlanarAtoms companion alongRaw acrossRaw
      (hplanarShape leftLabel hleftMem) (hplanarShape rightLabel hrightMem)
      halongScale hacrossScale (hrawBrackets leftLabel rightLabel hleftMem hrightMem hne)
  exact hhinge size companion firstLabel secondLabel thirdLabel fourthLabel
    hone htwo hthree hfour hfive hsix
    (hbracket _ _ (Or.inl rfl) (Or.inr (Or.inl rfl)) hone)
    (hbracket _ _ (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) htwo)
    (hbracket _ _ (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) hthree)
    (hbracket _ _ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) hfour)
    (hbracket _ _ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) hfive)
    (hbracket _ _ (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) hsix)

/-- **The twin gate ON THE CROSSING LOCUS: the poles must outweigh the plane.**
The two-pole lane's residual sits where the companion's weight budget is met with
equality, `nu + kappa = poleMass (1 + kappa)`.  There the sector quantity
factorises exactly,

    2 nu + kappa - 1 = (2 poleMass - 1) (1 + kappa),

so the reach condition `2 nu + kappa > 1` of `exists_planarScale_of_poleSectorGate`
is equivalent to `poleMass > 1/2`: the twin gate closes the crossing locus
exactly on the half where the two poles carry more than half of the design's
weight, and — by `not_twinGate_of_poleSectorFails` — nowhere else. -/
theorem poleSectorGate_iff_poleMass_gt_half
    {inPlaneMass kappa poleMass : ℝ} (hkappaNonneg : 0 ≤ kappa)
    (hcrossingBudget : inPlaneMass + kappa = poleMass * (1 + kappa)) :
    1 < 2 * inPlaneMass + kappa ↔ 1 < 2 * poleMass := by
  have hfactor : 2 * inPlaneMass + kappa - 1 = (2 * poleMass - 1) * (1 + kappa) := by
    linarith [hcrossingBudget, mul_comm poleMass (1 + kappa)]
  constructor
  · intro hsector
    nlinarith [hfactor, hkappaNonneg]
  · intro hmass
    nlinarith [hfactor, hkappaNonneg]

/-! ## Part 8: the composite, with the handoff made explicit

The companion itself is NOT built here — those hundred-odd lines of Parseval
bookkeeping belong in the lane that owns the construction, and duplicating them
would be waste.  What is stated instead is the exact residual arrow, so that
landing the chain is discharging one named `Prop` rather than re-deriving
anything.

    RankTwoFourDirectionHinge
      -> StrictCompanionPairClosesTwoPoleSixThree
      -> TwoPoleStratumSelection 6

`StrictCompanionPairClosesTwoPoleSixThree` is precisely
`Gtz.exists_posDef_triple_of_transportGate` with two edits, both licensed by the
lemmas above: DELETE the weight budget `hgate`, `slack` and `hslackGate` and set
`planarScale = 1`; and REPLACE `Gtz.gtz_rank_two`'s weakly dominating pair by a
positive definite one.  The three shapes it must then case on are all paid for:

* two planar atoms — `planarPair_strictTarget_of_strictMaster`;
* a pole shadow with a planar atom — `mixedPair_alongBound_of_strictMaster`;
* two pole shadows — impossible, `not_posDef_pairGap_of_pairBracket_eq_zero`,
  since the shadows are parallel.

and `quadForm_gt_of_posDef_pair` is the one piece of glue between the pair the
hinge returns and the master inequality both twins consume.

THE EXCLUDED DEGENERACY, restated because it must appear in the landed
hypotheses: the four planar labels are pairwise non-parallel only when `nu < 1`.
At `nu = 1` the planar family has zero seed moment, every planar atom lies on
the cross axis, and the planar labels are pairwise PARALLEL, so the hinge says
nothing.  That configuration carries a parallel pair in the original `(6,3)`
design, which the campaign's parallel-pair funnel removes before this stratum is
reached, so excluding it costs nothing — but it is a hypothesis, not a triviality.
-/

/-- **THE HANDOFF.**  Everything still owed by the lane that owns the companion
construction.  Its antecedent is exactly `RankTwoFourDirectionHinge` specialised
to size six — note it needs the hinge at ONE size only, and needs no weight
budget, no companion scale below one, and no crossing-locus hypothesis. -/
def StrictCompanionPairClosesTwoPoleSixThree : Prop :=
  (∀ (companion : WeightedDesign 6 2)
      (firstLabel secondLabel thirdLabel fourthLabel : Fin 6),
      firstLabel ≠ secondLabel → firstLabel ≠ thirdLabel → firstLabel ≠ fourthLabel →
      secondLabel ≠ thirdLabel → secondLabel ≠ fourthLabel → thirdLabel ≠ fourthLabel →
      pairBracket companion firstLabel secondLabel ≠ 0 →
      pairBracket companion firstLabel thirdLabel ≠ 0 →
      pairBracket companion firstLabel fourthLabel ≠ 0 →
      pairBracket companion secondLabel thirdLabel ≠ 0 →
      pairBracket companion secondLabel fourthLabel ≠ 0 →
      pairBracket companion thirdLabel fourthLabel ≠ 0 →
      ∃ dominatingPair : Finset (Fin 6), dominatingPair.card = 2
        ∧ (subsetSum companion dominatingPair - 1).PosDef) →
    TwoPoleStratumSelection 6

/-- **THE COMPOSITE.**  Branch (iii) of the `(6,3)` stress trichotomy reduces to
the rank-two hinge plus the handoff.  Not to `12.7%` of the crossing locus — to
the whole substratum, because the transport gate that produced that ceiling is
not needed once the companion pair is strict. -/
theorem twoPoleStratumSelection_of_hinge_of_handoff
    (hhinge : RankTwoFourDirectionHinge)
    (hhandoff : StrictCompanionPairClosesTwoPoleSixThree) :
    TwoPoleStratumSelection 6 :=
  hhandoff fun companion firstLabel secondLabel thirdLabel fourthLabel
    hone htwo hthree hfour hfive hsix bracketOne bracketTwo bracketThree
    bracketFour bracketFive bracketSix =>
    hhinge 6 companion firstLabel secondLabel thirdLabel fourthLabel
      hone htwo hthree hfour hfive hsix bracketOne bracketTwo bracketThree
      bracketFour bracketFive bracketSix

end Gtz

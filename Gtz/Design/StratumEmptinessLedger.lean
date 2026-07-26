/-
# The primitive-tight stratum ledger: what is discharged, what the residual is,
# and the leverage floor that narrows every open entry

`Gtz.Design.PrimitiveTightClassification` reduces the campaign's one
nature-facing gap — the HINGE at `(6,3)` and `(7,3)` — to a finite ledger of
per-matroid emptiness statements, THIRTY-TWO isomorphism classes (nine at six
points, twenty-three at seven).  This file does three things to that ledger and
claims nothing beyond them.

1. It records the discharged entries as a STRUCTURAL peel rather than a list of
   names: `hingeHoldsAtSize_of_residualLedger` and its size-seven sibling take a
   complete enumeration and ask tie-freeness only of the patterns that are
   neither a near pencil nor a Fano.  So the residual obligation the campaign
   owes is exactly the open classes, and no bookkeeping step stands between the
   discharged ones and the hinge.
2. It proves a LEVERAGE FLOOR: at `(6,3)`, unconditionally, every atom of a tie
   has `|g_c|^2 >= 1`.  Hence `StratumIsTieFreeAmongHeavy` — tie-freeness asked
   only of designs all of whose atoms are heavy — already implies
   `StratumIsTieFree` at size six.  That strictly shrinks the semialgebraic
   system every one of the open entries has to solve, and it is not a
   criticality argument: it runs through the landed `GtzWeighted 5 3`.
3. It sharpens the repo's light-atom deflation from WEAK to STRICT domination,
   which is what the floor is extracted from, and keeps the quantitative gap
   bound the weak form discards.

## The gap bound, and why the floor follows

Fix a design of size `m + 1` and a label `d` whose SHARE `t_d |g_d|^2` is
strictly below one.  Whitening the surviving atoms against
`P = I - t_d g_d g_d^T` produces a design of size `m`
(`Gtz.deflatedDesign`), and `GtzWeighted m k` hands back a dominating subset
`C` of the survivors.  Pulling the domination back through the congruence gives
not merely `S_C >= I` but the sharp

  (1 - t_d) (S_C - I)  >=  t_d (I - g_d g_d^T)     (Loewner, division-free)

— `exists_deflatedGapBound`.  The right-hand side is positive definite exactly
when `|g_d|^2 < 1`, so a strictly light atom yields a STRICTLY dominating subset
(`exists_posDef_of_lightAtom`), and a tie therefore has no strictly light atom
(`leverage_one_le_of_isTie`).  Even when `|g_d|^2 > 1` the bound still says the
gap is positive definite on the plane orthogonal to `g_d` with margin
`t_d/(1 - t_d)` — `posDef_on_orthogonal_of_deflatedGapBound`.

The floor is UNCONDITIONAL at size six because the input is `GtzWeighted 5 3`
(`Gtz.gtzWeighted_of_le_five`).  At size seven the same argument needs
`GtzWeighted 6 3`, which is open, so every size-seven statement here carries it
as a named hypothesis and none of them is used elsewhere.

## PROVED here, kernel-checked, unconditional

* `posDef_one_sub_atomMatrix_of_leverage_lt_one` — `I - g g^T` is positive
  definite exactly at a strictly light atom.  Rides
  `Gtz.posDef_sub_vecMulVec_iff` at `N = I`.
* **`exists_deflatedGapBound`** — the sharp deflation transport, stated
  division-free.  The subset it returns AVOIDS the deflated label.  Its
  whitening step consumes the shipped
  `Gtz.posDef_one_sub_smul_atomMatrix_of_share_lt_one`
  (`Gtz.Reduction.SplitTransfer`) — the pivot `I - t g g^T` is positive definite
  when the SHARE `t |g|^2` is below one, which is weaker than lightness and fails
  exactly at a near-pencil pole, where the share is one
  (`Gtz.soleOffPlane_share_eq_one`).
* `posDef_on_orthogonal_of_deflatedGapBound` — the two-dimensional half of the
  bound, valid at every label whatever its leverage.
* **`exists_posDef_of_lightAtom`**, `not_isTie_of_lightAtom` — the strict
  upgrade of `Gtz.dominating_of_light_atom`, whose conclusion is only weak
  domination and so cannot exclude a tie.
* **`leverage_one_le_of_isTie`** and **`leverage_one_le_of_isTie_sixThree`** —
  the leverage floor, the second unconditional at `(6,3)`.
  `leverage_one_le_of_isTie_fourThree` is the same statement one rung down.
* `StratumIsTieFreeAmongHeavy`, `stratumIsTieFreeAmongHeavy_of_stratumIsTieFree`,
  **`stratumIsTieFree_of_amongHeavy_sixThree`** — the narrowed per-class
  obligation and the reduction that makes it sufficient at size six.
  `stratumIsTieFree_of_amongHeavy_sevenThree` is the size-seven form and carries
  `GtzWeighted 6 3`.
* `IsRelabelOf`, `isRelabelOf_refl`, `stratumIsTieFree_of_isRelabelOf` — the
  up-to-relabelling vocabulary, riding the landed
  `Gtz.stratumIsTieFree_comp_relabel`.
* `IsNearPencilClass`, `IsFanoClass`, `stratumIsTieFree_of_isNearPencilClass`,
  `stratumIsTieFree_of_isFanoClass` — the three discharged entries as
  recognizers on patterns.  `nearPencilLinePattern_comp_relabel` and
  `isNearPencilClass_iff_exists_pole` record that the near-pencil family is
  already closed under relabelling, so that entry needs no transport at all.
* `isPrimitiveDesign_iff_not_hasParallelPair` — the bridge the classification
  header says a wiring module needs, exercised rather than described.  Because
  this file imports `Gtz.Reduction.SplitTransfer`, every assembly below concludes
  `Gtz.HingeHoldsAtSize size 3` ON THE NOSE rather than its body written out.
* **`hingeHoldsAtSize_of_residualLedger`**,
  **`hingeHoldsAtSize_of_residualLedger_sevenThree`**,
  **`hingeHoldsAtSize_of_heavyResidualLedger_sixThree`**,
  `hingeHoldsAtSize_of_heavyResidualLedger_sevenThree` — the assemblies.  The
  last two are the sharpest honest form: the hinge at six points follows from a
  complete enumeration plus tie-freeness of the non-near-pencil classes RESTRICTED
  to all-heavy designs.
* `not_isNearPencilClass_lineFree`, `tetraDesign_forall_leverage_one_le`,
  `diamondDesign_forall_leverage_one_le` — the controls.  The first shows the
  peel is not secretly everything: the line-free stratum `U(3,size)` survives it
  at every size `>= 4`, so `U(3,6)` and `U(3,7)` are still owed.  The other two
  show the heavy restriction does not throw the phenomenon away: the `(4,3)`
  tetrahedron tie and the `(5,3)` diamond tie are both all-heavy, so
  `StratumIsTieFreeAmongHeavy` is a statement about a class of designs that
  genuinely contains ties at the sizes where ties exist.

## What this file does NOT do

It discharges NONE of the twenty-nine open classes.  No entry of the ledger
moves from open to empty here; what moves is the SHAPE of the residual.  In
particular `M(K4)` (`q6m8`) is untouched: its infimum is one, not attained, and
approached along the boundary where one atom's weight and length go to zero
together, so the leverage floor does not reach it — the floor is a necessary
condition on ties, not a positive margin.

No statement here assumes total tie, criticality of the maximum, or any
first-order condition at a tie.  Per `Gtz.Ties.TotalTieCorankOne` a proof through
criticality would prove `GtzWeighted` at the same size and be circular; the only
inputs used are `GtzWeighted` at STRICTLY SMALLER size, which is what makes the
size-six statements unconditional and the size-seven ones honestly hypothetical.

## CITED, not reproved here

* `Gtz.deflatedDesign` and `Gtz.dominating_of_light_atom`
  (`Gtz.Reduction.Deflation`) — the whitening construction and the weak
  light-atom conclusion this file sharpens.  The gap bound below reuses the
  construction verbatim and replaces only the final assembly.
* `Gtz.posDef_one_sub_smul_atomMatrix_of_share_lt_one`, `Gtz.HasParallelPair`,
  `Gtz.HingeHoldsAtSize`, `Gtz.not_hingeHoldsAtSize_five_three`
  (`Gtz.Reduction.SplitTransfer`) — the share-form deflation pivot, the hinge
  predicate, and the fact that it is FALSE one size below.
* `Gtz.gtzWeighted_of_le_five` (`Gtz.Reduction.Reductions`) — weighted GTZ at
  every size at most five, itself resting on the corank-one and corank-two laws.
  This is the sole reason the size-six statements are unconditional.
* `Gtz.stratumIsTieFree_nearPencil` (`Gtz.Design.NearPencilStrictDomination`) —
  the near-pencil entry, at every size and every pole.  An independent
  mechanization of the same class exists at
  `Gtz.stratumIsTieFree_solePoleLinePattern`
  (`Gtz.Design.NearPencilTransport`), by the same rank-two transport with a
  different weight bookkeeping; this file consumes only the first, so the entry
  is doubly certified but singly depended on.
* `Gtz.stratumIsTieFree_fano`, `Gtz.stratumIsTieFree_comp_relabel`,
  `Gtz.hingeHoldsAtSize_of_relabelLedger`, `Gtz.LinePattern`,
  `Gtz.HasLinePattern`, `Gtz.StratumIsTieFree`,
  `Gtz.PatternListIsCompleteUpToRelabel` (`Gtz.Design.PrimitiveTightClassification`).
* `Gtz.tetraDesign_isTie` (`Gtz.Ties.TetrahedronCertifiedTie`),
  `Gtz.diamondDesign_isTie` (`Gtz.Design.DiamondPrimitive`) — the two ties below
  the hinge, used only as controls.
* `Gtz.posDef_sub_vecMulVec_iff` (`Gtz.LinAlg.SchurRankOne`),
  `Gtz.posSemidef_congr_right` / `Gtz.exists_congruence_to_one`
  (`Gtz.LinAlg.PsdKit`), `Gtz.weight_lt_one` / `Gtz.sum_weighted_leverage`
  (`Gtz.Core.Sanity`), `Gtz.weighted_leverage_le_one`
  (`Gtz.Design.LeverageBound`).

## MEASURED, outside Lean — the ledger's state, and it is NOT closed

The count after the near-pencil transport landed is THREE of thirty-two
isomorphism classes mechanized and TWENTY-NINE open:

* mechanized: `F7` at seven points (`Gtz.stratumIsTieFree_fano`, one class,
  equivalently thirty labelled strata) and the two near pencils `q6m3` (a
  five-point line among six) and `q7m4` (a six-point line among seven), the
  latter two via `Gtz.stratumIsTieFree_nearPencil`;
* attained and OUTSIDE the hinge: `U(3,4)` at four points and the diamond
  `M(K4 - e)` at five, both already in the repository, which is why the hinge is
  asserted from six points on;
* open: the remaining twenty-nine, six at six points and twenty-three minus one
  at seven.

Two independent exact-rational sweeps agree on the enumeration: class counts
`2, 4, 9, 23` at four through seven points, labelled-stratum counts `352` at six
and `8389` at seven, `|Aut(F7)| = 168` with `7!/168 = 30` labellings.  Beyond
the counts, three findings bear on how the open entries can be attacked, all
measured and none proved here.

* Exact rational realizations exist for all thirty-one non-Fano classes, so
  `F7` is the ONLY class that dies by non-representability over the reals.  There
  is no second free win of that shape at these sizes.
* The complex-emptiness route is DEAD on every realizable class: for each one a
  pair of rational endpoints was exhibited between which `det(S_B - I)` changes
  sign along a segment interior to the open stratum, so the tie-EQUATION variety
  has real points and the ideal does not contain one.  The inequation and
  definiteness half is load-bearing everywhere, exactly as the classification
  file says.
* `M(K4)` has value exactly `1/(1 - eps)` on the family that switches its sixth
  edge on with weight `eps`, confirming that file's `det(S - I)` sequence in exact
  arithmetic; the boundary point is the `(5,3)` diamond tie.  So its infimum is
  inherited from one size down and no argument continuous up to the closure can
  work there.

Naimark duality yields no reduction of the ledger: at six points the involution
fixes six of the nine classes and sends the other three to non-simple matroids,
so there is no dual PAIR to exploit, and at seven points it exports to rank four
and off this rung.  `PatternListIsCompleteUpToRelabel` — the enumeration itself
— remains unproved in Lean; both assemblies below take it as a named hypothesis
and neither pretends otherwise.

No tie was found on any class the ledger calls empty.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.Design.LeverageBound
import Gtz.Design.DiamondPrimitive
import Gtz.Design.PrimitiveTightClassification
import Gtz.Design.NearPencilStrictDomination
import Gtz.Reduction.Deflation
import Gtz.Reduction.Reductions
import Gtz.Reduction.SplitTransfer
import Gtz.Ties.TetrahedronCertifiedTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The two rank-one definiteness pivots

Deflating at a label needs its pivot `I - t g g^T` positive definite, and
reading strictness back off the transported gap needs `I - g g^T` positive
definite.  The two conditions are the share and the leverage falling strictly
below one, and they are genuinely different: at a near-pencil pole the share is
exactly one while the leverage is `1/t > 1`. -/

/-- **A strictly light atom has a positive-definite complement.**  `I - g g^T`
is positive definite exactly when `|g|^2 < 1`; this is the summand that turns a
transported weak domination into a strict one. -/
theorem posDef_one_sub_atomMatrix_of_leverage_lt_one (atomVec : Fin k → ℝ)
    (hlight : leverageOf atomVec < 1) :
    ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix atomVec).PosDef := by
  rw [atomMatrix, posDef_sub_vecMulVec_iff _ Matrix.PosDef.one, inv_one,
    Matrix.one_mulVec, ← leverageOf_eq_dotProduct]
  exact hlight

/-! ## The sharp deflation transport

`Gtz.dominating_of_light_atom` throws away the quantitative content of the
pullback: its conclusion is `S_C >= I`, which a tie already satisfies, so it
cannot exclude one.  The pullback actually proves a Loewner INEQUALITY between
the gap and the deflated atom's complement, and that inequality is what the rest
of this file runs on.  Stated multiplied through by `1 - t_d` so no division
appears. -/

/-- **The deflated gap bound.**  Whitening away the label `dropLabel`, whose
share is below one, and importing a dominating subset of the smaller design
yields a subset `selected` of the SURVIVORS with

  `(1 - t_d) (S_selected - I) >= t_d (I - g_d g_d^T)` .

Both the membership statement (`dropLabel` is absent) and the Loewner bound are
new relative to `Gtz.dominating_of_light_atom`, whose conclusion is the weaker
`S_selected >= I` and only under the stronger hypothesis `|g_d|^2 <= 1`. -/
theorem exists_deflatedGapBound (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m k) (dropLabel : Fin (m + 1))
    (hshare : D.weight dropLabel * leverageOf (D.atom dropLabel) < 1) :
    ∃ selected : Finset (Fin (m + 1)), selected.card = k ∧ dropLabel ∉ selected ∧
      (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
        - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))).PosSemidef := by
  classical
  have hweightPos := D.weight_pos dropLabel
  have hweightLtOne : D.weight dropLabel < 1 := weight_lt_one D (by omega) dropLabel
  have hSurvivingMass : (0 : ℝ) < 1 - D.weight dropLabel := by linarith
  have hPivotPosDef :
      ((1 : Matrix (Fin k) (Fin k) ℝ) - D.weight dropLabel • atomMatrix (D.atom dropLabel)).PosDef :=
    posDef_one_sub_smul_atomMatrix_of_share_lt_one hweightPos hshare
  obtain ⟨whitener, hwhitenerUnit, hwhitenerPivot⟩ := exists_congruence_to_one hPivotPosDef
  obtain ⟨smallerSubset, hsmallerCard, hsmallerDominates⟩ :=
    hsmaller (deflatedDesign D dropLabel whitener hSurvivingMass hwhitenerPivot)
  have hEmbeddingInjective : Function.Injective dropLabel.succAbove :=
    Fin.succAbove_right_injective
  refine ⟨smallerSubset.image dropLabel.succAbove, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hEmbeddingInjective, hsmallerCard]
  · intro hMem
    obtain ⟨survivor, _, hsurvivor⟩ := Finset.mem_image.mp hMem
    exact Fin.succAbove_ne dropLabel survivor hsurvivor
  · -- the deflated domination, in explicit-sum form
    have hDeflatedDominates : ((∑ survivor ∈ smallerSubset,
        atomMatrix (Real.sqrt (1 - D.weight dropLabel)
          • (whitenerᵀ *ᵥ D.atom (dropLabel.succAbove survivor)))) - 1).PosSemidef :=
      hsmallerDominates
    -- that sum is the congruated, scaled primal subset sum
    have hScaledSum : ∑ survivor ∈ smallerSubset,
          atomMatrix (Real.sqrt (1 - D.weight dropLabel)
            • (whitenerᵀ *ᵥ D.atom (dropLabel.succAbove survivor)))
        = whitenerᵀ * (((1 : ℝ) - D.weight dropLabel)
            • subsetSum D (smallerSubset.image dropLabel.succAbove)) * whitener := by
      rw [subsetSum, Finset.sum_image fun a _ b _ hab => hEmbeddingInjective hab,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul,
        Finset.smul_sum]
      exact Finset.sum_congr rfl fun survivor _ => by
        rw [atomMatrix_smul, Real.sq_sqrt hSurvivingMass.le, transpose_mul_atomMatrix_mul]
    have hShiftedSymmetric : ((((1 : ℝ) - D.weight dropLabel)
            • subsetSum D (smallerSubset.image dropLabel.succAbove))
          - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel)))ᵀ
        = (((1 : ℝ) - D.weight dropLabel)
            • subsetSum D (smallerSubset.image dropLabel.succAbove))
          - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel)) := by
      rw [Matrix.transpose_sub, Matrix.transpose_smul, subsetSum_transpose,
        Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
        transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom dropLabel)).1]
    have hShiftedPosSemidef : ((((1 : ℝ) - D.weight dropLabel)
        • subsetSum D (smallerSubset.image dropLabel.succAbove))
        - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel))).PosSemidef := by
      refine (posSemidef_congr_right hShiftedSymmetric hwhitenerUnit).mpr ?_
      have hExpand : whitenerᵀ * ((((1 : ℝ) - D.weight dropLabel)
            • subsetSum D (smallerSubset.image dropLabel.succAbove))
            - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel))) * whitener
          = (∑ survivor ∈ smallerSubset,
              atomMatrix (Real.sqrt (1 - D.weight dropLabel)
                • (whitenerᵀ *ᵥ D.atom (dropLabel.succAbove survivor)))) - 1 := by
        rw [Matrix.mul_sub, Matrix.sub_mul, hwhitenerPivot, ← hScaledSum]
      rw [hExpand]
      exact hDeflatedDominates
    have hRearranged : ((1 : ℝ) - D.weight dropLabel)
          • (subsetSum D (smallerSubset.image dropLabel.succAbove) - 1)
          - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))
        = (((1 : ℝ) - D.weight dropLabel)
            • subsetSum D (smallerSubset.image dropLabel.succAbove))
          - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel)) := by
      module
    rw [hRearranged]
    exact hShiftedPosSemidef

/-- **The gap bound's two-dimensional half.**  Whatever the deflated label's
leverage, the transported gap is strictly positive on every direction orthogonal
to that label's atom, with margin `t_d/(1 - t_d)` after undoing the scaling.  So
a singular direction of the gap must pair nontrivially against `g_d`, which is
the structural content the leverage floor below extracts. -/
theorem posDef_on_orthogonal_of_deflatedGapBound (D : WeightedDesign (m + 1) k)
    (dropLabel : Fin (m + 1)) (selected : Finset (Fin (m + 1)))
    (hbound : (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
      - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))).PosSemidef)
    (hsize : 1 ≤ m) (probeVec : Fin k → ℝ) (hProbeNe : probeVec ≠ 0)
    (hOrthogonal : D.atom dropLabel ⬝ᵥ probeVec = 0) :
    0 < probeVec ⬝ᵥ ((subsetSum D selected - 1) *ᵥ probeVec) := by
  have hweightPos := D.weight_pos dropLabel
  have hweightLtOne : D.weight dropLabel < 1 := weight_lt_one D (by omega) dropLabel
  have hSurvivingMass : (0 : ℝ) < 1 - D.weight dropLabel := by linarith
  have hProbePos : 0 < probeVec ⬝ᵥ probeVec := dotProduct_self_pos hProbeNe
  have hInnerComplement : probeVec ⬝ᵥ
        (((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom dropLabel)) *ᵥ probeVec)
      = probeVec ⬝ᵥ probeVec := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm probeVec (D.atom dropLabel), hOrthogonal, mul_zero, sub_zero]
  have hBoundForm := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hbound).2 probeVec
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    hInnerComplement] at hBoundForm
  nlinarith [hBoundForm, mul_pos hweightPos hProbePos, hSurvivingMass]

/-! ## Strict light-atom deflation, and the leverage floor at a tie

`Gtz.dominating_of_light_atom` concludes weak domination from `|g_d|^2 <= 1`.
Under the strict hypothesis the deflated atom's complement is positive definite,
so the gap bound upgrades to positive definiteness and the design cannot be a
tie.  Contrapositive: at a tie every atom is heavy. -/

/-- **Strictly light means strictly dominating.**  An atom of leverage below one
forces a `k`-subset of the OTHER labels whose gap is positive definite, granted
weighted GTZ one size down.  Strictly stronger than
`Gtz.dominating_of_light_atom`, and the strictness is what excludes a tie. -/
theorem exists_posDef_of_lightAtom (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m k) (dropLabel : Fin (m + 1))
    (hlight : leverageOf (D.atom dropLabel) < 1) :
    ∃ selected : Finset (Fin (m + 1)), selected.card = k ∧ dropLabel ∉ selected ∧
      (subsetSum D selected - 1).PosDef := by
  have hweightPos := D.weight_pos dropLabel
  have hweightLtOne : D.weight dropLabel < 1 := weight_lt_one D (by omega) dropLabel
  have hSurvivingMass : (0 : ℝ) < 1 - D.weight dropLabel := by linarith
  have hLeverageNonneg : 0 ≤ leverageOf (D.atom dropLabel) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hshare : D.weight dropLabel * leverageOf (D.atom dropLabel) < 1 := by
    nlinarith [hweightPos, hweightLtOne, hlight, hLeverageNonneg]
  obtain ⟨selected, hcard, hAvoidsDrop, hbound⟩ :=
    exists_deflatedGapBound D hsize hsmaller dropLabel hshare
  refine ⟨selected, hcard, hAvoidsDrop, ?_⟩
  have hComplementPosDef :
      (D.weight dropLabel • ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom dropLabel))).PosDef :=
    (posDef_one_sub_atomMatrix_of_leverage_lt_one _ hlight).smul hweightPos
  have hScaledGapPosDef :
      (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)).PosDef := by
    have hSplit : ((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
        = D.weight dropLabel • ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom dropLabel))
          + (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
            - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))) := by
      module
    rw [hSplit]
    exact hComplementPosDef.add_posSemidef hbound
  have hUnscale : subsetSum D selected - 1
      = (((1 : ℝ) - D.weight dropLabel)⁻¹)
        • (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)) := by
    rw [smul_smul, inv_mul_cancel₀ hSurvivingMass.ne', one_smul]
  rw [hUnscale]
  exact hScaledGapPosDef.smul (inv_pos.mpr hSurvivingMass)

/-- **A design with a strictly light atom is not a tie.** -/
theorem not_isTie_of_lightAtom (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m k) (dropLabel : Fin (m + 1))
    (hlight : leverageOf (D.atom dropLabel) < 1) : ¬ IsTie D := by
  intro htie
  obtain ⟨selected, hcard, _, hposDef⟩ :=
    exists_posDef_of_lightAtom D hsize hsmaller dropLabel hlight
  exact htie.2 selected hcard hposDef

/-- **The leverage floor at a tie.**  Every atom of a tie has leverage at least
one, granted weighted GTZ one size down.  Combined with the per-atom ceiling
`Gtz.weighted_leverage_le_one` this pins each share into `(t_c, 1]` and each
weight below its own share; combined with `Gtz.sum_weighted_leverage` the shares
still sum to the rank, so the floor constrains a tie without deciding it. -/
theorem leverage_one_le_of_isTie (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m k) (htie : IsTie D) (label : Fin (m + 1)) :
    1 ≤ leverageOf (D.atom label) := by
  by_contra hlight
  exact not_isTie_of_lightAtom D hsize hsmaller label (lt_of_not_ge hlight) htie

/-! ## The floor at the hinge's lower size, unconditionally

At six points the input is `GtzWeighted 5 3`, which is landed, so the floor is a
theorem with no hypothesis.  At seven points the same argument needs
`GtzWeighted 6 3`; that instance is open and appears as a named hypothesis in
every size-seven statement below. -/

/-- **Every `(6,3)` tie is all-heavy**, unconditionally.  The input is
`Gtz.gtzWeighted_of_le_five` at five points, so no open instance is assumed and
no criticality argument is used. -/
theorem leverage_one_le_of_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    (label : Fin 6) : 1 ≤ leverageOf (D.atom label) :=
  leverage_one_le_of_isTie (m := 5) (k := 3) D (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) htie label

/-- **Every `(7,3)` tie is all-heavy**, granted the open `GtzWeighted 6 3`. -/
theorem leverage_one_le_of_isTie_sevenThree (hsixThree : GtzWeighted 6 3)
    (D : WeightedDesign 7 3) (htie : IsTie D) (label : Fin 7) :
    1 ≤ leverageOf (D.atom label) :=
  leverage_one_le_of_isTie (m := 6) (k := 3) D (by norm_num) hsixThree htie label

/-- **Every `(4,3)` tie is all-heavy** — the same statement one rung below the
hinge, where a tie provably exists (`Gtz.tetraDesign_isTie`).  Kept so the floor
is visibly a statement about an inhabited situation. -/
theorem leverage_one_le_of_isTie_fourThree (D : WeightedDesign 4 3) (htie : IsTie D)
    (label : Fin 4) : 1 ≤ leverageOf (D.atom label) :=
  leverage_one_le_of_isTie (m := 3) (k := 3) D (by norm_num)
    (gtzWeighted_of_le_five 3 3 (by norm_num) (by norm_num)) htie label

/-- **Every `(5,3)` tie is all-heavy** — the diamond's rung. -/
theorem leverage_one_le_of_isTie_fiveThree (D : WeightedDesign 5 3) (htie : IsTie D)
    (label : Fin 5) : 1 ≤ leverageOf (D.atom label) :=
  leverage_one_le_of_isTie (m := 4) (k := 3) D (by norm_num)
    (gtzWeighted_of_le_five 4 3 (by norm_num) (by norm_num)) htie label

/-! ## The narrowed per-class obligation

A ledger entry asks tie-freeness of a whole stratum.  The floor lets it ask only
of the ALL-HEAVY designs on that stratum, which is a strictly smaller
semialgebraic set: the inequalities `|g_c|^2 >= 1` may be added to every open
entry's system for free.  The reduction is unconditional at six points. -/

/-- Tie-freeness asked only of the designs whose every atom is heavy.  Weaker
than `Gtz.StratumIsTieFree`, and by the floor equivalent to it at the hinge's
sizes. -/
def StratumIsTieFreeAmongHeavy {size : ℕ} (pattern : LinePattern size) : Prop :=
  ∀ D : WeightedDesign size 3, HasLinePattern D pattern →
    (∀ label : Fin size, 1 ≤ leverageOf (D.atom label)) → ¬ IsTie D

/-- The narrowed obligation is genuinely weaker: full tie-freeness implies it. -/
theorem stratumIsTieFreeAmongHeavy_of_stratumIsTieFree {size : ℕ}
    {pattern : LinePattern size} (hfree : StratumIsTieFree pattern) :
    StratumIsTieFreeAmongHeavy pattern :=
  fun D hpattern _ => hfree D hpattern

/-- **The narrowed obligation suffices**, at any size one above a settled one. -/
theorem stratumIsTieFree_of_amongHeavy {m : ℕ} (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m 3) {pattern : LinePattern (m + 1)}
    (hheavyFree : StratumIsTieFreeAmongHeavy pattern) : StratumIsTieFree pattern :=
  fun D hpattern htie =>
    hheavyFree D hpattern (fun label => leverage_one_le_of_isTie D hsize hsmaller htie label) htie

/-- **At six points the narrowing is free.**  An open ledger entry at `(6,3)` may
assume every atom heavy with no extra hypothesis anywhere. -/
theorem stratumIsTieFree_of_amongHeavy_sixThree {pattern : LinePattern 6}
    (hheavyFree : StratumIsTieFreeAmongHeavy pattern) : StratumIsTieFree pattern :=
  stratumIsTieFree_of_amongHeavy (m := 5) (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) hheavyFree

/-- The size-seven form of the narrowing, which needs the open `GtzWeighted 6 3`. -/
theorem stratumIsTieFree_of_amongHeavy_sevenThree (hsixThree : GtzWeighted 6 3)
    {pattern : LinePattern 7} (hheavyFree : StratumIsTieFreeAmongHeavy pattern) :
    StratumIsTieFree pattern :=
  stratumIsTieFree_of_amongHeavy (m := 6) (by norm_num) hsixThree hheavyFree

/-! ## The discharged entries as recognizers

A ledger is a list of patterns, and the discharged classes should be peeled off
it structurally rather than matched against three names by hand.  `IsRelabelOf`
names "same stratum up to relabelling"; the two recognizers below are the near
pencil and the Fano, and each carries its own tie-freeness. -/

/-- One pattern is a relabelling of another.  `Gtz.stratumIsTieFree_comp_relabel`
is exactly what makes tie-freeness invariant under this. -/
def IsRelabelOf {size : ℕ} (pattern basePattern : LinePattern size) : Prop :=
  ∃ relabel : Equiv.Perm (Fin size),
    pattern = fun leftLabel midLabel rightLabel =>
      basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)

/-- Relabelling-equivalence is reflexive, witnessed by the identity. -/
theorem isRelabelOf_refl {size : ℕ} (pattern : LinePattern size) :
    IsRelabelOf pattern pattern :=
  ⟨Equiv.refl _, rfl⟩

/-- **Tie-freeness transports along a relabelling.** -/
theorem stratumIsTieFree_of_isRelabelOf {size : ℕ} {pattern basePattern : LinePattern size}
    (hrelabel : IsRelabelOf pattern basePattern) (hbaseFree : StratumIsTieFree basePattern) :
    StratumIsTieFree pattern := by
  obtain ⟨relabel, hpattern⟩ := hrelabel
  rw [hpattern]
  exact stratumIsTieFree_comp_relabel basePattern relabel hbaseFree

/-- The near-pencil classes: some relabelling of some pole's near pencil. -/
def IsNearPencilClass {size : ℕ} (pattern : LinePattern size) : Prop :=
  ∃ poleLabel : Fin size, IsRelabelOf pattern (nearPencilLinePattern poleLabel)

/-- The Fano class at seven points. -/
def IsFanoClass (pattern : LinePattern 7) : Prop := IsRelabelOf pattern fanoLinePattern

/-- **A relabelled near pencil is a near pencil**, at the moved pole.  So the
near-pencil family needs no relabelling closure: recognizing it up to
relabelling is the same as recognizing it on the nose. -/
theorem nearPencilLinePattern_comp_relabel {size : ℕ} (poleLabel : Fin size)
    (relabel : Equiv.Perm (Fin size)) :
    (fun leftLabel midLabel rightLabel =>
        nearPencilLinePattern poleLabel (relabel leftLabel) (relabel midLabel)
          (relabel rightLabel))
      = nearPencilLinePattern (relabel.symm poleLabel) := by
  funext leftLabel midLabel rightLabel
  have hmoved : ∀ label : Fin size,
      (relabel label ≠ poleLabel) = (label ≠ relabel.symm poleLabel) := by
    intro label
    exact propext (not_congr (relabel.apply_eq_iff_eq_symm_apply))
  rw [nearPencilLinePattern, nearPencilLinePattern, hmoved, hmoved, hmoved]

/-- **The near-pencil recognizer is pole-matching on the nose.** -/
theorem isNearPencilClass_iff_exists_pole {size : ℕ} (pattern : LinePattern size) :
    IsNearPencilClass pattern ↔ ∃ poleLabel : Fin size,
      pattern = nearPencilLinePattern poleLabel := by
  constructor
  · rintro ⟨poleLabel, relabel, hpattern⟩
    exact ⟨relabel.symm poleLabel, by
      rw [hpattern, nearPencilLinePattern_comp_relabel]⟩
  · rintro ⟨poleLabel, hpattern⟩
    exact ⟨poleLabel, hpattern ▸ isRelabelOf_refl _⟩

/-- **The near-pencil entries are discharged**, at every size at least three and
whatever the pole.  Rides `Gtz.stratumIsTieFree_nearPencil`, whose proof is the
rank-two transport. -/
theorem stratumIsTieFree_of_isNearPencilClass {size : ℕ} (hsize : 3 ≤ size)
    {pattern : LinePattern size} (hclass : IsNearPencilClass pattern) :
    StratumIsTieFree pattern := by
  obtain ⟨poleLabel, hrelabel⟩ := hclass
  exact stratumIsTieFree_of_isRelabelOf hrelabel (stratumIsTieFree_nearPencil hsize poleLabel)

/-- **The Fano entry is discharged.**  Rides `Gtz.stratumIsTieFree_fano`, whose
proof is that no seven vectors of three-space realize the Fano plane. -/
theorem stratumIsTieFree_of_isFanoClass {pattern : LinePattern 7}
    (hclass : IsFanoClass pattern) : StratumIsTieFree pattern :=
  stratumIsTieFree_of_isRelabelOf hclass stratumIsTieFree_fano

/-! ## The residual assemblies

Each theorem here is `Gtz.hingeHoldsAtSize_of_relabelLedger` with the discharged
recognizers already discharged, so the hypothesis it still takes is exactly the
residual obligation.  Nothing is claimed about whether the enumeration
hypothesis holds: `Gtz.PatternListIsCompleteUpToRelabel` is unproved in Lean and
is passed through untouched.

The conclusion is `Gtz.HingeHoldsAtSize size 3` on the nose.  The classification
file writes the hinge's body out because it does not import
`Gtz.Reduction.SplitTransfer`; this file does, so the correspondence its header
describes as definitional is exercised rather than described —
`isPrimitiveDesign_iff_not_hasParallelPair` records the other half of that
dictionary explicitly. -/

/-- **Primitivity is exactly the absence of a parallel pair.**  The two
predicates are the same statement with the negation pushed in;
`Gtz.IsPrimitiveDesign` lives in the classification file and
`Gtz.HasParallelPair` in the split-transfer file, and this is the bridge the
classification header says a wiring module needs. -/
theorem isPrimitiveDesign_iff_not_hasParallelPair {size rank : ℕ}
    (D : WeightedDesign size rank) : IsPrimitiveDesign D ↔ ¬ HasParallelPair D := by
  constructor
  · rintro hprimitive ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
    exact hprimitive keptLabel dropLabel ratio hdistinct hparallel
  · intro hnoParallelPair keptLabel dropLabel ratio hdistinct hparallel
    exact hnoParallelPair ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩

/-- **The hinge from the residual ledger.**  A complete enumeration up to
relabelling plus tie-freeness of every listed class that is NOT a near pencil
gives `Gtz.HingeHoldsAtSize size 3`.  The near-pencil entries are paid by
`stratumIsTieFree_of_isNearPencilClass`.

At `size = 4` and `size = 5` the conclusion is FALSE
(`Gtz.not_hingeHoldsAtSize_five_three`; `Gtz.tetraDesign_isTie` and
`Gtz.diamondDesign_isTie` are primitive ties), so any use must supply enumeration
data that genuinely fails there. -/
theorem hingeHoldsAtSize_of_residualLedger {size : ℕ} (hsize : 3 ≤ size)
    (patterns : List (LinePattern size))
    (hcomplete : PatternListIsCompleteUpToRelabel size patterns)
    (hresidual : ∀ pattern ∈ patterns, ¬ IsNearPencilClass pattern →
      StratumIsTieFree pattern) :
    HingeHoldsAtSize size 3 := by
  classical
  refine hingeHoldsAtSize_of_relabelLedger patterns hcomplete fun pattern hmem => ?_
  by_cases hnearPencil : IsNearPencilClass pattern
  · exact stratumIsTieFree_of_isNearPencilClass hsize hnearPencil
  · exact hresidual pattern hmem hnearPencil

/-- **The hinge at seven points from the residual ledger**, with BOTH discharged
recognizers peeled: the residual is asked only of the classes that are neither a
near pencil nor a Fano.  Against the isomorphism-class ledger that leaves
twenty-one of the twenty-three entries at seven points. -/
theorem hingeHoldsAtSize_of_residualLedger_sevenThree
    (patterns : List (LinePattern 7))
    (hcomplete : PatternListIsCompleteUpToRelabel 7 patterns)
    (hresidual : ∀ pattern ∈ patterns, ¬ IsNearPencilClass pattern →
      ¬ IsFanoClass pattern → StratumIsTieFree pattern) :
    HingeHoldsAtSize 7 3 := by
  classical
  refine hingeHoldsAtSize_of_residualLedger (by norm_num) patterns hcomplete
    fun pattern hmem hnearPencil => ?_
  by_cases hfano : IsFanoClass pattern
  · exact stratumIsTieFree_of_isFanoClass hfano
  · exact hresidual pattern hmem hnearPencil hfano

/-- **The sharpest honest form at six points.**  The hinge at `(6,3)` follows
from a complete enumeration plus, for each listed class that is not a near
pencil, tie-freeness RESTRICTED to all-heavy designs.  Both peels are
unconditional: the near pencils by the rank-two transport, the heaviness by
`GtzWeighted 5 3`.  Against the isomorphism-class ledger that leaves eight of the
nine entries at six points, each with the leverage floor already granted. -/
theorem hingeHoldsAtSize_of_heavyResidualLedger_sixThree
    (patterns : List (LinePattern 6))
    (hcomplete : PatternListIsCompleteUpToRelabel 6 patterns)
    (hresidual : ∀ pattern ∈ patterns, ¬ IsNearPencilClass pattern →
      StratumIsTieFreeAmongHeavy pattern) :
    HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_residualLedger (by norm_num) patterns hcomplete
    fun pattern hmem hnearPencil =>
      stratumIsTieFree_of_amongHeavy_sixThree (hresidual pattern hmem hnearPencil)

/-- The same at seven points, with the Fano peeled too and the leverage floor
bought with the open `GtzWeighted 6 3`. -/
theorem hingeHoldsAtSize_of_heavyResidualLedger_sevenThree (hsixThree : GtzWeighted 6 3)
    (patterns : List (LinePattern 7))
    (hcomplete : PatternListIsCompleteUpToRelabel 7 patterns)
    (hresidual : ∀ pattern ∈ patterns, ¬ IsNearPencilClass pattern →
      ¬ IsFanoClass pattern → StratumIsTieFreeAmongHeavy pattern) :
    HingeHoldsAtSize 7 3 :=
  hingeHoldsAtSize_of_residualLedger_sevenThree patterns hcomplete
    fun pattern hmem hnearPencil hfano =>
      stratumIsTieFree_of_amongHeavy_sevenThree hsixThree
        (hresidual pattern hmem hnearPencil hfano)

/-! ## Controls: the peel is not everything, and the narrowing keeps the ties

Two failure modes would make the statements above worthless.  The peel could
accidentally cover the whole ledger, making the residual hypothesis vacuous; and
the heavy restriction could exclude every tie, making
`StratumIsTieFreeAmongHeavy` vacuous.  Both are ruled out here. -/

/-- **The line-free stratum survives the peel.**  At four or more labels the
uniform matroid's pattern — no dependent triple at all — is not a near-pencil
class, because a near pencil at that size has a dependent triple avoiding its
pole.  So `U(3,6)` and `U(3,7)` remain in the residual and the peel is not
secretly total. -/
theorem not_isNearPencilClass_lineFree {size : ℕ} (hsize : 4 ≤ size) :
    ¬ IsNearPencilClass (size := size) (fun _ _ _ => False) := by
  classical
  intro hclass
  obtain ⟨poleLabel, hpattern⟩ := (isNearPencilClass_iff_exists_pole _).mp hclass
  have hcomplement : 3 ≤ ({poleLabel}ᶜ : Finset (Fin size)).card := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    omega
  obtain ⟨witnessTriple, hsubset, hcard⟩ := Finset.exists_subset_card_eq hcomplement
  obtain ⟨leftLabel, midLabel, rightLabel, _, _, _, hshape⟩ := Finset.card_eq_three.mp hcard
  have hoff : ∀ label : Fin size, label ∈ witnessTriple → label ≠ poleLabel := by
    intro label hmem
    simpa only [Finset.mem_compl, Finset.mem_singleton] using hsubset hmem
  have hdependent : nearPencilLinePattern poleLabel leftLabel midLabel rightLabel :=
    ⟨hoff leftLabel (by rw [hshape]; simp), hoff midLabel (by rw [hshape]; simp),
      hoff rightLabel (by rw [hshape]; simp)⟩
  rw [← hpattern] at hdependent
  exact hdependent

/-- **The tetrahedron tie is all-heavy** — the leverage floor realized at the
`(4,3)` tie, so the heavy restriction is not vacuous by excluding every tie. -/
theorem tetraDesign_forall_leverage_one_le (label : Fin 4) :
    1 ≤ leverageOf (tetraDesign.atom label) :=
  leverage_one_le_of_isTie_fourThree tetraDesign tetraDesign_isTie label

/-- **The diamond tie is all-heavy** — the same at the `(5,3)` tie, which is the
primitive one sitting on `M(K4)`'s boundary.  So the leverage floor does not
exclude the very phenomenon the open entries have to survive; it is a necessary
condition on ties, not a margin. -/
theorem diamondDesign_forall_leverage_one_le (label : Fin 5) :
    1 ≤ leverageOf (diamondDesign.atom label) :=
  leverage_one_le_of_isTie_fiveThree diamondDesign diamondDesign_isTie label

/-- **The narrowed obligation is inhabited on both sides at `(4,3)`.**  The
line-free stratum there is NOT tie-free even among heavy designs — the
tetrahedron witnesses it — so `StratumIsTieFreeAmongHeavy` is a genuine
condition and not provable outright at every pattern. -/
theorem not_stratumIsTieFreeAmongHeavy_fourThree_lineFree :
    ¬ StratumIsTieFreeAmongHeavy (size := 4) (fun _ _ _ => False) := fun hheavyFree =>
  hheavyFree tetraDesign tetraDesign_hasUniformLinePattern
    tetraDesign_forall_leverage_one_le tetraDesign_isTie

end Gtz

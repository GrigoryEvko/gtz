/-
PROVENANCE.  Harvested by the phase-4 residual-threading campaign.  An
environment-level census asked the kernel which CLOSED propositions the tree takes
as a hypothesis somewhere without any theorem proving them, and got 77.  Eighteen
reconnaissance lanes chased them and one verification lane re-derived every claim
from shipped anchors without reusing a chase agent's proof.  This file is the
landable residue of that: the canonical names, the bridge lemmas, and the one piece
of genuinely new mathematics the campaign produced.

# Threading the undischarged assumptions

A residual is a proposition the tree ASSUMES but never CONCLUDES.  A census that
indexes theorems by the head constant of their conclusion cannot see most of the
reasons a residual is not really open, and the campaign found four such blind spots.
Each one is a reason a bridge below exists and did not before.

* **An `Iff` bridge is invisible.**  `Gtz.symmetricCovering_iff_discriminantCovering`
  has conclusion head `Iff`, so no amount of searching under head `SymmetricCovering`
  finds it.  Sections 2 and 3 restate every such collapse with the residual on the
  left, which is the form a head index can read.
* **Instantiating a universally quantified residual is invisible.**  Residual
  `∀ rank, 1 ≤ rank → GtzWeighted (rank+3) rank` implies `GtzWeighted 6 3` by
  instantiation, and the converse runs through Naimark duality at size `rank+3`;
  neither arrow is a defeq match against any shipped conclusion.
* **The trivial weakening is invisible.**  A residual of the shape "the target with
  hypotheses added" follows from the target by `fun D _ _ => hcell D`, and no shipped
  theorem records that.  Every narrowing in Section 3 is of that shape.
* **A narrowing concludes the UNDECORATED predicate.**  In a family related by added
  hypotheses — `StratumIsTieFree`, `...AmongHeavy`, `...AtBalancedStress` — every
  narrowing theorem's conclusion carries the WEAKER decoration, so the decorated
  members all score an empty candidate pool.  Section 5 gives that lattice pointwise.

## What is genuinely new here rather than a restatement

Section 1.  **The bordered-slack converse.**
`Gtz/Reduction/StrengthenedInductionHypothesis.lean` asserts in prose (its lines
99-107) that `BorderedSlackLifting rank` is EQUIVALENT to
`(∀ size, GtzWeighted size (rank+1))` and to `LiftingLemma rank`, "because a rank-one
Loewner bound ALREADY forces range membership".  Only the forward arrow shipped.  The
missing step is `Gtz.exists_mulVec_solution_of_rankOneForm_le`: for a symmetric form,
range and kernel meet only at zero (a vector in both is orthogonal to itself),
rank-nullity closes them to a direct sum, and the Loewner bound tested on the kernel
component reads `|kernelPart|⁴ ≤ 0`.  No inner-product-space structure, no orthogonal
projection, no eigenvalues — it stays inside the tree's spectral-theorem-free
`Gtz/LinAlg/PsdKit.lean` discipline.  With it, `hsolves` and `hrate` are never extra
demands, so the strengthened hypothesis was never a strengthening of anything, and the
two equivalences the header asserts become theorems.

## What this file does NOT do

It moves the census, not the frontier.  Every canonical survivor below — `GtzWeighted
6 3`, full weighted GTZ, `GtzWeightedAll 4`, `GtzWeightedAll 5`, `GtzWeighted 8 4`, the
hinge stratum obligation — is open, and nothing here advances any of them.  What it
buys is that the next census counts each obligation once instead of once per phrasing.
-/
import Mathlib
import Gtz.Reduction.StrengthenedInductionHypothesis
import Gtz.Reduction.StressWalk
import Gtz.Reduction.HeavyTraceFrame
import Gtz.Reduction.RankFourWindow
import Gtz.Reduction.AllHeavyMinimiser
import Gtz.Reduction.NaimarkLeverage
import Gtz.Reduction.RankThreeFromSixThree
import Gtz.Reduction.LineCountReduction
import Gtz.Reduction.GenericityReduction
import Gtz.Reduction.ChartPointFactorisation
import Gtz.Reduction.SignClashCoverage
import Gtz.Reduction.WeightFloorWindow
import Gtz.Reduction.ConverseBridge
import Gtz.Quantitative.SixThreeCrux
import Gtz.Quantitative.SixThreeExclusionFrontier
import Gtz.Quantitative.SixThreeMinimalityLayer
import Gtz.Quantitative.SixThreeFrontierSharp
import Gtz.Quantitative.SevenThreeCollapse
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Quantitative.PositivstellensatzRankThree
import Gtz.Quantitative.ResidueReduction
import Gtz.Quantitative.DeformationAndCurvature
import Gtz.Quantitative.ChartValueTwoRegime
import Gtz.Quantitative.GlobalMinimumRankThree
import Gtz.Quantitative.HingeStressNarrowing
import Gtz.Design.StratumEmptinessLedger
import Gtz.Design.LinePatternEnumeration
import Gtz.Design.LinePatternSixCasesTwo

namespace Gtz

open Matrix

/-! ## Section 1. The bordered-slack converse

The three lemmas below are the new mathematics; everything after them in this section
is bookkeeping on top of the shipped forward arrow.
-/

section BorderedSlackConverse

variable {size : ℕ}

/-- For a symmetric matrix the range and the kernel meet only at zero: a vector in both
is orthogonal to itself, and `Gtz.eq_zero_of_dotProduct_self_eq_zero` finishes. -/
theorem range_inf_ker_eq_bot_of_symmetric {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymmetric : formᵀ = form) :
    LinearMap.range form.mulVecLin ⊓ LinearMap.ker form.mulVecLin = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro vec ⟨⟨source, hsource⟩, hker⟩
  have hkerApply : form *ᵥ vec = 0 := hker
  have hsourceApply : form *ᵥ source = vec := hsource
  have hselfPairing : vec ⬝ᵥ vec = 0 := by
    calc vec ⬝ᵥ vec = (form *ᵥ source) ⬝ᵥ vec := by rw [hsourceApply]
      _ = vec ⬝ᵥ (form *ᵥ source) := dotProduct_comm _ _
      _ = source ⬝ᵥ (form *ᵥ vec) := dot_mulVec_comm hsymmetric vec source
      _ = 0 := by rw [hkerApply, dotProduct_zero]
  simpa using eq_zero_of_dotProduct_self_eq_zero hselfPairing

/-- ... so by rank-nullity they span. -/
theorem range_sup_ker_eq_top_of_symmetric {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymmetric : formᵀ = form) :
    LinearMap.range form.mulVecLin ⊔ LinearMap.ker form.mulVecLin = ⊤ := by
  have hdisjoint := range_inf_ker_eq_bot_of_symmetric hsymmetric
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker form.mulVecLin
  have hsupInf := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range form.mulVecLin) (LinearMap.ker form.mulVecLin)
  rw [hdisjoint, finrank_bot] at hsupInf
  have hambient : Module.finrank ℝ (Fin size → ℝ) = size := by simp
  have hfull : Module.finrank ℝ
      (↥(LinearMap.range form.mulVecLin ⊔ LinearMap.ker form.mulVecLin))
      = Module.finrank ℝ (Fin size → ℝ) := by
    rw [hambient]; rw [hambient] at hrankNullity; omega
  exact Submodule.eq_top_of_finrank_eq hfull

/-- **THE MISSING STEP.**  A rank-one Loewner bound already forces the coupling vector
into the range of the (symmetric) form, so the `hsolves` clause of
`Gtz.BorderedSlackLifting` is never an extra demand.

This is the claim `Gtz/Reduction/StrengthenedInductionHypothesis.lean` carries as prose
and never proves.  The tree ships every bordered lemma with the solution vector GIVEN
(`Gtz.borderedMatrix_posSemidef_iff_solutionRate_le`) and nothing supplying its
existence; this supplies it. -/
theorem exists_mulVec_solution_of_rankOneForm_le {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymmetric : formᵀ = form) {direction : Fin size → ℝ} {budget : ℝ}
    (hbound : ∀ testVec : Fin size → ℝ,
      (direction ⬝ᵥ testVec) ^ 2 ≤ budget * (testVec ⬝ᵥ (form *ᵥ testVec))) :
    ∃ solution : Fin size → ℝ, form *ᵥ solution = direction := by
  have hmem : direction ∈ LinearMap.range form.mulVecLin ⊔ LinearMap.ker form.mulVecLin := by
    rw [range_sup_ker_eq_top_of_symmetric hsymmetric]; trivial
  obtain ⟨rangePart, hrangePart, kernelPart, hkernelPart, hsplit⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨source, hsource⟩ := hrangePart
  have hsourceApply : form *ᵥ source = rangePart := hsource
  have hkernelApply : form *ᵥ kernelPart = 0 := hkernelPart
  have hatKernel := hbound kernelPart
  have hquadZero : kernelPart ⬝ᵥ (form *ᵥ kernelPart) = 0 := by
    rw [hkernelApply, dotProduct_zero]
  rw [hquadZero, mul_zero] at hatKernel
  have hcross : rangePart ⬝ᵥ kernelPart = 0 := by
    calc rangePart ⬝ᵥ kernelPart = (form *ᵥ source) ⬝ᵥ kernelPart := by rw [hsourceApply]
      _ = kernelPart ⬝ᵥ (form *ᵥ source) := dotProduct_comm _ _
      _ = source ⬝ᵥ (form *ᵥ kernelPart) := dot_mulVec_comm hsymmetric kernelPart source
      _ = 0 := by rw [hkernelApply, dotProduct_zero]
  have hpairing : direction ⬝ᵥ kernelPart = kernelPart ⬝ᵥ kernelPart := by
    rw [← hsplit, add_dotProduct, hcross, zero_add]
  rw [hpairing] at hatKernel
  have hnonneg : 0 ≤ kernelPart ⬝ᵥ kernelPart :=
    Finset.sum_nonneg fun index _ => mul_self_nonneg (kernelPart index)
  have hzero : kernelPart ⬝ᵥ kernelPart = 0 := by nlinarith [hatKernel, hnonneg]
  have hkernelZero : kernelPart = 0 := eq_zero_of_dotProduct_self_eq_zero hzero
  exact ⟨source, by rw [hsourceApply, ← hsplit, hkernelZero, add_zero]⟩

/-- A dominating subset contains an atom that is not the zero vector: otherwise its
subset sum is the zero matrix and the domination clause reads `-1 ≥ 0`. -/
theorem exists_nonzero_atom_of_dominates {atomCount rank : ℕ}
    {D : WeightedDesign atomCount (rank + 1)} {dominator : Finset (Fin atomCount)}
    (hdominates : Dominates D dominator) : ∃ pivot ∈ dominator, D.atom pivot ≠ 0 := by
  by_contra hnone
  have hallZero : ∀ label ∈ dominator, D.atom label = 0 := by
    intro label hlabel
    by_contra hnonzero
    exact hnone ⟨label, hlabel, hnonzero⟩
  have hsumZero : subsetSum D dominator = 0 := by
    rw [subsetSum]
    refine Finset.sum_eq_zero fun label hlabel => ?_
    rw [hallZero label hlabel, atomMatrix]
    ext rowIndex colIndex
    simp [Matrix.vecMulVec_apply]
  have hquad := quadForm_nonneg_of_posSemidef hdominates (Pi.single (0 : Fin (rank + 1)) (1 : ℝ))
  rw [hsumZero] at hquad
  have hunitValue : (Pi.single (0 : Fin (rank + 1)) (1 : ℝ))
      ⬝ᵥ (((0 : Matrix (Fin (rank + 1)) (Fin (rank + 1)) ℝ) - 1)
        *ᵥ Pi.single (0 : Fin (rank + 1)) (1 : ℝ)) = -1 := by
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply]
  rw [hunitValue] at hquad
  linarith

/-- **THE CONVERSE.**  Weighted GTZ in dimension `rank + 1` at every size produces the
strengthened hypothesis at `rank`.  Every certificate but one is a shipped extraction
lemma; the exception is the solution vector, supplied by
`Gtz.exists_mulVec_solution_of_rankOneForm_le`. -/
theorem borderedSlackLifting_of_gtzWeighted {rank : ℕ}
    (hgtz : ∀ size, GtzWeighted size (rank + 1)) : BorderedSlackLifting rank := by
  intro size D
  obtain ⟨dominator, hcard, hdominates⟩ := hgtz size D
  obtain ⟨pivot, hpivotMem, hpivotNonzero⟩ := exists_nonzero_atom_of_dominates hdominates
  obtain ⟨scale, deflator, hscalePos, hcoisometry, hkill, hsplit, hunit⟩ :=
    exists_pivot_deflation D pivot hpivotNonzero
  set pivotUnit := scale • D.atom pivot with hpivotUnitDef
  set subset := dominator.erase pivot with hsubsetDef
  have hnotMem : pivot ∉ subset := Finset.notMem_erase pivot dominator
  have hinsert : insert pivot subset = dominator := Finset.insert_erase hpivotMem
  have hfloor : 0 ≤ liftBudget D pivot pivotUnit subset := by
    have hcoercive := sum_sq_ge_of_dominates hdominates pivotUnit
    rw [hunit, ← hinsert, Finset.sum_insert hnotMem] at hcoercive
    rw [liftBudget_eq]
    have hswap : ∀ label : Fin size,
        (pivotUnit ⬝ᵥ D.atom label) ^ 2 = (D.atom label ⬝ᵥ pivotUnit) ^ 2 :=
      fun label => by rw [dotProduct_comm]
    rw [hswap pivot, Finset.sum_congr rfl fun label _ => hswap label]
    linarith
  have hprojected : Dominates (coisometryPushforward D deflator hcoisometry) subset :=
    dominates_pushforward_of_dominates_insert D pivot hcoisometry hkill subset hnotMem
      (by rw [hinsert]; exact hdominates)
  have hloewner := (dominates_insert_iff_loewnerSlack D pivot hcoisometry hunit hsplit
    hkill subset hnotMem hprojected hfloor).mp (by rw [hinsert]; exact hdominates)
  obtain ⟨couplingSolution, hsolves⟩ :=
    exists_mulVec_solution_of_rankOneForm_le
      (projectedGap_transpose D deflator hcoisometry subset) hloewner
  have hrate := solutionRate_le_of_rankOneForm_le hprojected hfloor hsolves hloewner
  exact ⟨pivot, pivotUnit, deflator, hcoisometry, subset, couplingSolution, hsplit, hkill,
    hnotMem, by rw [hsubsetDef, Finset.card_erase_of_mem hpivotMem, hcard]; omega, hprojected,
    hfloor, hsolves, hrate⟩

/-- **THE CANONICAL STATEMENT.**  Every other result of this section is a corollary. -/
theorem borderedSlackLifting_iff_gtzWeightedAll {rank : ℕ} :
    BorderedSlackLifting rank ↔ GtzWeightedAll (rank + 1) :=
  ⟨gtzWeighted_succ_of_borderedSlackLifting, borderedSlackLifting_of_gtzWeighted⟩

/-- ... and the second equivalence the module header asserts. -/
theorem borderedSlackLifting_iff_liftingLemma {rank : ℕ} :
    BorderedSlackLifting rank ↔ LiftingLemma rank :=
  borderedSlackLifting_iff_gtzWeightedAll.trans
    (liftingLemma_iff_gtzWeighted_succ (k := rank)).symm

/-- Rung one, beside `Gtz.borderedSlackLifting_zero`. -/
theorem borderedSlackLifting_one : BorderedSlackLifting 1 :=
  borderedSlackLifting_of_gtzWeighted gtz_rank_two

/-- **Residual: `∀ rank, BorderedSlackLifting rank` is FULL WEIGHTED GTZ**, not a
statement about the rank-three frontier.  It sits strictly above it. -/
theorem forall_borderedSlackLifting_iff_forall_gtzWeightedAll :
    (∀ rank : ℕ, BorderedSlackLifting rank) ↔ (∀ rank : ℕ, GtzWeightedAll rank) := by
  refine ⟨gtzWeightedAll_of_borderedSlackLifting, fun hall rank => ?_⟩
  exact borderedSlackLifting_of_gtzWeighted fun size => hall (rank + 1) size

/-- **Residual: `∀ rank, DoesPropagateBorderedSlack rank` is FULL WEIGHTED GTZ too.**
Forward needs the base case, which `Gtz.borderedSlackLifting_zero` now supplies;
backward is free, because under full GTZ every rung's CONCLUSION holds outright. -/
theorem forall_doesPropagateBorderedSlack_iff_forall_gtzWeightedAll :
    (∀ rank : ℕ, DoesPropagateBorderedSlack rank) ↔ (∀ rank : ℕ, GtzWeightedAll rank) := by
  refine ⟨gtzWeightedAll_of_base_of_propagates, fun hall rank _ => ?_⟩
  exact borderedSlackLifting_of_gtzWeighted fun size => hall (rank + 2) size

/-- **The propagation family is a LADDER, and its rungs are the original induction
step.**  Rung zero is a theorem (its conclusion is `Gtz.gtz_rank_two`); rung one is the
campaign frontier; rung `rank` is the `(rank+1) → (rank+2)` step verbatim.  This is the
`CORRECTED:` paragraph of the header, mechanised. -/
theorem doesPropagateBorderedSlack_iff_rankStep {rank : ℕ} :
    DoesPropagateBorderedSlack rank
      ↔ (GtzWeightedAll (rank + 1) → GtzWeightedAll (rank + 2)) := by
  constructor
  · intro hpropagates hall
    exact borderedSlackLifting_iff_gtzWeightedAll.mp
      (hpropagates (borderedSlackLifting_iff_gtzWeightedAll.mpr hall))
  · intro hstep hslack
    exact borderedSlackLifting_iff_gtzWeightedAll.mpr
      (hstep (borderedSlackLifting_iff_gtzWeightedAll.mp hslack))

/-- **The first open rung of the propagation family IS the campaign frontier.**  An
agent sent at "propagation" at rung one is being sent at `Gtz.GtzWeightedAll 3`. -/
theorem doesPropagateBorderedSlack_one_iff_gtzWeightedAll_three :
    DoesPropagateBorderedSlack 1 ↔ GtzWeightedAll 3 := by
  rw [doesPropagateBorderedSlack_iff_rankStep]
  exact ⟨fun hstep => hstep gtz_rank_two, fun hall _ => hall⟩

end BorderedSlackConverse

/-! ## Section 2. Canonical names for the rank-three frontier cluster

Each theorem below puts a residual on the LEFT of an `Iff` whose right side is
`Gtz.GtzWeighted 6 3`.  Where the tree already ships that bridge under another name
(`Gtz.gtzWeightedHeavy_six_three_iff_gtzWeighted_six_three`,
`Gtz.gtzWeighted_six_three_iff_seven_three`, `Gtz.liftingLemma_two_iff_six_three`,
`Gtz.gtzWeightedHeavyMinimal_iff_gtzWeighted_six_three`,
`Gtz.hasChartValueZeroLimitAtEveryCrux_iff_gtzWeighted_six_three`,
`Gtz.gtzWeighted_six_three_iff_exceptionalDesignsDominate`,
`Gtz.gtzWeighted_six_three_iff_seven_four`) it is NOT restated here.
-/

section FrontierNames

/-- The bridge the crux module never states.  It ships both arrows separately —
`Gtz.gtzWeighted_six_three_of_isEmpty_sixThreeCrux` and
`Gtz.isEmpty_sixThreeCrux_of_gtzWeighted_six_three` — and six `Iff`s to OTHER targets,
but not this one, which is why a head index scored the residual as open. -/
theorem isEmpty_sixThreeCrux_iff_gtzWeighted_six_three :
    IsEmpty SixThreeCrux ↔ GtzWeighted 6 3 :=
  ⟨gtzWeighted_six_three_of_isEmpty_sixThreeCrux, isEmpty_sixThreeCrux_of_gtzWeighted_six_three⟩

/-- The chart-value regime at the ceiling gap width. -/
theorem chartValueTwoRegime_four_div_twentySeven_iff_gtzWeighted_six_three :
    ChartValueTwoRegime (4 / 27) ↔ GtzWeighted 6 3 :=
  ⟨fun hregime => gtzWeighted_six_three_of_isEmpty_sixThreeCrux
      (isEmpty_sixThreeCrux_of_chartValueTwoRegime hregime),
   fun hcell => chartValueTwoRegime_of_isEmpty_sixThreeCrux
      (isEmpty_sixThreeCrux_of_gtzWeighted_six_three hcell) (4 / 27)⟩

/-- ... and the frontier gives EVERY gap width, so no member of the family below the
`4/27` threshold is a reduction of the cell — each is a consequence of it. -/
theorem chartValueTwoRegime_of_gtzWeighted_six_three (hcell : GtzWeighted 6 3)
    (gapWidth : ℝ) : ChartValueTwoRegime gapWidth :=
  chartValueTwoRegime_of_isEmpty_sixThreeCrux
    (isEmpty_sixThreeCrux_of_gtzWeighted_six_three hcell) gapWidth

/-- The discriminant covering at six points is the frontier in polynomial coordinates. -/
theorem discriminantCovering_six_iff_gtzWeighted_six_three :
    DiscriminantCovering 6 ↔ GtzWeighted 6 3 :=
  (gtzWeightedHeavy_three_iff_discriminantCovering 6).symm.trans
    gtzWeightedHeavy_six_three_iff_gtzWeighted_six_three

/-- ... and so is the covering at SEVEN points: the size changes across the bridge, so
the two coverings are also equivalent to each other. -/
theorem discriminantCovering_seven_iff_gtzWeighted_six_three :
    DiscriminantCovering 7 ↔ GtzWeighted 6 3 :=
  (gtzWeightedHeavy_three_iff_discriminantCovering 7).symm.trans
    gtzWeightedHeavy_seven_three_iff_gtzWeighted_six_three

/-- The symmetric covering is the discriminant covering is the frontier. -/
theorem symmetricCovering_six_iff_gtzWeighted_six_three :
    SymmetricCovering 6 ↔ GtzWeighted 6 3 :=
  (symmetricCovering_iff_discriminantCovering 6).trans
    discriminantCovering_six_iff_gtzWeighted_six_three

/-- The rank-four pivot-minor covering at seven points is the same sentence again, in a
rank-four polynomial encoding. -/
theorem pivotMinorCoveringFour_seven_iff_gtzWeighted_six_three :
    PivotMinorCoveringFour 7 ↔ GtzWeighted 6 3 :=
  discriminantCovering_seven_iff_pivotMinorCoveringFour_seven.symm.trans
    discriminantCovering_seven_iff_gtzWeighted_six_three

/-- The all-sizes rank-three statement is the single cell, by instantiation one way and
the shipped crystallization the other. -/
theorem gtzWeightedAll_three_iff_gtzWeighted_six_three :
    GtzWeightedAll 3 ↔ GtzWeighted 6 3 :=
  ⟨fun hall => hall 6, gtzWeightedAll_three_of_six_three⟩

/-- The all-heavy cell at `(7,4)`. -/
theorem gtzWeightedHeavy_seven_four_iff_gtzWeighted_six_three :
    GtzWeightedHeavy 7 4 ↔ GtzWeighted 6 3 :=
  ⟨fun hheavy => gtzWeightedAll_three_of_heavy_seven_four hheavy 6,
   fun hcell => gtzWeightedHeavy_of_gtzWeighted (gtzWeighted_six_three_iff_seven_four.mp hcell)⟩

/-- **The negations agree too.**  `¬ GtzWeighted 6 3` and `¬ GtzWeighted 7 3` are one
proposition, so the census's two entries are the two faces of ONE decision. -/
theorem not_gtzWeighted_seven_three_iff_not_gtzWeighted_six_three :
    ¬ GtzWeighted 7 3 ↔ ¬ GtzWeighted 6 3 :=
  not_congr gtzWeighted_six_three_iff_seven_three.symm

/-- The all-heavy negation at `(7,3)`, likewise. -/
theorem not_gtzWeightedHeavy_seven_three_iff_not_gtzWeighted_six_three :
    ¬ GtzWeightedHeavy 7 3 ↔ ¬ GtzWeighted 6 3 :=
  not_congr gtzWeightedHeavy_seven_three_iff_gtzWeighted_six_three

/-- The all-sizes negation, likewise. -/
theorem not_gtzWeightedAll_three_iff_not_gtzWeighted_six_three :
    ¬ GtzWeightedAll 3 ↔ ¬ GtzWeighted 6 3 :=
  not_congr gtzWeightedAll_three_iff_gtzWeighted_six_three

end FrontierNames

/-! ## Section 3. The narrowings, and the corank and line-count residuals

Every theorem in this section has the shape "the cell with hypotheses ADDED".  The
backward arrow is always the trivial weakening `fun D _ _ => hcell D`, which no shipped
theorem records and which no defeq classifier can find; the forward arrow is the
shipped consumable.
-/

section Narrowings

/-- Residual: the doubly-heavy stratum at `(6,3)`. -/
theorem forall_doublyHeavy_dominates_six_iff_gtzWeighted_six_three :
    (∀ D : WeightedDesign 6 3, AllHeavy D → HasStrictlyDominatingCoSingletons D →
      ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) ↔ GtzWeighted 6 3 :=
  ⟨fun hstratum => gtzWeightedAll_three_of_doublyHeavy_six_three hstratum 6,
   fun hcell D _ _ => hcell D⟩

/-- Residual: the doubly-heavy stratum at `(7,3)` -- the SAME sentence, so the "sharper
twenty triples rather than thirty-five" reading is about the search space, not about
logical strength. -/
theorem forall_doublyHeavy_dominates_seven_iff_gtzWeighted_six_three :
    (∀ D : WeightedDesign 7 3, AllHeavy D → HasStrictlyDominatingCoSingletons D →
      ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C) ↔ GtzWeighted 6 3 :=
  ⟨fun hstratum => gtzWeightedAll_three_of_doublyHeavy_seven_three hstratum 6,
   fun hcell D _ _ => gtzWeighted_six_three_iff_seven_three.mp hcell D⟩

/-- Residual: six-or-more lines, all-heavy, at `(6,3)`. -/
theorem forall_heavy_sixLines_dominates_six_iff_gtzWeighted_six_three :
    (∀ D : WeightedDesign 6 3, AllHeavy D → ¬ HasAtMostLines D 5 →
      ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) ↔ GtzWeighted 6 3 :=
  ⟨fun hstratum => gtzWeightedAll_three_of_sixLines hstratum 6, fun hcell D _ _ => hcell D⟩

/-- Residual: six-or-more lines at `(6,3)` with the all-heavy decoration DROPPED.  It is
the same obligation: a non-all-heavy `(6,3)` design has a light atom and deflates to
`(5,3)`, which is a theorem.  So the decoration is free at size six. -/
theorem forall_sixLines_dominates_six_iff_gtzWeighted_six_three :
    (∀ D : WeightedDesign 6 3, ¬ HasAtMostLines D 5 →
      ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) ↔ GtzWeighted 6 3 :=
  ⟨gtzWeighted_six_three_of_sixLines, fun hcell D _ => hcell D⟩

/-- Residual: six-or-more lines, all-heavy, at `(7,3)`. -/
theorem forall_heavy_sixLines_dominates_seven_iff_gtzWeighted_six_three :
    (∀ D : WeightedDesign 7 3, AllHeavy D → ¬ HasAtMostLines D 5 →
      ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C) ↔ GtzWeighted 6 3 :=
  ⟨fun hstratum => rank_three_of_heavy_top (gtzWeightedHeavy_seven_three_of_sixLines hstratum) 6,
   fun hcell D _ _ => gtzWeighted_six_three_iff_seven_three.mp hcell D⟩

/-- Residual: six-or-more lines at `(7,3)`, undecorated.  Note the asymmetry with size
six: the light-atom deflation at `(7,3)` lands on `(6,3)`, the OPEN cell, so this
equivalence must route through rank three rather than through the free `(5,3)` rung. -/
theorem forall_sixLines_dominates_seven_iff_gtzWeighted_six_three :
    (∀ D : WeightedDesign 7 3, ¬ HasAtMostLines D 5 →
      ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C) ↔ GtzWeighted 6 3 :=
  ⟨fun hstratum => gtzWeightedAll_three_of_six_three
      (gtzWeighted_six_three_iff_seven_three.mpr (gtzWeighted_seven_three_of_sixLines hstratum)) 6,
   fun hcell D _ => gtzWeighted_six_three_iff_seven_three.mp hcell D⟩

/-- Residual: the generic all-heavy stratum at `(6,3)`. -/
theorem forall_generic_dominates_iff_gtzWeighted_six_three :
    (∀ D : WeightedDesign 6 3, AllHeavy D → IsGenericDesign D →
      ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) ↔ GtzWeighted 6 3 :=
  ⟨gtzWeighted_of_forall_generic_dominates, fun hcell D _ _ => hcell D⟩

/-- Residual: the nonzero-pairing stratum at `(6,3)`. -/
theorem forall_nonzeroPairings_dominates_iff_gtzWeighted_six_three :
    (∀ D : WeightedDesign 6 3, AllHeavy D →
      (∀ firstLabel secondLabel : Fin 6, firstLabel ≠ secondLabel →
        atomPairing D firstLabel secondLabel ≠ 0) →
      ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) ↔ GtzWeighted 6 3 :=
  ⟨gtzWeighted_of_forall_nonzero_pairings_dominates, fun hcell D _ _ => hcell D⟩

/-- Residual: no refutation candidate exists.  The backward arrow is the shipped
design-level refutation read contrapositively. -/
theorem forall_not_isSixThreeRefutationCandidate_iff_gtzWeighted_six_three :
    (∀ design : WeightedDesign 6 3, ¬ IsSixThreeRefutationCandidate design)
      ↔ GtzWeighted 6 3 :=
  ⟨gtzWeighted_six_three_of_forall_not_isSixThreeRefutationCandidate,
   fun hcell _design hcandidate =>
     not_gtzWeighted_six_three_of_isSixThreeRefutationCandidate hcandidate hcell⟩

/-- The `Sharp` variant is the SAME obligation, pointwise: the tree ships
`Gtz.isSixThreeRefutationCandidateSharp_iff` at every design. -/
theorem forall_not_isSixThreeRefutationCandidateSharp_iff_gtzWeighted_six_three :
    (∀ design : WeightedDesign 6 3, ¬ IsSixThreeRefutationCandidateSharp design)
      ↔ GtzWeighted 6 3 := by
  rw [← forall_not_isSixThreeRefutationCandidate_iff_gtzWeighted_six_three]
  exact ⟨fun hnone design hcandidate =>
      hnone design ((isSixThreeRefutationCandidateSharp_iff design).mpr hcandidate),
    fun hnone design hcandidate =>
      hnone design ((isSixThreeRefutationCandidateSharp_iff design).mp hcandidate)⟩

/-- The `Minimal` variant is a strictly SMALLER box of designs, so the two negated
statements are not pointwise equal -- but both are the cell, so they are equal as
propositions. -/
theorem forall_not_isSixThreeRefutationCandidateMinimal_iff_gtzWeighted_six_three :
    (∀ design : WeightedDesign 6 3, ¬ IsSixThreeRefutationCandidateMinimal design)
      ↔ GtzWeighted 6 3 :=
  ⟨gtzWeighted_six_three_of_forall_not_isSixThreeRefutationCandidateMinimal,
   fun hcell _design hminimal =>
     not_gtzWeighted_six_three_of_isSixThreeRefutationCandidate
       (isSixThreeRefutationCandidate_of_minimal hminimal) hcell⟩

/-- **Residual [76] is a STRENGTHENING OF THE NEGATION of the target**, and the weaker
statement that its consumer actually uses is already an equivalence with that negation.
So proving [76] would refute the conjecture, and it buys nothing beyond `¬ GtzWeighted
6 3` even then. -/
theorem exists_isSixThreeRefutationCandidate_iff_not_gtzWeighted_six_three :
    (∃ design : WeightedDesign 6 3, IsSixThreeRefutationCandidate design)
      ↔ ¬ GtzWeighted 6 3 :=
  ⟨fun ⟨_, hcandidate⟩ =>
      not_gtzWeighted_six_three_of_isSixThreeRefutationCandidate hcandidate,
   exists_isSixThreeRefutationCandidate_of_not_gtzWeighted_six_three⟩

/-- Residual: corank three at every rank.  Forward is the shipped consumer; backward is
Naimark duality at size `rank + 3`, which sends rank `rank` to rank `3`.  The backward
arrow instantiates a universally quantified residual at a VARIABLE size and runs through
an `Iff`, which is why no defeq classifier recorded it. -/
theorem forall_corankThree_iff_gtzWeighted_six_three :
    (∀ rank : ℕ, 1 ≤ rank → GtzWeighted (rank + 3) rank) ↔ GtzWeighted 6 3 := by
  refine ⟨fun hcorank => gtzWeightedAll_three_of_corank_three hcorank 6, fun hcell rank hrank => ?_⟩
  have hall : GtzWeightedAll 3 := gtzWeightedAll_three_of_six_three hcell
  have hrankLe : rank + 1 ≤ rank + 3 := by omega
  have hdual := gtzWeighted_dual_iff (rank + 3) rank hrank hrankLe
  have hcorankValue : rank + 3 - rank = 3 := by omega
  rw [hdual, hcorankValue]
  exact hall (rank + 3)

/-- Residual: the `rank + 3` line bound at every rank is the rank-three cell as well. -/
theorem forall_hasAtMostLines_rankAddThree_iff_gtzWeightedAll_three :
    (∀ rank : ℕ, 1 ≤ rank → ∀ (size : ℕ) (D : WeightedDesign size rank),
        HasAtMostLines D (rank + 3) → ∃ C : Finset (Fin size), C.card = rank ∧ Dominates D C)
      ↔ GtzWeightedAll 3 := by
  refine ⟨gtzWeightedAll_three_of_hasAtMostLines_rankAddThree, fun hall rank hrank size D hlines => ?_⟩
  exact exists_dominating_of_hasAtMostLines
    (forall_corankThree_iff_gtzWeighted_six_three.mpr (hall 6) rank hrank) size D hlines

end Narrowings

/-! ## Section 4. The rank-four and rank-five rings, and the full-GTZ aliases -/

section HigherRanks

/-- Residual: `GtzWeighted 11 4` is the whole of rank four. -/
theorem gtzWeighted_eleven_four_iff_gtzWeightedAll_four :
    GtzWeighted 11 4 ↔ GtzWeightedAll 4 :=
  ⟨gtzWeightedAll_four_of_eleven, fun hall => hall 11⟩

/-- Residual: so is the Veronese top `GtzWeighted 10 4`, and that is the SINGLE-premise
reason the rank-four cluster collapses -- `10 = 4*(4+1)/2` is the top, so
`Gtz.gtzWeightedAll_four_of_ten` climbs from it with nothing else. -/
theorem gtzWeighted_ten_four_iff_gtzWeightedAll_four :
    GtzWeighted 10 4 ↔ GtzWeightedAll 4 :=
  ⟨gtzWeightedAll_four_of_ten, fun hall => hall 10⟩

/-- Residual: the all-heavy restriction is not a discount at the window top. -/
theorem gtzWeightedHeavy_eleven_four_iff_gtzWeightedAll_four :
    GtzWeightedHeavy 11 4 ↔ GtzWeightedAll 4 :=
  ⟨rank_four_of_heavy_top, fun hall => gtzWeightedHeavy_of_gtzWeighted (hall 11)⟩

/-- Residual: the only rank-five entry of the census, and it is all of rank five.  There
is no `PivotMinorCoveringFive`, so this has no covering-polynomial partner. -/
theorem gtzWeightedHeavy_sixteen_five_iff_gtzWeightedAll_five :
    GtzWeightedHeavy 16 5 ↔ GtzWeightedAll 5 :=
  ⟨rank_five_of_heavy_top, fun hall => gtzWeightedHeavy_of_gtzWeighted (hall 16)⟩

/-- Residual: the quantified chart interior is FULL weighted GTZ, so it sits strictly
above the rank-three frontier rather than beside it. -/
theorem forall_chartGtzInterior_iff_forall_gtzWeighted :
    (∀ atomCount rankValue : ℕ, ChartGtzInterior atomCount rankValue)
      ↔ (∀ atomCount rankValue : ℕ, GtzWeighted atomCount rankValue) :=
  ⟨fun hinterior atomCount rankValue =>
      (chartGtzInterior_iff_gtzWeighted atomCount rankValue).mp (hinterior atomCount rankValue),
   fun hgtz atomCount rankValue =>
      (chartGtzInterior_iff_gtzWeighted atomCount rankValue).mpr (hgtz atomCount rankValue)⟩

/-- Residual: the canonical window list IS the whole conjecture, carrying no reduction in
logical strength.  Its value is its SHAPE -- a finite window per rank -- not its
difficulty, and an agent assigned "prove the canonical list" is assigned all of GTZ. -/
theorem forall_canonicalWindow_iff_forall_gtzWeightedAll :
    (∀ atomWidth atomCount : ℕ, 2 ≤ atomWidth → 2 * atomWidth ≤ atomCount →
        atomCount ≤ atomWidth * (atomWidth + 1) / 2 + 1 → GtzWeighted atomCount atomWidth)
      ↔ (∀ rank : ℕ, 1 ≤ rank → GtzWeightedAll rank) :=
  ⟨gtz_of_canonical_list, fun hall atomWidth atomCount hwidth _ _ => hall atomWidth (by omega) atomCount⟩

end HigherRanks

/-! ## Section 5. The spread-floor trio and the balanced-stress stratum lattice -/

section StratumLattice

/-- The shipped certificate at `(6,3)`, in its uniform-weight form. -/
theorem spreadFloorCertificate_sixThree_uniform_iff :
    SpreadFloorCertificate 6 3 (((6 : ℕ) : ℝ)⁻¹)
      ↔ ∀ D : WeightedDesign 6 3,
          (∀ atomLabel : Fin 6, D.weight atomLabel = ((6 : ℕ) : ℝ)⁻¹) →
            ¬ HasParallelPair D →
              ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C :=
  spreadFloorCertificate_sizeInv_iff_uniform (by norm_num)

/-- Residual: the unequal-leverage form of the spread floor. -/
theorem forall_unequalLeverage_dominates_iff_spreadFloorCertificate :
    (∀ D : WeightedDesign 6 3,
        (∀ atomLabel : Fin 6, D.weight atomLabel = ((6 : ℕ) : ℝ)⁻¹) →
          (∃ atomLabel : Fin 6, leverageOf (D.atom atomLabel) ≠ (3 : ℝ)) →
            ¬ HasParallelPair D →
              ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C)
      ↔ SpreadFloorCertificate 6 3 (((6 : ℕ) : ℝ)⁻¹) :=
  ⟨spreadFloorCertificate_sixThree_sizeInv_of_unequalLeverage,
   fun hcertificate D huniform _ hnoParallel =>
     spreadFloorCertificate_sixThree_uniform_iff.mp hcertificate D huniform hnoParallel⟩

/-- Residual: the heavy unequal-leverage form -- the same obligation. -/
theorem forall_heavyUnequalLeverage_dominates_iff_spreadFloorCertificate :
    (∀ D : WeightedDesign 6 3,
        (∀ atomLabel : Fin 6, D.weight atomLabel = ((6 : ℕ) : ℝ)⁻¹) →
          (∀ atomLabel : Fin 6, 1 < leverageOf (D.atom atomLabel)) →
            (∃ atomLabel : Fin 6, leverageOf (D.atom atomLabel) ≠ (3 : ℝ)) →
              ¬ HasParallelPair D →
                ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C)
      ↔ SpreadFloorCertificate 6 3 (((6 : ℕ) : ℝ)⁻¹) :=
  ⟨spreadFloorCertificate_sixThree_sizeInv_of_heavyUnequalLeverage,
   fun hcertificate D huniform _ _ hnoParallel =>
     spreadFloorCertificate_sixThree_uniform_iff.mp hcertificate D huniform hnoParallel⟩

/-- Residual: the closed-residue form.  Its missing `¬HasParallelPair` slot is supplied
by the shipped merge branch, which is unconditional. -/
theorem forall_closedResidue_dominates_iff_spreadFloorCertificate :
    (∀ D : WeightedDesign 6 3,
        (∀ atomLabel : Fin 6, D.weight atomLabel = ((6 : ℕ) : ℝ)⁻¹) →
          (∀ atomLabel : Fin 6, 1 ≤ leverageOf (D.atom atomLabel)) →
            (∃ atomLabel : Fin 6, leverageOf (D.atom atomLabel) ≠ (3 : ℝ)) →
              ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C)
      ↔ SpreadFloorCertificate 6 3 (((6 : ℕ) : ℝ)⁻¹) := by
  refine ⟨spreadFloorCertificate_sixThree_sizeInv_of_closedResidue,
    fun hcertificate D huniform _ _ => ?_⟩
  by_cases hparallel : HasParallelPair D
  · exact exists_dominating_triple_of_hasParallelPair_sixThree D hparallel
  · exact spreadFloorCertificate_sixThree_uniform_iff.mp hcertificate D huniform hparallel

/-- **The balanced-stress decoration is FREE at six points**, on the heavy face: the
qualifier is paid by `Gtz.hasOnlyBalancedStress_of_isTie_sixThree` and the leverage floor
by the unconditional `Gtz.gtzWeighted_of_le_five`.  So the decorated predicate is the
UNDECORATED one, pointwise. -/
theorem stratumIsTieFreeAmongHeavyAtBalancedStress_iff_stratumIsTieFree
    (pattern : LinePattern 6) :
    StratumIsTieFreeAmongHeavyAtBalancedStress pattern ↔ StratumIsTieFree pattern :=
  ⟨fun hnarrow => stratumIsTieFree_of_amongHeavy_sixThree
      (stratumIsTieFreeAmongHeavy_of_balancedStress_sixThree hnarrow),
   fun hfree D hpattern _ _ => hfree D hpattern⟩

/-- ... likewise on the all-heavy face. -/
theorem stratumIsTieFreeAmongAllHeavyAtBalancedStress_iff_stratumIsTieFreeAmongAllHeavy
    (pattern : LinePattern 6) :
    StratumIsTieFreeAmongAllHeavyAtBalancedStress pattern
      ↔ StratumIsTieFreeAmongAllHeavy pattern :=
  ⟨stratumIsTieFreeAmongAllHeavy_of_balancedStress_sixThree,
   fun hfree D hpattern hheavy _ => hfree D hpattern hheavy⟩

/-- ... and on the unit-leverage face. -/
theorem stratumIsTieFreeAtUnitLeverageAtBalancedStress_iff_stratumIsTieFreeAtUnitLeverage
    (pattern : LinePattern 6) :
    StratumIsTieFreeAtUnitLeverageAtBalancedStress pattern
      ↔ StratumIsTieFreeAtUnitLeverage pattern :=
  ⟨stratumIsTieFreeAtUnitLeverage_of_balancedStress_sixThree,
   fun hfree D hpattern hunit _ => hfree D hpattern hunit⟩

/-- **The order among the three balanced-stress residuals is a MEET, not a chain.**
The heavy face's design class is covered by two DISJOINT classes -- `AllHeavy` is
strict, the unit-leverage face is an equality, and `1 < 1` is false -- so the heavy form
implies both faces and the two faces give it back.  The census's three entries are one
obligation. -/
theorem stratumIsTieFreeAmongHeavyAtBalancedStress_iff_faces (pattern : LinePattern 6) :
    StratumIsTieFreeAmongHeavyAtBalancedStress pattern
      ↔ (StratumIsTieFreeAmongAllHeavyAtBalancedStress pattern
          ∧ StratumIsTieFreeAtUnitLeverageAtBalancedStress pattern) := by
  constructor
  · intro hheavy
    have hfree : StratumIsTieFree pattern :=
      (stratumIsTieFreeAmongHeavyAtBalancedStress_iff_stratumIsTieFree pattern).mp hheavy
    exact ⟨fun D hpattern _ _ => hfree D hpattern, fun D hpattern _ _ => hfree D hpattern⟩
  · rintro ⟨hallHeavy, hunitLeverage⟩
    have hheavy : StratumIsTieFreeAmongHeavy pattern :=
      stratumIsTieFreeAmongHeavy_of_allHeavy_and_unitLeverage_atBalancedStress
        hallHeavy hunitLeverage
    exact fun D hpattern hleverage _ => hheavy D hpattern hleverage

end StratumLattice

/-! ## Section 6. Names for the anonymous open obligations

The two propositions below are carried by the tree as inline `∀`s inside a hypothesis
and are therefore invisible to any census that indexes by head constant.  Naming them is
what lets the next census count them.
-/

section OpenObligations

/-- **OPEN.  The six-point hinge stratum obligation.**  Tie-freeness of the eight
non-near-pencil six-point strata, all-heavy.  Every route into `Gtz.HingeHoldsAtSize 6 3`
is equivalent to this, and by `Gtz.hingeHoldsAtSize_sixThree_of_tieFreeResidual` it
suffices for the hinge at `(6,3)` -- which, unlike the seven-point hinge, IS on the path
to the frontier.

EXTERNAL MEASUREMENT (phase-4 census, not re-derived here).  An exhaustive walk of the
8947 `Gtz` theorems finds FOUR declarations whose conclusion has this head and ZERO that
conclude the statement itself; a `Not`-headed pool of 448 candidates yields no
refutation, with two same-head positive controls firing one and two sizes down
(`Gtz.not_hingeHoldsAtSize_five_three`, `Gtz.not_hingeHoldsAtSize_four_three`) so the
sweep provably sees a refutation of this predicate family when one exists.  The
near-pencil guard peels exactly one of the nine entries of `Gtz.lineFamiliesSix`, so
eight strata survive; none is discharged anywhere in the tree.  No prior art was found
for ties on a rank-3 matroid stratum of a weighted Parseval frame. -/
def HingeStratumObligationSix : Prop :=
  ∀ lines ∈ lineFamiliesSix, ¬ IsNearPencilFamily lines →
    StratumIsTieFreeAmongHeavy (lineFamilyPattern lines)

/-- **OPEN.  The seven-point hinge stratum obligation**, with the near-pencil and Fano
guards.

EXTERNAL MEASUREMENT (phase-4 census, not re-derived here).  Zero producers and exactly
one consumer tree-wide, and that consumer's conclusion `Gtz.HingeHoldsAtSize 7 3` has
ZERO consumers -- so unlike the six-point obligation this one is OFF EVERY PATH, and
discharging it would move nothing.  The two guards peel exactly two of the twenty-three
entries of `Gtz.lineFamiliesSeven` (near pencil, Fano), both of which are already
tie-free theorems, leaving twenty-one.  No refutation in the 448-theorem `Not`-headed
pool, with three positive controls firing. -/
def HingeStratumObligationSeven : Prop :=
  ∀ lines ∈ lineFamiliesSeven, ¬ IsNearPencilFamily lines →
    ¬ IsFanoClass (lineFamilyPattern lines) →
      StratumIsTieFreeAmongHeavy (lineFamilyPattern lines)

/-- The named six-point obligation is exactly the hypothesis the shipped assembly takes,
so naming it costs nothing at the call site. -/
theorem hingeHoldsAtSize_six_three_of_hingeStratumObligationSix
    (hobligation : HingeStratumObligationSix) : HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_sixThree_of_tieFreeResidual hobligation

/-- The balanced-stress narrowing of the six-point obligation is the SAME obligation --
see `Gtz.stratumIsTieFreeAmongHeavyAtBalancedStress_iff_stratumIsTieFree` for the
pointwise reason. -/
theorem hingeStratumObligationSix_iff_balancedStress :
    HingeStratumObligationSix
      ↔ (∀ lines ∈ lineFamiliesSix, ¬ IsNearPencilFamily lines →
          StratumIsTieFreeAmongHeavyAtBalancedStress (lineFamilyPattern lines)) := by
  constructor
  · exact fun hobligation lines hmem hnotPencil D hpattern hleverage _ =>
      hobligation lines hmem hnotPencil D hpattern hleverage
  · exact fun hnarrow lines hmem hnotPencil =>
      stratumIsTieFreeAmongHeavy_of_balancedStress_sixThree (hnarrow lines hmem hnotPencil)

/-- The named seven-point obligation, likewise, is the hypothesis the shipped assembly
takes -- and it drags the open `Gtz.GtzWeighted 6 3` in with it, which is the second
reason this lane is not a reduction. -/
theorem hingeHoldsAtSize_seven_three_of_hingeStratumObligationSeven
    (hsixThree : GtzWeighted 6 3)
    (hcomplete : LinearSpaceListIsComplete 7 linePatternListSeven)
    (hobligation : HingeStratumObligationSeven) : HingeHoldsAtSize 7 3 :=
  hingeHoldsAtSize_of_linearSpaceEnumeration_sevenThree hsixThree hcomplete hobligation

end OpenObligations

/-! ## Section 7. The sign-clash clean pair

`Gtz.EraseConsistentForcedClashOnClean` and `Gtz.OwnSignForcedClashOnClean` are the CSP
and sigma readings of one obligation; both arrows ship separately and the `Iff` did not.
The canonical name is the sigma form, which is what a parametric-LP attack solves.
-/

/-- The two clean sign-clash residuals are one proposition. -/
theorem eraseConsistentForcedClashOnClean_iff_ownSignForcedClashOnClean :
    EraseConsistentForcedClashOnClean ↔ OwnSignForcedClashOnClean :=
  ⟨ownSignForcedClashOnClean_of_eraseConsistentForcedClashOnClean,
   eraseConsistentForcedClashOnClean_of_ownSignForcedClashOnClean⟩

end Gtz

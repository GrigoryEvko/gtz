/-
# The reach hypothesis at general rank: the composition, and its two topological inputs

`AnchorReachAssembly` reduced route (b)'s anchor-reach obligation to ONE
statement, `CanonicalWindowParallelFreeConnectivity`.  This file takes that
statement apart, at general size and general rank, exactly as
`Gtz.Reduction.ParallelFreeReach` does at `(6,3)`:

* **T1, the tuple walk** (`GoodTupleConnected`): the row systems that are
  pairwise non-parallel and spanning are path-connected inside themselves.
* **T2, the whitening interface** (`WhiteningTransferAtRank`): a continuous
  pointwise-spanning tuple path with Parseval endpoints deforms onto the
  Parseval shell through a pointwise invertible linear mix, so the parallelism
  pattern survives.
* **T3, the composition** (`parallelFreeReachesAnchor_of_tupleReach`, proved
  here at every size and rank): fold both designs into row tuples, walk, whiten,
  and divide by an interpolated weight profile.

T3 is the whole content of this file, and it is rank-uniform.  Chaining it with
`AnchorReachAssembly` turns the anchor-reach obligation into T1 and T2 alone —
`sharpWindowAnchorReach_of_tupleReach` states that outright.

MECHANISM PARITY: at `(6,3)` both inputs are theorems already in the tree
(`Gtz.exists_goodTuple_path` and `Gtz.whiteningTransfer_holds`), and the
general-rank composition reproduces `Gtz.parallelFreeReachesAnchor_six_three`
from them.  So the skeleton is calibrated against the one cell where the answer
is known, and nothing here weakens it.

THE RANK SIGNATURE: T1 dies at rank two, where two vectors are parallel on a
codimension-one wall.  `not_canonicalWindowParallelFreeConnectivity_two`
records the refutation, and every statement here that consumes T1 carries the
size floor that keeps it clear.
-/
import Gtz.Uniform.AnchorReachAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz
namespace GeneralRankReach

open Matrix Finset

/-! ## The tuple space at general rank -/

/-- A row system has a parallel pair — the tuple-level mirror of
`Gtz.HasParallelPair`, with the same quantifier shape and the same
orientation. -/
def HasParallelRows {size rank : ℕ} (rows : Fin size → Fin rank → ℝ) : Prop :=
  ∃ (keptLabel dropLabel : Fin size) (ratio : ℝ),
    keptLabel ≠ dropLabel ∧ rows dropLabel = ratio • rows keptLabel

/-- The rows span, in the dual form every consumer below wants: only the zero
probe is orthogonal to every row. -/
def RowsSpan {size rank : ℕ} (rows : Fin size → Fin rank → ℝ) : Prop :=
  ∀ probe : Fin rank → ℝ, (∀ label, rows label ⬝ᵥ probe = 0) → probe = 0

/-- The good tuples: pairwise non-parallel and spanning.  These are exactly the
row systems of parallel-free designs after the weights are folded in. -/
def IsGoodTuple {size rank : ℕ} (rows : Fin size → Fin rank → ℝ) : Prop :=
  ¬ HasParallelRows rows ∧ RowsSpan rows

theorem noRatio_of_isGoodTuple {size rank : ℕ} {rows : Fin size → Fin rank → ℝ}
    (hgood : IsGoodTuple rows) {keptLabel dropLabel : Fin size}
    (hdistinct : keptLabel ≠ dropLabel) (ratio : ℝ) :
    rows dropLabel ≠ ratio • rows keptLabel :=
  fun hparallel => hgood.1 ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩

/-- Every row of a good tuple of at least two rows is nonzero: the zero vector
is parallel to everything. -/
theorem row_ne_zero_of_isGoodTuple {size rank : ℕ} (hsize : 2 ≤ size)
    {rows : Fin size → Fin rank → ℝ} (hgood : IsGoodTuple rows) (label : Fin size) :
    rows label ≠ 0 := by
  intro hzero
  have hzeroIdx : (0 : ℕ) < size := by omega
  have honeIdx : (1 : ℕ) < size := by omega
  rcases eq_or_ne label ⟨0, hzeroIdx⟩ with hatZero | hoffZero
  · refine noRatio_of_isGoodTuple hgood (keptLabel := ⟨1, honeIdx⟩) (dropLabel := label)
      (fun hcollide => ?_) 0 ?_
    · rw [hatZero] at hcollide
      exact absurd (congrArg Fin.val hcollide) (by norm_num)
    · rw [hzero, zero_smul]
  · refine noRatio_of_isGoodTuple hgood (keptLabel := ⟨0, hzeroIdx⟩) (dropLabel := label)
      (fun hcollide => hoffZero hcollide.symm) 0 ?_
    rw [hzero, zero_smul]

/-! ## The Gram matrix of a tuple

`gramOf rows` is the Parseval sum with the weights already folded into the
rows.  It is `1` exactly on the Parseval shell. -/

/-- The Gram matrix of a bare tuple. -/
def gramOf {size rank : ℕ} (rows : Fin size → Fin rank → ℝ) :
    Matrix (Fin rank) (Fin rank) ℝ :=
  ∑ label, atomMatrix (rows label)

/-- The Gram quadratic form is the sum of squared row dots. -/
theorem gramOf_form {size rank : ℕ} (rows : Fin size → Fin rank → ℝ)
    (probe : Fin rank → ℝ) :
    probe ⬝ᵥ ((gramOf rows).mulVec probe) = ∑ label, (rows label ⬝ᵥ probe) ^ 2 := by
  rw [gramOf, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [atomMatrix, Matrix.vecMulVec_mulVec, dotProduct_smul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, dotProduct_comm]
  ring

/-- A good tuple's Gram matrix is positive definite — spanning is exactly
non-degeneracy of the form, with no eigenvalue involved. -/
theorem posDef_gramOf_of_isGoodTuple {size rank : ℕ} {rows : Fin size → Fin rank → ℝ}
    (hgood : IsGoodTuple rows) : (gramOf rows).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hne => ?_⟩
  · exact (Matrix.posSemidef_sum Finset.univ
      fun label _ => posSemidef_atomMatrix (rows label)).1
  · rw [star_trivial, gramOf_form]
    have hnonneg : (0 : ℝ) ≤ ∑ label, (rows label ⬝ᵥ probe) ^ 2 :=
      Finset.sum_nonneg fun label _ => sq_nonneg _
    rcases hnonneg.lt_or_eq with hpos | hzero
    · exact hpos
    · exfalso
      have hall : ∀ label ∈ Finset.univ, (rows label ⬝ᵥ probe) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun label _ => sq_nonneg _).mp hzero.symm
      exact hne (hgood.2 probe fun label =>
        pow_eq_zero_iff two_ne_zero |>.mp (hall label (Finset.mem_univ label)))

/-- **The forward dictionary.**  The rows of a parallel-free design, weights
folded in, form a good tuple. -/
theorem isGoodTuple_designRows {size rank : ℕ} (design : WeightedDesign size rank)
    (hfree : ¬ HasParallelPair design) :
    IsGoodTuple (fun label => Real.sqrt (design.weight label) • design.atom label) := by
  constructor
  · rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
    have hkeptPos : (0 : ℝ) < Real.sqrt (design.weight keptLabel) :=
      Real.sqrt_pos.mpr (design.weight_pos keptLabel)
    have hdropPos : (0 : ℝ) < Real.sqrt (design.weight dropLabel) :=
      Real.sqrt_pos.mpr (design.weight_pos dropLabel)
    refine hfree ⟨keptLabel, dropLabel,
      ratio * Real.sqrt (design.weight keptLabel) / Real.sqrt (design.weight dropLabel),
      hdistinct, ?_⟩
    have hscaled := congrArg (fun vec => (Real.sqrt (design.weight dropLabel))⁻¹ • vec)
      hparallel
    simp only [smul_smul] at hscaled
    rw [inv_mul_cancel₀ (ne_of_gt hdropPos), one_smul] at hscaled
    rw [hscaled]
    congr 1
    rw [div_eq_mul_inv]
    ring
  · intro probe hprobe
    have hatomDot : ∀ label, design.atom label ⬝ᵥ probe = 0 := by
      intro label
      have hrow := hprobe label
      rw [smul_dotProduct, smul_eq_mul] at hrow
      exact (mul_eq_zero.mp hrow).resolve_left
        (ne_of_gt (Real.sqrt_pos.mpr (design.weight_pos label)))
    by_contra hne
    have hpos := selfDotProduct_pos hne
    have hform : probe ⬝ᵥ ((1 : Matrix (Fin rank) (Fin rank) ℝ).mulVec probe)
        = ∑ label, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 := by
      rw [← design.isParseval, Matrix.sum_mulVec, dotProduct_sum]
      refine Finset.sum_congr rfl fun label _ => ?_
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
        Matrix.vecMulVec_mulVec, dotProduct_smul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, dotProduct_comm]
      ring
    rw [Matrix.one_mulVec] at hform
    have hzeroSum : ∑ label, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 = 0 :=
      Finset.sum_eq_zero fun label _ => by rw [hatomDot label]; ring
    rw [hform, hzeroSum] at hpos
    exact lt_irrefl 0 hpos

/-- The rows of a design sit exactly on the Parseval shell. -/
theorem gramOf_designRows {size rank : ℕ} (design : WeightedDesign size rank) :
    gramOf (fun label => Real.sqrt (design.weight label) • design.atom label) = 1 := by
  rw [← design.isParseval, gramOf]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [atomMatrix_smul, Real.sq_sqrt (design.weight_pos label).le]

/-! ## The interpolated weight profile

The reach statement asks for a globally continuous atom path but only for
design witnesses on `[0, 1]`, so the weights ride a clamped interpolation.
`Gtz.clampUnit` is already rank-free, and only the profile needs restating. -/

/-- The clamped linear interpolation between two weight profiles, at general
size. -/
def weightBlend {size : ℕ} (weightStart weightEnd : Fin size → ℝ) (time : ℝ)
    (label : Fin size) : ℝ :=
  (1 - clampUnit time) * weightStart label + clampUnit time * weightEnd label

theorem weightBlend_pos {size : ℕ} {weightStart weightEnd : Fin size → ℝ}
    (hstartPos : ∀ label, 0 < weightStart label)
    (hendPos : ∀ label, 0 < weightEnd label) (time : ℝ) (label : Fin size) :
    0 < weightBlend weightStart weightEnd time label := by
  rcases lt_or_eq_of_le (clampUnit_le_one time) with hbelowOne | hatOne
  · have hfirst : 0 < (1 - clampUnit time) * weightStart label :=
      mul_pos (by linarith) (hstartPos label)
    have hsecond : 0 ≤ clampUnit time * weightEnd label :=
      mul_nonneg (clampUnit_nonneg time) (hendPos label).le
    rw [weightBlend]
    linarith
  · rw [weightBlend, hatOne]
    simpa using hendPos label

theorem weightBlend_sum {size : ℕ} {weightStart weightEnd : Fin size → ℝ}
    (hstartSum : ∑ label, weightStart label = 1)
    (hendSum : ∑ label, weightEnd label = 1) (time : ℝ) :
    ∑ label, weightBlend weightStart weightEnd time label = 1 := by
  simp only [weightBlend]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hstartSum, hendSum]
  ring

@[simp] theorem weightBlend_zero {size : ℕ} (weightStart weightEnd : Fin size → ℝ)
    (label : Fin size) :
    weightBlend weightStart weightEnd 0 label = weightStart label := by
  simp [weightBlend, clampUnit_zero]

@[simp] theorem weightBlend_one {size : ℕ} (weightStart weightEnd : Fin size → ℝ)
    (label : Fin size) :
    weightBlend weightStart weightEnd 1 label = weightEnd label := by
  simp [weightBlend, clampUnit_one]

theorem continuous_weightBlend_apply {size : ℕ} (weightStart weightEnd : Fin size → ℝ)
    (label : Fin size) :
    Continuous fun time => weightBlend weightStart weightEnd time label :=
  (((continuous_const.sub continuous_clampUnit).mul continuous_const).add
    (continuous_clampUnit.mul continuous_const))

/-- Invertible matrices cancel on `mulVec` — the engine that transports the
parallelism pattern back through the whitening mix. -/
theorem mulVec_cancel {rank : ℕ} {mix : Matrix (Fin rank) (Fin rank) ℝ}
    (hdet : mix.det ≠ 0) {leftVec rightVec : Fin rank → ℝ}
    (hequal : mix.mulVec leftVec = mix.mulVec rightVec) : leftVec = rightVec := by
  have hunit : IsUnit mix.det := isUnit_iff_ne_zero.mpr hdet
  have hleft := congrArg (fun vec => mix⁻¹.mulVec vec) hequal
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul mix hunit,
    Matrix.one_mulVec] using hleft

/-! ## The two topological inputs, at general size and rank -/

/-- **T1, THE TUPLE WALK.**  Any two good tuples are joined by a continuous
path of good tuples.  At `(6,3)` this is `Gtz.exists_goodTuple_path`. -/
def GoodTupleConnected (size rank : ℕ) : Prop :=
  ∀ rowsStart rowsEnd : Fin size → Fin rank → ℝ,
    IsGoodTuple rowsStart → IsGoodTuple rowsEnd →
      ∃ tuplePath : ℝ → Fin size → Fin rank → ℝ,
        Continuous tuplePath ∧ tuplePath 0 = rowsStart ∧ tuplePath 1 = rowsEnd
          ∧ ∀ time : ℝ, IsGoodTuple (tuplePath time)

/-- **T2, THE WHITENING INTERFACE.**  A continuous pointwise-spanning tuple path
with Parseval endpoints deforms onto the Parseval shell, endpoints fixed,
through a pointwise invertible linear mix.  At `(6,3)` this is
`Gtz.whiteningTransfer_holds`, by explicit Cholesky. -/
def WhiteningTransferAtRank (size rank : ℕ) : Prop :=
  ∀ tuplePath : ℝ → Fin size → Fin rank → ℝ, Continuous tuplePath →
    (∀ time, (gramOf (tuplePath time)).PosDef) →
    gramOf (tuplePath 0) = 1 → gramOf (tuplePath 1) = 1 →
    ∃ whitePath : ℝ → Fin size → Fin rank → ℝ,
      Continuous whitePath ∧ whitePath 0 = tuplePath 0 ∧ whitePath 1 = tuplePath 1
        ∧ (∀ time, gramOf (whitePath time) = 1)
        ∧ ∀ time, ∃ mix : Matrix (Fin rank) (Fin rank) ℝ, mix.det ≠ 0
            ∧ ∀ label, whitePath time label = mix.mulVec (tuplePath time label)

/-! ## T3, the composition — rank-uniform -/

/-- **THE REACH STATEMENT, FROM T1 AND T2, AT EVERY SIZE AND RANK.**  Fold both
designs into their row tuples, walk the tuple path, whiten back onto the
Parseval shell, and divide by the interpolated weight profile: every time slice
is a parallel-free design, and the endpoints are the two atom systems on the
nose. -/
theorem parallelFreeReachesAnchor_of_tupleReach {size rank : ℕ}
    (hwalk : GoodTupleConnected size rank) (hwhiten : WhiteningTransferAtRank size rank)
    (anchor : WeightedDesign size rank) (hanchorFree : ¬ HasParallelPair anchor) :
    ParallelFreeReachesAnchor size rank anchor := by
  intro design hdesignFree
  obtain ⟨tuplePath, hcont, hstart, hend, hgood⟩ :=
    hwalk (fun label => Real.sqrt (anchor.weight label) • anchor.atom label)
      (fun label => Real.sqrt (design.weight label) • design.atom label)
      (isGoodTuple_designRows anchor hanchorFree)
      (isGoodTuple_designRows design hdesignFree)
  obtain ⟨whitePath, hwhiteCont, hwhiteStart, hwhiteEnd, hwhiteGram, hwhiteMix⟩ :=
    hwhiten tuplePath hcont (fun time => posDef_gramOf_of_isGoodTuple (hgood time))
      (by rw [hstart]; exact gramOf_designRows anchor)
      (by rw [hend]; exact gramOf_designRows design)
  have hblendPos : ∀ time label, 0 < weightBlend anchor.weight design.weight time label :=
    fun time label => weightBlend_pos anchor.weight_pos design.weight_pos time label
  have hrootPos : ∀ time label,
      0 < Real.sqrt (weightBlend anchor.weight design.weight time label) :=
    fun time label => Real.sqrt_pos.mpr (hblendPos time label)
  refine ⟨fun time label =>
    (Real.sqrt (weightBlend anchor.weight design.weight time label))⁻¹
      • whitePath time label, ?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun label => ?_
    have hroot : Continuous fun time : ℝ =>
        Real.sqrt (weightBlend anchor.weight design.weight time label) :=
      Real.continuous_sqrt.comp (continuous_weightBlend_apply anchor.weight design.weight label)
    exact (hroot.inv₀ fun time => ne_of_gt (hrootPos time label)).smul
      ((continuous_apply label).comp hwhiteCont)
  · funext label
    show (Real.sqrt (weightBlend anchor.weight design.weight 0 label))⁻¹
        • whitePath 0 label = anchor.atom label
    rw [congrFun (hwhiteStart.trans hstart) label, weightBlend_zero, smul_smul,
      inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (anchor.weight_pos label))), one_smul]
  · funext label
    show (Real.sqrt (weightBlend anchor.weight design.weight 1 label))⁻¹
        • whitePath 1 label = design.atom label
    rw [congrFun (hwhiteEnd.trans hend) label, weightBlend_one, smul_smul,
      inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (design.weight_pos label))), one_smul]
  · intro time _htime
    refine ⟨⟨fun label =>
        (Real.sqrt (weightBlend anchor.weight design.weight time label))⁻¹
          • whitePath time label,
      weightBlend anchor.weight design.weight time, fun label => hblendPos time label,
      weightBlend_sum anchor.weight_sum_one design.weight_sum_one time, ?_⟩, rfl, ?_⟩
    · show ∑ label, weightBlend anchor.weight design.weight time label •
          atomMatrix ((Real.sqrt (weightBlend anchor.weight design.weight time label))⁻¹
            • whitePath time label) = 1
      have hterm : ∀ label, weightBlend anchor.weight design.weight time label •
          atomMatrix ((Real.sqrt (weightBlend anchor.weight design.weight time label))⁻¹
            • whitePath time label) = atomMatrix (whitePath time label) := by
        intro label
        rw [atomMatrix_smul, inv_pow, Real.sq_sqrt (hblendPos time label).le, smul_smul,
          mul_inv_cancel₀ (ne_of_gt (hblendPos time label)), one_smul]
      rw [Finset.sum_congr rfl fun label _ => hterm label]
      exact hwhiteGram time
    · rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
      have hscaled : (Real.sqrt (weightBlend anchor.weight design.weight time dropLabel))⁻¹
            • whitePath time dropLabel
          = ratio • (Real.sqrt (weightBlend anchor.weight design.weight time keptLabel))⁻¹
            • whitePath time keptLabel := hparallel
      have hcleared : whitePath time dropLabel
          = (Real.sqrt (weightBlend anchor.weight design.weight time dropLabel)
              * (ratio * (Real.sqrt (weightBlend anchor.weight design.weight time
                  keptLabel))⁻¹)) • whitePath time keptLabel := by
        have hmul := congrArg (fun vec =>
          Real.sqrt (weightBlend anchor.weight design.weight time dropLabel) • vec) hscaled
        simp only [smul_smul] at hmul
        rwa [mul_inv_cancel₀ (ne_of_gt (hrootPos time dropLabel)), one_smul] at hmul
      obtain ⟨mix, hdet, hmix⟩ := hwhiteMix time
      rw [hmix dropLabel, hmix keptLabel, ← Matrix.mulVec_smul] at hcleared
      exact (hgood time).1
        ⟨keptLabel, dropLabel, _, hdistinct, mulVec_cancel hdet hcleared⟩

/-! ## Chaining with the assembly

The anchor is free (`AnchorReachAssembly`), so T1 and T2 alone carry the whole
anchor-reach obligation. -/

/-- Connectivity over the canonical window, from T1 and T2 at every window
cell. -/
theorem canonicalWindowParallelFreeConnectivity_of_tupleReach {rank : ℕ}
    (hwalk : ∀ size : ℕ, InductionStep.IsInsideCanonicalWindow size rank →
      GoodTupleConnected size rank)
    (hwhiten : ∀ size : ℕ, InductionStep.IsInsideCanonicalWindow size rank →
      WhiteningTransferAtRank size rank) :
    UniformPositionBridge.CanonicalWindowParallelFreeConnectivity rank :=
  fun size hinside anchor hanchorFree =>
    parallelFreeReachesAnchor_of_tupleReach (hwalk size hinside) (hwhiten size hinside)
      anchor hanchorFree

/-- **THE ANCHOR-REACH OBLIGATION, REDUCED TO T1 AND T2.**  Same statement as
`Skeleton.obligationSharpWindowAnchorReachRankFourAndUp` at one rank, with the
tuple walk and the whitening interface as its only hypotheses.  Everything
else — the anchor, its strict domination, the Parseval balance, the block
reindexing — is a theorem. -/
theorem sharpWindowAnchorReach_of_tupleReach {rank : ℕ} (hrank : 3 ≤ rank)
    (hwalk : ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
      GoodTupleConnected size rank)
    (hwhiten : ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
      WhiteningTransferAtRank size rank) :
    ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
      ∃ anchor : WeightedDesign size rank,
        HasStrictlyDominatingSubset anchor ∧ ParallelFreeReachesAnchor size rank anchor := by
  refine UniformPositionBridge.sharpWindowAnchorReach_of_connectivity hrank ?_
  intro size hbelow habove anchor hanchorFree
  exact parallelFreeReachesAnchor_of_tupleReach (hwalk size hbelow habove)
    (hwhiten size hbelow habove) anchor hanchorFree

/-- **ROUTE (b), ON THREE INPUTS.**  The relativized window hinge, the tuple
walk and the whitening interface give weighted GTZ at every size and every
rank.  No anchor, no domination estimate, and no hinge production appears. -/
theorem routeB_target_of_tupleReach
    (hwindowTie : ∀ rank : ℕ, 3 ≤ rank →
      UniformPositionBridge.ParallelPairAtWindowTieRelative rank)
    (hwalk : ∀ rank : ℕ, 3 ≤ rank → ∀ size : ℕ,
      InductionStep.IsInsideCanonicalWindow size rank → GoodTupleConnected size rank)
    (hwhiten : ∀ rank : ℕ, 3 ≤ rank → ∀ size : ℕ,
      InductionStep.IsInsideCanonicalWindow size rank → WhiteningTransferAtRank size rank) :
    ∀ size rank : ℕ, 1 ≤ rank → rank ≤ size → GtzWeighted size rank :=
  UniformPositionBridge.routeB_target_of_connectivity hwindowTie
    (fun rank hrank => canonicalWindowParallelFreeConnectivity_of_tupleReach
      (hwalk rank hrank) (hwhiten rank hrank))

/-! ## Mechanism parity at rank three

Both inputs are theorems at `(6,3)`, and the general-rank composition returns
the landed reach theorem from them.  Nothing here is weaker than what the tree
already proves. -/

/-- T1 at `(6,3)`, from the moment-curve walk. -/
theorem goodTupleConnected_six_three : GoodTupleConnected 6 3 :=
  fun _ _ hgoodStart hgoodEnd => exists_goodTuple_path hgoodStart hgoodEnd

/-- T2 at `(6,3)`, from the explicit Cholesky whitening. -/
theorem whiteningTransferAtRank_six_three : WhiteningTransferAtRank 6 3 :=
  whiteningTransfer_holds

/-- **PARITY.**  The general-rank composition, fed the two rank-three inputs,
reproduces the landed `Gtz.parallelFreeReachesAnchor_six_three` — for EVERY
parallel-free anchor at `(6,3)`, not only the icosahedron. -/
theorem parallelFreeReachesAnchor_six_three_ofAnyAnchor
    (anchor : WeightedDesign 6 3) (hanchorFree : ¬ HasParallelPair anchor) :
    ParallelFreeReachesAnchor 6 3 anchor :=
  parallelFreeReachesAnchor_of_tupleReach goodTupleConnected_six_three
    whiteningTransferAtRank_six_three anchor hanchorFree

/-- **The rank-three window is closed on the reach side, at every anchor.**  The
canonical window at rank three is `{6, 7}`, and the reach input is a theorem at
size six — recorded here as the instance of the general residual that the tree
already owns. -/
theorem canonicalWindowParallelFreeConnectivity_six :
    ∀ anchor : WeightedDesign 6 3, ¬ HasParallelPair anchor →
      ParallelFreeReachesAnchor 6 3 anchor :=
  parallelFreeReachesAnchor_six_three_ofAnyAnchor

/-- **The reach half at `(6,3)` needs no named anchor at all.**  The assembly
supplies a parallel-free strictly dominating design and the walk reaches it, so
the pair that route (b) consumes at the bottom rank-three cell is a theorem
without `Gtz.icosaDesign`. -/
theorem exists_anchorReach_six_three :
    ∃ anchor : WeightedDesign 6 3,
      HasStrictlyDominatingSubset anchor ∧ ParallelFreeReachesAnchor 6 3 anchor := by
  obtain ⟨anchor, hanchorFree, hanchorStrict⟩ :=
    UniformPositionBridge.exists_parallelFreeStrictAnchor_sixThree
  exact ⟨anchor, hanchorStrict, parallelFreeReachesAnchor_six_three_ofAnyAnchor anchor
    hanchorFree⟩

/-! ## Toward T1: the moment curve and the single move, at general rank

The rank-three walk steers one row at a time through a moment-curve waypoint,
and reads "off the line of `u`" through a cross product.  A cross product is a
rank-three object.  Its role is only to supply a NONZERO vector orthogonal to
two given vectors, and at every rank of three or more that vector exists for a
cheaper reason: two rows cannot fill a space of dimension three or more, so the
matrix carrying them as its first two rows is singular. -/

/-- The matrix whose two named rows are the given vectors and whose other rows
vanish. -/
def pairRowMatrix {rank : ℕ} (firstRow secondRow : Fin rank)
    (first second : Fin rank → ℝ) : Matrix (Fin rank) (Fin rank) ℝ :=
  fun rowIndex =>
    if rowIndex = firstRow then first else if rowIndex = secondRow then second else 0

@[simp] theorem pairRowMatrix_first {rank : ℕ} (firstRow secondRow : Fin rank)
    (first second : Fin rank → ℝ) :
    pairRowMatrix firstRow secondRow first second firstRow = first := by
  rw [pairRowMatrix, if_pos rfl]

theorem pairRowMatrix_second {rank : ℕ} {firstRow secondRow : Fin rank}
    (hdistinct : secondRow ≠ firstRow) (first second : Fin rank → ℝ) :
    pairRowMatrix firstRow secondRow first second secondRow = second := by
  rw [pairRowMatrix, if_neg hdistinct, if_pos rfl]

theorem pairRowMatrix_other {rank : ℕ} {firstRow secondRow other : Fin rank}
    (hfirst : other ≠ firstRow) (hsecond : other ≠ secondRow)
    (first second : Fin rank → ℝ) :
    pairRowMatrix firstRow secondRow first second other = 0 := by
  rw [pairRowMatrix, if_neg hfirst, if_neg hsecond]

/-- **THE NORMAL TO A PAIR, at every rank of three or more.**  Two vectors leave
a nonzero direction orthogonal to both.  This replaces the cross product of the
rank-three walk, and it is the exact point where rank two dies: at rank two the
matrix below has no third row to vanish. -/
theorem exists_normal_of_pair {rank : ℕ} (hrank : 3 ≤ rank) (first second : Fin rank → ℝ) :
    ∃ normal : Fin rank → ℝ, normal ≠ 0 ∧ first ⬝ᵥ normal = 0 ∧ second ⬝ᵥ normal = 0 := by
  classical
  have hzeroLt : 0 < rank := by omega
  have honeLt : 1 < rank := by omega
  have htwoLt : 2 < rank := by omega
  have hsecondNeFirst : (⟨1, honeLt⟩ : Fin rank) ≠ ⟨0, hzeroLt⟩ := by
    simp [Fin.ext_iff]
  have hthirdNeFirst : (⟨2, htwoLt⟩ : Fin rank) ≠ ⟨0, hzeroLt⟩ := by
    simp [Fin.ext_iff]
  have hthirdNeSecond : (⟨2, htwoLt⟩ : Fin rank) ≠ ⟨1, honeLt⟩ := by
    simp [Fin.ext_iff]
  have hdet : (pairRowMatrix (⟨0, hzeroLt⟩ : Fin rank) ⟨1, honeLt⟩ first second).det = 0 := by
    refine Matrix.det_eq_zero_of_row_eq_zero (⟨2, htwoLt⟩ : Fin rank) fun coord => ?_
    rw [pairRowMatrix_other hthirdNeFirst hthirdNeSecond]
    rfl
  obtain ⟨normal, hnormalNe, hkill⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hrowKill : ∀ rowIndex : Fin rank,
      pairRowMatrix (⟨0, hzeroLt⟩ : Fin rank) ⟨1, honeLt⟩ first second rowIndex ⬝ᵥ normal
        = 0 := by
    intro rowIndex
    have hentry := congrFun hkill rowIndex
    simpa [Matrix.mulVec] using hentry
  refine ⟨normal, hnormalNe, ?_, ?_⟩
  · have hrow := hrowKill ⟨0, hzeroLt⟩
    rwa [pairRowMatrix_first] at hrow
  · have hrow := hrowKill ⟨1, honeLt⟩
    rwa [pairRowMatrix_second hsecondNeFirst] at hrow

/-! ### The moment curve -/

/-- The moment curve in `ℝ^rank`: `param ↦ (1, param, param², ...)`. -/
def momentPoint (rank : ℕ) (param : ℝ) : Fin rank → ℝ :=
  fun coord => param ^ (coord : ℕ)

@[simp] theorem momentPoint_apply (rank : ℕ) (param : ℝ) (coord : Fin rank) :
    momentPoint rank param coord = param ^ (coord : ℕ) := rfl

theorem momentPoint_apply_zero {rank : ℕ} (hrank : 1 ≤ rank) (param : ℝ) :
    momentPoint rank param ⟨0, by omega⟩ = 1 := by
  simp

theorem momentPoint_apply_one {rank : ℕ} (hrank : 2 ≤ rank) (param : ℝ) :
    momentPoint rank param ⟨1, by omega⟩ = param := by
  simp

theorem momentPoint_dotProduct {rank : ℕ} (param : ℝ) (coeffs : Fin rank → ℝ) :
    momentPoint rank param ⬝ᵥ coeffs = ∑ index, coeffs index * param ^ (index : ℕ) := by
  rw [dotProduct]
  exact Finset.sum_congr rfl fun index _ => by rw [momentPoint_apply, mul_comm]

theorem momentPoint_ne_zero {rank : ℕ} (hrank : 1 ≤ rank) (param : ℝ) :
    momentPoint rank param ≠ 0 := by
  intro hzero
  have hatZero := congrFun hzero (⟨0, by omega⟩ : Fin rank)
  rw [momentPoint_apply_zero hrank, Pi.zero_apply] at hatZero
  exact one_ne_zero hatZero

/-- Distinct parameters give non-parallel moment points: the leading coordinate
pins the ratio to one, the second then pins the parameter. -/
theorem momentPoint_offLine {rank : ℕ} (hrank : 2 ≤ rank) {leftParam rightParam : ℝ}
    (hdistinct : leftParam ≠ rightParam) (ratio : ℝ) :
    momentPoint rank leftParam ≠ ratio • momentPoint rank rightParam := by
  intro hparallel
  have hatZero := congrFun hparallel ⟨0, by omega⟩
  have hatOne := congrFun hparallel ⟨1, by omega⟩
  rw [momentPoint_apply_zero (by omega), Pi.smul_apply,
    momentPoint_apply_zero (by omega), smul_eq_mul, mul_one] at hatZero
  rw [momentPoint_apply_one hrank, Pi.smul_apply, momentPoint_apply_one hrank,
    smul_eq_mul, ← hatZero, one_mul] at hatOne
  exact hdistinct hatOne

/-- At most ONE parameter puts the moment point on a fixed line: the leading
coordinate forces the ratio and the second coordinate then forces the
parameter.  No nonvanishing hypothesis on the line is needed. -/
theorem subsingleton_setOf_momentPoint_parallel {rank : ℕ} (hrank : 2 ≤ rank)
    (direction : Fin rank → ℝ) :
    {param : ℝ | ∃ ratio : ℝ, momentPoint rank param = ratio • direction}.Subsingleton := by
  obtain ⟨leadCoord, hleadVal⟩ : ∃ coord : Fin rank, (coord : ℕ) = 0 :=
    ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨nextCoord, hnextVal⟩ : ∃ coord : Fin rank, (coord : ℕ) = 1 :=
    ⟨⟨1, by omega⟩, rfl⟩
  have hlead : ∀ param : ℝ, momentPoint rank param leadCoord = 1 := by
    intro param
    rw [momentPoint_apply, hleadVal, pow_zero]
  have hnext : ∀ param : ℝ, momentPoint rank param nextCoord = param := by
    intro param
    rw [momentPoint_apply, hnextVal, pow_one]
  rintro leftParam ⟨leftRatio, hleft⟩ rightParam ⟨rightRatio, hright⟩
  have hpin : ∀ param ratio : ℝ, momentPoint rank param = ratio • direction →
      param * direction leadCoord = direction nextCoord := by
    intro param ratio hparallel
    have hatZero := congrFun hparallel leadCoord
    have hatOne := congrFun hparallel nextCoord
    rw [hlead, Pi.smul_apply, smul_eq_mul] at hatZero
    rw [hnext, Pi.smul_apply, smul_eq_mul] at hatOne
    linear_combination (-(direction nextCoord)) * hatZero + direction leadCoord * hatOne
  have hleadNe : direction leadCoord ≠ 0 := by
    intro hzero
    have hatZero := congrFun hleft leadCoord
    rw [hlead, Pi.smul_apply, smul_eq_mul, hzero, mul_zero] at hatZero
    exact one_ne_zero hatZero
  have hcombined : (leftParam - rightParam) * direction leadCoord = 0 := by
    rw [sub_mul, hpin leftParam leftRatio hleft, hpin rightParam rightRatio hright, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcombined).resolve_right hleadNe)

theorem finite_setOf_momentPoint_parallel {rank : ℕ} (hrank : 2 ≤ rank)
    (direction : Fin rank → ℝ) :
    {param : ℝ | ∃ ratio : ℝ, momentPoint rank param = ratio • direction}.Finite :=
  (subsingleton_setOf_momentPoint_parallel hrank direction).finite

/-! ### Root counting: the moment curve meets a hyperplane finitely often -/

/-- The polynomial whose evaluation is the moment dot product. -/
noncomputable def dotPolynomial {rank : ℕ} (coeffs : Fin rank → ℝ) : Polynomial ℝ :=
  ∑ index : Fin rank, Polynomial.monomial (index : ℕ) (coeffs index)

theorem eval_dotPolynomial {rank : ℕ} (coeffs : Fin rank → ℝ) (param : ℝ) :
    (dotPolynomial coeffs).eval param = ∑ index, coeffs index * param ^ (index : ℕ) := by
  rw [dotPolynomial, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun index _ => Polynomial.eval_monomial

theorem dotPolynomial_ne_zero {rank : ℕ} {coeffs : Fin rank → ℝ} (hne : coeffs ≠ 0) :
    dotPolynomial coeffs ≠ 0 := by
  obtain ⟨witness, hwitness⟩ := Function.ne_iff.mp hne
  intro hzero
  have hcoeff : (dotPolynomial coeffs).coeff (witness : ℕ) = coeffs witness := by
    rw [dotPolynomial, Polynomial.finsetSum_coeff,
      Finset.sum_eq_single witness
        (fun other _ hother => by
          rw [Polynomial.coeff_monomial, if_neg fun hval => hother (Fin.ext hval)])
        (fun habsent => absurd (Finset.mem_univ witness) habsent),
      Polynomial.coeff_monomial, if_pos rfl]
  rw [hzero, Polynomial.coeff_zero] at hcoeff
  exact hwitness (by simpa using hcoeff.symm)

/-- **A nonzero normal is met finitely often.**  The moment dot product is a
polynomial of degree less than the rank, so it has at most `rank - 1` roots. -/
theorem finite_setOf_momentPoint_dot_eq_zero {rank : ℕ} {normal : Fin rank → ℝ}
    (hne : normal ≠ 0) :
    {param : ℝ | momentPoint rank param ⬝ᵥ normal = 0}.Finite := by
  refine Set.Finite.subset (Polynomial.finite_setOf_isRoot (dotPolynomial_ne_zero hne))
    fun param hparam => ?_
  rw [Set.mem_setOf_eq, momentPoint_dotProduct] at hparam
  rw [Set.mem_setOf_eq, Polynomial.IsRoot, eval_dotPolynomial]
  exact hparam

/-! ### Vandermonde: moment points at distinct parameters span -/

theorem det_vandermonde_ne_zero {rank : ℕ} {params : Fin rank → ℝ}
    (hinjective : Function.Injective params) : (Matrix.vandermonde params).det ≠ 0 := by
  rw [Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun leftIndex _ =>
    Finset.prod_ne_zero_iff.mpr fun rightIndex hmem => ?_
  have hlt : leftIndex < rightIndex := Finset.mem_Ioi.mp hmem
  exact sub_ne_zero.mpr fun hvalue => (ne_of_gt hlt) (hinjective hvalue)

/-- **THE SPANNING CERTIFICATE.**  `rank` moment points at distinct parameters
span, so only the zero probe is orthogonal to all of them. -/
theorem probe_eq_zero_of_momentPoints {rank : ℕ} {params : Fin rank → ℝ}
    (hinjective : Function.Injective params) {probe : Fin rank → ℝ}
    (hkill : ∀ index, momentPoint rank (params index) ⬝ᵥ probe = 0) : probe = 0 := by
  refine Matrix.eq_zero_of_mulVec_eq_zero (det_vandermonde_ne_zero hinjective) ?_
  funext index
  rw [Pi.zero_apply, ← hkill index]
  simp [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]

/-- The spanning certificate with the parameters carried by an arbitrary index
type of at least `rank` values — the shape the walk consumes, where the placed
labels are a subset of the design's labels. -/
theorem probe_eq_zero_of_manyMomentPoints {rank : ℕ} {index : Type} [Fintype index]
    {params : index → ℝ} (hinjective : Function.Injective params)
    (hcard : rank ≤ Fintype.card index) {probe : Fin rank → ℝ}
    (hkill : ∀ label : index, momentPoint rank (params label) ⬝ᵥ probe = 0) : probe = 0 := by
  obtain ⟨pick⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin rank) ≤ Fintype.card index by rwa [Fintype.card_fin])
  exact probe_eq_zero_of_momentPoints (params := fun slot => params (pick slot))
    (fun leftSlot rightSlot hvalue => pick.injective (hinjective hvalue))
    fun slot => hkill (pick slot)

/-! ### Straight segments, and the avoidance mechanism -/

/-- The straight segment, as a globally defined map. -/
def segment {rank : ℕ} (start finish : Fin rank → ℝ) (param : ℝ) : Fin rank → ℝ :=
  (1 - param) • start + param • finish

@[simp] theorem segment_zero {rank : ℕ} (start finish : Fin rank → ℝ) :
    segment start finish 0 = start := by
  simp [segment]

@[simp] theorem segment_one {rank : ℕ} (start finish : Fin rank → ℝ) :
    segment start finish 1 = finish := by
  simp [segment]

theorem continuous_segment {rank : ℕ} (start finish : Fin rank → ℝ) :
    Continuous (segment start finish) :=
  (((continuous_const.sub continuous_id).smul continuous_const).add
    (continuous_id.smul continuous_const))

/-- **THE AVOIDANCE MECHANISM, at general rank.**  A segment leaving a start
that is off the line of `direction`, toward a waypoint certified against a
normal that kills both the start and the direction, never meets that line: at
every positive parameter the certificate forbids it, and at parameter zero the
start does. -/
theorem segment_avoids_line {rank : ℕ} {start waypoint direction normal : Fin rank → ℝ}
    (hstartNormal : start ⬝ᵥ normal = 0) (hdirectionNormal : direction ⬝ᵥ normal = 0)
    (hwaypointNormal : waypoint ⬝ᵥ normal ≠ 0)
    (hstartOff : ∀ ratio : ℝ, start ≠ ratio • direction) (param ratio : ℝ) :
    segment start waypoint param ≠ ratio • direction := by
  intro hmeet
  have hdotSegment : segment start waypoint param ⬝ᵥ normal
      = param * (waypoint ⬝ᵥ normal) := by
    rw [segment, add_dotProduct, smul_dotProduct, smul_dotProduct, hstartNormal,
      smul_zero, zero_add, smul_eq_mul]
  have hdotLine : (ratio • direction) ⬝ᵥ normal = 0 := by
    rw [smul_dotProduct, hdirectionNormal, smul_zero]
  rw [hmeet, hdotLine] at hdotSegment
  have hparamZero : param = 0 :=
    (mul_eq_zero.mp hdotSegment.symm).resolve_right hwaypointNormal
  rw [hparamZero, segment_zero] at hmeet
  exact hstartOff ratio hmeet

/-! ### Single-coordinate moves inside the good tuples -/

/-- The good tuples as a set, the ambient space of every `JoinedIn` below. -/
def goodTupleSet (size rank : ℕ) : Set (Fin size → Fin rank → ℝ) :=
  {rows | IsGoodTuple rows}

/-- Non-parallelism transfers across the pair. -/
theorem offLine_symm {rank : ℕ} {base mover : Fin rank → ℝ} (hbase : base ≠ 0)
    (hoff : ∀ ratio : ℝ, mover ≠ ratio • base) (ratio : ℝ) : base ≠ ratio • mover := by
  intro hparallel
  rcases eq_or_ne ratio 0 with rfl | hratioNe
  · rw [zero_smul] at hparallel
    exact hbase hparallel
  · refine hoff ratio⁻¹ ?_
    rw [hparallel, smul_smul, inv_mul_cancel₀ hratioNe, one_smul]

/-- Updating one row to a mover off every other row's line keeps the tuple good,
provided the other rows span on their own. -/
theorem isGoodTuple_update {size rank : ℕ} (hsize : 2 ≤ size)
    {rows : Fin size → Fin rank → ℝ} (hgood : IsGoodTuple rows) (movingLabel : Fin size)
    {mover : Fin rank → ℝ}
    (hmoverOff : ∀ other, other ≠ movingLabel → ∀ ratio : ℝ, mover ≠ ratio • rows other)
    (hothersSpan : ∀ probe : Fin rank → ℝ,
      (∀ other, other ≠ movingLabel → rows other ⬝ᵥ probe = 0) → probe = 0) :
    IsGoodTuple (Function.update rows movingLabel mover) := by
  classical
  constructor
  · rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
    rcases eq_or_ne dropLabel movingLabel with rfl | hdropOff
    · rw [Function.update_self, Function.update_of_ne hdistinct] at hparallel
      exact hmoverOff keptLabel hdistinct ratio hparallel
    · rcases eq_or_ne keptLabel movingLabel with rfl | hkeptOff
      · rw [Function.update_of_ne hdropOff, Function.update_self] at hparallel
        exact offLine_symm (row_ne_zero_of_isGoodTuple hsize hgood dropLabel)
          (hmoverOff dropLabel hdropOff) ratio hparallel
      · rw [Function.update_of_ne hdropOff, Function.update_of_ne hkeptOff] at hparallel
        exact noRatio_of_isGoodTuple hgood hdistinct ratio hparallel
  · intro probe hprobe
    refine hothersSpan probe fun other hother => ?_
    have hrow := hprobe other
    rwa [Function.update_of_ne hother] at hrow

/-- One straight leg of a move, packaged as a `JoinedIn`. -/
theorem joinedIn_update_segment {size rank : ℕ}
    {ambient : Set (Fin size → Fin rank → ℝ)} {rows : Fin size → Fin rank → ℝ}
    (movingLabel : Fin size) (target : Fin rank → ℝ)
    (hstays : ∀ param : ℝ,
      Function.update rows movingLabel (segment (rows movingLabel) target param) ∈ ambient) :
    JoinedIn ambient rows (Function.update rows movingLabel target) := by
  classical
  refine ⟨⟨⟨fun time => Function.update rows movingLabel
      (segment (rows movingLabel) target (time : ℝ)), ?_⟩, ?_, ?_⟩, fun time => hstays _⟩
  · exact continuous_const.update movingLabel
      ((continuous_segment _ _).comp continuous_subtype_val)
  · show Function.update rows movingLabel
      (segment (rows movingLabel) target ((0 : unitInterval) : ℝ)) = rows
    rw [Set.Icc.coe_zero, segment_zero, Function.update_eq_self]
  · show Function.update rows movingLabel
      (segment (rows movingLabel) target ((1 : unitInterval) : ℝ))
        = Function.update rows movingLabel target
    rw [Set.Icc.coe_one, segment_one]

/-- **THE SINGLE MOVE, at general rank.**  If the target is off every other
row's line and the other rows span on their own, the tuple joins its update
inside the good tuples.  The path runs through a moment-curve waypoint chosen
against finitely many polynomials of degree less than the rank — two for each
of the other rows. -/
theorem joinedIn_moveOne {size rank : ℕ} (hsize : 2 ≤ size) (hrank : 3 ≤ rank)
    {rows : Fin size → Fin rank → ℝ} (hgood : IsGoodTuple rows) (movingLabel : Fin size)
    {target : Fin rank → ℝ}
    (htargetOff : ∀ other, other ≠ movingLabel → ∀ ratio : ℝ, target ≠ ratio • rows other)
    (hothersSpan : ∀ probe : Fin rank → ℝ,
      (∀ other, other ≠ movingLabel → rows other ⬝ᵥ probe = 0) → probe = 0) :
    JoinedIn (goodTupleSet size rank) rows (Function.update rows movingLabel target) := by
  classical
  choose startNormal hstartNormalNe hstartNormalKillsStart hstartNormalKillsRow using
    fun other : Fin size => exists_normal_of_pair hrank (rows movingLabel) (rows other)
  choose targetNormal htargetNormalNe htargetNormalKillsTarget htargetNormalKillsRow using
    fun other : Fin size => exists_normal_of_pair hrank target (rows other)
  have hbad : (⋃ other ∈ Finset.univ.erase movingLabel,
      ({param : ℝ | momentPoint rank param ⬝ᵥ startNormal other = 0}
        ∪ {param : ℝ | momentPoint rank param ⬝ᵥ targetNormal other = 0})).Finite := by
    refine Set.Finite.biUnion (Finset.univ.erase movingLabel).finite_toSet fun other _ => ?_
    exact (finite_setOf_momentPoint_dot_eq_zero (hstartNormalNe other)).union
      (finite_setOf_momentPoint_dot_eq_zero (htargetNormalNe other))
  obtain ⟨param, hparam⟩ := exists_param_avoiding hbad
  have hcertStart : ∀ other, other ≠ movingLabel →
      momentPoint rank param ⬝ᵥ startNormal other ≠ 0 := by
    intro other hother hzero
    exact hparam (Set.mem_biUnion (Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩)
      (Set.mem_union_left _ hzero))
  have hcertTarget : ∀ other, other ≠ movingLabel →
      momentPoint rank param ⬝ᵥ targetNormal other ≠ 0 := by
    intro other hother hzero
    exact hparam (Set.mem_biUnion (Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩)
      (Set.mem_union_right _ hzero))
  have hstartOff : ∀ other, other ≠ movingLabel → ∀ ratio : ℝ,
      rows movingLabel ≠ ratio • rows other := fun other hother ratio =>
    noRatio_of_isGoodTuple hgood hother ratio
  have hlegOne : JoinedIn (goodTupleSet size rank) rows
      (Function.update rows movingLabel (momentPoint rank param)) := by
    refine joinedIn_update_segment movingLabel (momentPoint rank param) fun segParam => ?_
    exact isGoodTuple_update hsize hgood movingLabel
      (fun other hother ratio => segment_avoids_line (hstartNormalKillsStart other)
        (hstartNormalKillsRow other) (hcertStart other hother) (hstartOff other hother)
        segParam ratio)
      hothersSpan
  have hlegTwo : JoinedIn (goodTupleSet size rank)
      (Function.update rows movingLabel target)
      (Function.update rows movingLabel (momentPoint rank param)) := by
    have hcollapse : Function.update (Function.update rows movingLabel target) movingLabel
        (momentPoint rank param) = Function.update rows movingLabel (momentPoint rank param) :=
      Function.update_idem ..
    have hbase : (Function.update rows movingLabel target) movingLabel = target :=
      Function.update_self ..
    have hleg := joinedIn_update_segment (ambient := goodTupleSet size rank)
      (rows := Function.update rows movingLabel target) movingLabel
      (momentPoint rank param) ?_
    · rwa [hcollapse] at hleg
    · intro segParam
      rw [Function.update_idem, hbase]
      exact isGoodTuple_update hsize hgood movingLabel
        (fun other hother ratio => segment_avoids_line (htargetNormalKillsTarget other)
          (htargetNormalKillsRow other) (hcertTarget other hother)
          (htargetOff other hother) segParam ratio)
        hothersSpan
  exact hlegOne.trans hlegTwo.symm

/-! ### From `JoinedIn` to the T1 Prop -/

/-- The globally defined path version of T1: a `JoinedIn`-connected good-tuple
space supplies the continuous `ℝ`-parameterized family that the composition
consumes. -/
theorem goodTupleConnected_of_joinedIn {size rank : ℕ}
    (hjoined : ∀ rowsStart rowsEnd : Fin size → Fin rank → ℝ,
      IsGoodTuple rowsStart → IsGoodTuple rowsEnd →
        JoinedIn (goodTupleSet size rank) rowsStart rowsEnd) :
    GoodTupleConnected size rank := by
  intro rowsStart rowsEnd hgoodStart hgoodEnd
  obtain ⟨joinPath, hjoinMem⟩ := hjoined rowsStart rowsEnd hgoodStart hgoodEnd
  refine ⟨joinPath.extend, joinPath.continuous_extend, joinPath.extend_zero,
    joinPath.extend_one, fun time => ?_⟩
  rcases le_or_gt time 0 with hlow | habove
  · rw [joinPath.extend_of_le_zero hlow]
    exact hgoodStart
  · rcases le_or_gt 1 time with hhigh | hbelow
    · rw [joinPath.extend_of_one_le hhigh]
      exact hgoodEnd
    · have hmem : time ∈ Set.Icc (0 : ℝ) 1 := ⟨habove.le, hbelow.le⟩
      rw [joinPath.extend_extends' ⟨time, hmem⟩]
      exact hjoinMem ⟨time, hmem⟩

/-! ### The residual of T1, named

Everything above is a general-rank theorem.  What the rank-three walk does that
this file does not yet do is the SCHEDULE: order the moves so that the rows
left untouched always span.  At rank three that is a fixed tripod plus three
explicit steps.  At general rank the window supplies the room —
`Gtz.UniformPositionBridge.windowCell_meets_walkSchedule` gives
`2 * rank <= size`, so `rank` rows can stay fixed while the other `size - rank`
walk onto the curve, and the placed moment points then span by
`probe_eq_zero_of_manyMomentPoints` while the fixed rows follow. -/

/-- **THE SCHEDULE, named.**  Every good tuple reaches a moment-curve hub inside
the good tuples.  This is all that separates the single move above from T1. -/
def GoodTupleReachesMomentHub (size rank : ℕ) : Prop :=
  ∀ (rows : Fin size → Fin rank → ℝ) (params : Fin size → ℝ),
    IsGoodTuple rows → Function.Injective params →
      (∀ label other : Fin size, ∀ ratio : ℝ,
        momentPoint rank (params label) ≠ ratio • rows other) →
      JoinedIn (goodTupleSet size rank) rows (fun label => momentPoint rank (params label))

/-- **T1 FROM THE SCHEDULE.**  Two good tuples reach a common hub whose
parameters avoid the finitely many parallel-parameters of either tuple, so the
schedule alone yields the tuple walk. -/
theorem goodTupleConnected_of_reachesMomentHub {size rank : ℕ} (hrank : 2 ≤ rank)
    (hhub : GoodTupleReachesMomentHub size rank) : GoodTupleConnected size rank := by
  refine goodTupleConnected_of_joinedIn fun rowsStart rowsEnd hgoodStart hgoodEnd => ?_
  have hbad : (⋃ other : Fin size,
      ({param : ℝ | ∃ ratio : ℝ, momentPoint rank param = ratio • rowsStart other}
        ∪ {param : ℝ | ∃ ratio : ℝ, momentPoint rank param = ratio • rowsEnd other})).Finite :=
    Set.finite_iUnion fun other =>
      (finite_setOf_momentPoint_parallel hrank (rowsStart other)).union
        (finite_setOf_momentPoint_parallel hrank (rowsEnd other))
  obtain ⟨params, hinjective, havoid⟩ := exists_params_avoiding size hbad
  have hhubStart := hhub rowsStart params hgoodStart hinjective
    (fun label other ratio hparallel => havoid label
      (Set.mem_iUnion.mpr ⟨other, Set.mem_union_left _ ⟨ratio, hparallel⟩⟩))
  have hhubEnd := hhub rowsEnd params hgoodEnd hinjective
    (fun label other ratio hparallel => havoid label
      (Set.mem_iUnion.mpr ⟨other, Set.mem_union_right _ ⟨ratio, hparallel⟩⟩))
  exact hhubStart.trans hhubEnd.symm

/-- **THE ANCHOR-REACH OBLIGATION, ON THE SCHEDULE AND THE WHITENING.**  With the
assembly, the composition and the moment-curve calculus all discharged, the
sharp-window statement rests on two topological Props per cell. -/
theorem sharpWindowAnchorReach_of_schedule {rank : ℕ} (hrank : 3 ≤ rank)
    (hhub : ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
      GoodTupleReachesMomentHub size rank)
    (hwhiten : ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
      WhiteningTransferAtRank size rank) :
    ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
      ∃ anchor : WeightedDesign size rank,
        HasStrictlyDominatingSubset anchor ∧ ParallelFreeReachesAnchor size rank anchor :=
  sharpWindowAnchorReach_of_tupleReach hrank
    (fun size hbelow habove => goodTupleConnected_of_reachesMomentHub (by omega)
      (hhub size hbelow habove))
    hwhiten

end GeneralRankReach
end Gtz

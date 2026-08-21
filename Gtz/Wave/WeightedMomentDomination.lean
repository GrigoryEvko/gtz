/-
# The weighted-moment criterion, and the universal filter the tie tower imposes

## 1. A domination criterion that reads the WEIGHTED moment

Domination is a statement about the UNWEIGHTED atom sum `S_C = Σ_{c ∈ C} g_c g_cᵀ`,
while Parseval controls the WEIGHTED moment `M_C = Σ_{c ∈ C} t_c g_c g_cᵀ`.  One
inequality connects them.  If `cap` bounds the weights inside `C`, then for every
probe

  `cap · Σ_{c ∈ C} (g_c · x)² ≥ Σ_{c ∈ C} t_c (g_c · x)² = xᵀ M_C x` ,

so `M_C ⪰ cap · I` already forces `S_C ⪰ I`:

  **`Gtz.dominates_of_weightedMoment_ge`** , and its strict twin
  **`Gtz.posDef_subsetSum_sub_one_of_weightedMoment_gt`** .

The criterion is rank-free and size-free, it consumes weight positivity through
the cap alone, and it needs no determinant, no minor and no eigenvalue.  Two
immediate readings:

* **`Gtz.posDef_subsetSum_univ_sub_one`**: the WHOLE atom set of any design with
  at least two atoms dominates STRICTLY, because `M_univ = I` and every weight is
  below one.  Hence **`Gtz.not_isTie_of_size_eq_rank`**: there is no tie at
  `size = rank`, at any rank of two or more.  That is the floor of the tie tower.
* **`Gtz.isTie_outside_mass_floor`**: at a tie, every selection leaves at least
  `1 - cap` of the Parseval mass OUTSIDE itself, in some direction.  This is the
  general-rank form of the campaign's outside-mass ledgers, with no funnel and no
  rank-three bracket.

## 2. The universal filter

`Gtz.exists_isTie_of_succ_rank_le` (Gtz/Wave/BandTieTower.lean) puts an exact tie
at every cell of every rank from size `rank + 1` up.  A tie refuses every strict
dominator by definition.  So:

  **`Gtz.not_forall_exists_posDef`: NO criterion that produces a STRICTLY
  dominating selection at every design can hold at any cell from size `rank + 1`
  up, at any rank of three or more.**

That is a filter on producers, not a statement about GTZ.  It explains, at every
rank at once, why the campaign's excess-dominance producers for the two
general-rank registry axioms were refuted one cell at a time: every one of them
asserts a strict dominator at every design of its cell, and every such assertion
refutes its own antecedent.  The weighted-moment gate below is refuted by the
same theorem, and is recorded as refuted rather than offered as a route.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Quantitative.GeneralPositionWindow
import Gtz.Wave.BandTieTower

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. The two quadratic forms -/

/-- The weighted moment of a selection, `M_C = Σ_{c ∈ C} t_c g_c g_cᵀ`.  Parseval
says the moment of the whole index set is the identity. -/
noncomputable def weightedMoment (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    Matrix (Fin k) (Fin k) ℝ :=
  ∑ c ∈ selected, D.weight c • atomMatrix (D.atom c)

theorem weightedMoment_univ (D : WeightedDesign m k) :
    weightedMoment D Finset.univ = 1 := D.isParseval

/-- The quadratic form of the unweighted atom sum. -/
theorem dotProduct_subsetSum_finset_mulVec (D : WeightedDesign m k) (selected : Finset (Fin m))
    (probe : Fin k → ℝ) :
    probe ⬝ᵥ (subsetSum D selected *ᵥ probe)
      = ∑ c ∈ selected, (D.atom c ⬝ᵥ probe) ^ 2 := by
  rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun c _ => dotProduct_atomMatrix_mulVec (D.atom c) probe

/-- The quadratic form of the weighted moment. -/
theorem dotProduct_weightedMoment_mulVec (D : WeightedDesign m k) (selected : Finset (Fin m))
    (probe : Fin k → ℝ) :
    probe ⬝ᵥ (weightedMoment D selected *ᵥ probe)
      = ∑ c ∈ selected, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 :=
  dotProduct_sum_smul_atomMatrix_mulVec D.weight D.atom selected probe

theorem posSemidef_weightedMoment (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    (weightedMoment D selected).PosSemidef :=
  Matrix.posSemidef_sum selected fun c _ =>
    (posSemidef_atomMatrix (D.atom c)).smul (D.weight_pos c).le

-- `Gtz.posSemidef_subsetSum` (Gtz/Reduction/ExchangeInvariant.lean),
-- `Gtz.isHermitian_subsetSum_sub_one` and
-- `Gtz.posDef_subsetSum_univ_sub_one` (Gtz/Quantitative/GlobalMinimumRankThree.lean)
-- are already in the tree with exactly these statements.  They are imported, not
-- re-derived.  The single-pass name scan caught three collisions here.

theorem isHermitian_weightedMoment_sub_smul_one (D : WeightedDesign m k)
    (selected : Finset (Fin m)) (cap : ℝ) :
    (weightedMoment D selected - cap • (1 : Matrix (Fin k) (Fin k) ℝ)).IsHermitian := by
  refine (posSemidef_weightedMoment D selected).1.sub ?_
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]

/-! ## 2. The criterion

The single inequality is `cap · (g_c · x)² ≥ t_c · (g_c · x)²` at every inside
label, summed. -/

/-- The cap inequality, summed over the selection. -/
theorem weightedMoment_le_smul_subsetSum (D : WeightedDesign m k) (selected : Finset (Fin m))
    {cap : ℝ} (hcap : ∀ c ∈ selected, D.weight c ≤ cap) (probe : Fin k → ℝ) :
    probe ⬝ᵥ (weightedMoment D selected *ᵥ probe)
      ≤ cap * (probe ⬝ᵥ (subsetSum D selected *ᵥ probe)) := by
  rw [dotProduct_weightedMoment_mulVec, dotProduct_subsetSum_finset_mulVec, Finset.mul_sum]
  refine Finset.sum_le_sum fun c hc => ?_
  exact mul_le_mul_of_nonneg_right (hcap c hc) (sq_nonneg _)

/-- **THE WEIGHTED-MOMENT DOMINATION CRITERION.**  A selection whose weighted
moment clears `cap · I` dominates, as soon as `cap` bounds its own weights. -/
theorem dominates_of_weightedMoment_ge (D : WeightedDesign m k) (selected : Finset (Fin m))
    {cap : ℝ} (hcapPos : 0 < cap) (hcap : ∀ c ∈ selected, D.weight c ≤ cap)
    (hmoment : (weightedMoment D selected
      - cap • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef) :
    Dominates D selected := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨(Matrix.posSemidef_sum selected fun c _ =>
        posSemidef_atomMatrix (D.atom c)).1.sub Matrix.isHermitian_one, ?_⟩
  intro probe
  rw [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
  have hfloor : cap * (probe ⬝ᵥ probe) ≤ probe ⬝ᵥ (weightedMoment D selected *ᵥ probe) := by
    have hstep := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hmoment).2 probe
    rw [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul] at hstep
    linarith
  have hcapBound := weightedMoment_le_smul_subsetSum D selected hcap probe
  have hchain : cap * (probe ⬝ᵥ probe)
      ≤ cap * (probe ⬝ᵥ (subsetSum D selected *ᵥ probe)) := le_trans hfloor hcapBound
  have hcancel : probe ⬝ᵥ probe ≤ probe ⬝ᵥ (subsetSum D selected *ᵥ probe) :=
    le_of_mul_le_mul_left hchain hcapPos
  linarith

/-- **THE STRICT WEIGHTED-MOMENT CRITERION.** -/
theorem posDef_subsetSum_sub_one_of_weightedMoment_gt (D : WeightedDesign m k)
    (selected : Finset (Fin m)) {cap : ℝ} (hcapPos : 0 < cap)
    (hcap : ∀ c ∈ selected, D.weight c ≤ cap)
    (hmoment : (weightedMoment D selected
      - cap • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef) :
    (subsetSum D selected - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨(Matrix.posSemidef_sum selected fun c _ =>
        posSemidef_atomMatrix (D.atom c)).1.sub Matrix.isHermitian_one, ?_⟩
  intro probe hne
  rw [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
  have hstrict : cap * (probe ⬝ᵥ probe) < probe ⬝ᵥ (weightedMoment D selected *ᵥ probe) := by
    have hstep := (Matrix.posDef_iff_dotProduct_mulVec.mp hmoment).2 hne
    rw [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul] at hstep
    linarith
  have hcapBound := weightedMoment_le_smul_subsetSum D selected hcap probe
  have hchain : cap * (probe ⬝ᵥ probe)
      < cap * (probe ⬝ᵥ (subsetSum D selected *ᵥ probe)) := lt_of_lt_of_le hstrict hcapBound
  have hcancel : probe ⬝ᵥ probe < probe ⬝ᵥ (subsetSum D selected *ᵥ probe) :=
    lt_of_mul_lt_mul_left (by linarith) hcapPos.le
  linarith

/-! ## 3. The whole atom set, and the floor of the tie tower -/

/-- **THERE IS NO TIE AT `size = rank`**, at any rank of two or more.  This is the
floor of the tie tower of Gtz/Wave/BandTieTower.lean: ties inhabit every cell from
`rank + 1` up, and none at all at `rank`. -/
theorem not_isTie_of_size_eq_rank {rank : ℕ} (hrank : 2 ≤ rank)
    (D : WeightedDesign rank rank) : ¬ IsTie D := by
  intro htie
  refine htie.2 Finset.univ ?_ (posDef_subsetSum_univ_sub_one D hrank)
  rw [Finset.card_univ, Fintype.card_fin]

/-! ## 4. What a tie owes on the outside -/

/-- **THE OUTSIDE-MASS FLOOR AT A TIE.**  At a tie no selection clears the cap, so
every selection admits a direction in which its own weighted mass is at most
`cap`, and Parseval hands the rest to the complement. -/
theorem isTie_outside_mass_floor (D : WeightedDesign m k) (htie : IsTie D)
    (selected : Finset (Fin m)) (hcard : selected.card = k) {cap : ℝ} (hcapPos : 0 < cap)
    (hcap : ∀ c ∈ selected, D.weight c ≤ cap) :
    ∃ probe : Fin k → ℝ, probe ≠ 0 ∧
      ∑ c ∈ selected, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 ≤ cap * (probe ⬝ᵥ probe) := by
  by_contra hcontra
  push Not at hcontra
  refine htie.2 selected hcard
    (posDef_subsetSum_sub_one_of_weightedMoment_gt D selected hcapPos hcap ?_)
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_weightedMoment_sub_smul_one D selected cap, ?_⟩
  intro probe hne
  have hstep := hcontra probe hne
  rw [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_weightedMoment_mulVec]
  linarith

/-- The same law read through Parseval: the complement of any selection carries at
least `1 - cap` of the mass in that direction. -/
theorem isTie_complement_mass_floor (D : WeightedDesign m k) (htie : IsTie D)
    (selected : Finset (Fin m)) (hcard : selected.card = k) {cap : ℝ} (hcapPos : 0 < cap)
    (hcap : ∀ c ∈ selected, D.weight c ≤ cap) :
    ∃ probe : Fin k → ℝ, probe ≠ 0 ∧
      (1 - cap) * (probe ⬝ᵥ probe)
        ≤ ∑ c ∈ Finset.univ \ selected, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 := by
  classical
  obtain ⟨probe, hne, hinside⟩ :=
    isTie_outside_mass_floor D htie selected hcard hcapPos hcap
  refine ⟨probe, hne, ?_⟩
  have htotal : ∑ c : Fin m, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 = probe ⬝ᵥ probe := by
    have hparseval := dotProduct_weightedMoment_mulVec D Finset.univ probe
    rw [weightedMoment_univ, Matrix.one_mulVec] at hparseval
    exact hparseval.symm
  have hsplit : ∑ c ∈ Finset.univ \ selected, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2
      = (∑ c : Fin m, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2)
        - ∑ c ∈ selected, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 :=
    Finset.sum_sdiff_eq_sub (Finset.subset_univ selected)
  rw [hsplit, htotal]
  linarith

/-! ## 5. The universal filter on producers -/

/-- **NO STRICT-DOMINATION PRODUCER SURVIVES AT ANY CELL FROM SIZE `rank + 1` UP.**
The tie tower puts an exact tie at every such cell, and a tie refuses every strict
dominator.

WHY THIS MATTERS FOR THE REGISTRY.  Every excess-dominance producer of
`Skeleton.obligationSubThresholdBandHinge` and of
`Skeleton.obligationThresholdCellHingeRankFourAndUp` asserts a strictly dominating
selection at every design of its cell.  The campaign refuted those producers one
cell at a time with graphic designs.  This theorem refutes the whole SHAPE, at
every cell of every rank at once, and it does so from the tie tower rather than
from any particular witness. -/
theorem not_forall_exists_posDef {rank size : ℕ} (hthree : 3 ≤ rank)
    (hsize : rank + 1 ≤ size) :
    ¬ (∀ D : WeightedDesign size rank, ∃ C : Finset (Fin size), C.card = rank
        ∧ (subsetSum D C - 1).PosDef) := by
  obtain ⟨D, htie⟩ := exists_isTie_of_succ_rank_le hthree hsize
  intro hproducer
  obtain ⟨C, hcard, hposDef⟩ := hproducer D
  exact htie.2 C hcard hposDef

/-- The weighted-moment gate: a selection at every design whose weighted moment
strictly clears its own weight cap. -/
def WeightedMomentGate (size rank : ℕ) : Prop :=
  ∀ D : WeightedDesign size rank, ∃ (C : Finset (Fin size)) (cap : ℝ),
    C.card = rank ∧ 0 < cap ∧ (∀ c ∈ C, D.weight c ≤ cap)
      ∧ (weightedMoment D C - cap • (1 : Matrix (Fin rank) (Fin rank) ℝ)).PosDef

/-- **THE WEIGHTED-MOMENT GATE IS REFUTED AT EVERY CELL FROM SIZE `rank + 1` UP.**
Recorded as refuted at the moment it is defined, so that no successor spends a
cycle on it.  The criterion of section 2 stays useful at ONE design at a time. -/
theorem not_weightedMomentGate {rank size : ℕ} (hthree : 3 ≤ rank) (hsize : rank + 1 ≤ size) :
    ¬ WeightedMomentGate size rank := by
  intro hgate
  refine not_forall_exists_posDef hthree hsize fun D => ?_
  obtain ⟨C, cap, hcard, hcapPos, hcap, hmoment⟩ := hgate D
  exact ⟨C, hcard, posDef_subsetSum_sub_one_of_weightedMoment_gt D C hcapPos hcap hmoment⟩

/-- The filter at the threshold cell of rank three. -/
theorem not_forall_exists_posDef_sixThree :
    ¬ (∀ D : WeightedDesign 6 3, ∃ C : Finset (Fin 6), C.card = 3
        ∧ (subsetSum D C - 1).PosDef) :=
  not_forall_exists_posDef (by norm_num) (by norm_num)

/-- The filter at the first band cell of rank four. -/
theorem not_forall_exists_posDef_eightFour :
    ¬ (∀ D : WeightedDesign 8 4, ∃ C : Finset (Fin 8), C.card = 4
        ∧ (subsetSum D C - 1).PosDef) :=
  not_forall_exists_posDef (by norm_num) (by norm_num)

/-- The filter at the threshold cell of rank four. -/
theorem not_forall_exists_posDef_tenFour :
    ¬ (∀ D : WeightedDesign 10 4, ∃ C : Finset (Fin 10), C.card = 4
        ∧ (subsetSum D C - 1).PosDef) :=
  not_forall_exists_posDef (by norm_num) (by norm_num)

end Gtz

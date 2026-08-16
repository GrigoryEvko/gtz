/-
# The corank-one co-leverage criterion is an equivalence

`Gtz.dominates_of_sum_coLeverageRatio_le_one` is SUFFICIENT at every size and rank:
a `k`-subset whose co-leverage ratios total at most one dominates.  Its docstring
records that at `m = k + 1` the converse holds too, and that the proof "would need
`rank (I − P) = 1`, which the repository does not supply".

`Gtz.exists_orthonormalFrame_of_symmetric_idempotent` supplies it.  The complementary
projection is symmetric, idempotent, and of trace `m − k`, so at corank one it factors
through a single column: `I − P = q qᵀ` with `q ⬝ᵥ q = 1`.  The co-leverage score of a
label is then the square of that label's entry, and the block criterion becomes a
rank-one test against a positive diagonal, which Cauchy-Schwarz decides exactly.

## What is proved here

* `Gtz.exists_coVector_corankOne` — the rank-one factor of `I − P` at `m = k + 1`.
* `Gtz.sum_coLeverageRatio_le_one_of_dominates` — the MISSING direction.
* `Gtz.corankOne_dominates_iff_sum_coLeverageRatio_le_one` — the equivalence.
* `Gtz.corankOne_posDef_gap_iff_sum_coLeverageRatio_lt_one` — the strict twin.
* `Gtz.corankOne_isTie_iff_forall_sum_coLeverageRatio_eq_one` — the tie reading.

## Scope

Corank one only.  The converse is FALSE from `(4,2)` up, and the repository already
refutes it there, so the corank hypothesis is not removable.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Certificates.ResidueDissolution
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.DiagonalRungs
import Gtz.Reduction.ChartPointFactorisation
import Gtz.Wave.ProjectionBlockObjective
import Gtz.Ties.TotalTieCorankOne
import Gtz.Ties.CorankOneTieCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Finset Matrix

variable {m k : ℕ}

/-! ## Part 1: the rank-one factor of the complementary projection -/

theorem trace_complementProjection (D : WeightedDesign m k) :
    Matrix.trace (complementProjection D) = (m : ℝ) - (k : ℝ) := by
  rw [complementProjection, Matrix.trace_sub, trace_projectionOfDesign]
  simp

/-- **AT CORANK ONE THE COMPLEMENTARY PROJECTION IS A SQUARE.**  Symmetric,
idempotent and of trace one, so it factors through one column: `I − P = q qᵀ` with
`q` a unit vector of the index space. -/
theorem exists_coVector_corankOne (D : WeightedDesign (k + 1) k) :
    ∃ coVector : Fin (k + 1) → ℝ,
      (∑ index, coVector index * coVector index) = 1
        ∧ ∀ leftIndex rightIndex, complementProjection D leftIndex rightIndex
            = coVector leftIndex * coVector rightIndex := by
  have htrace : Matrix.trace (complementProjection D) = ((1 : ℕ) : ℝ) := by
    rw [trace_complementProjection]
    push_cast
    ring
  obtain ⟨frame, hortho, hfactor⟩ :=
    exists_orthonormalFrame_of_symmetric_idempotent (complementProjection D)
      (complementProjection_transpose D) (complementProjection_mul_self D) htrace
  refine ⟨fun index => frame index 0, ?_, ?_⟩
  · have hentry := congrFun (congrFun hortho 0) 0
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at hentry
    simpa [Matrix.transpose_apply] using hentry
  · intro leftIndex rightIndex
    have hentry := congrFun (congrFun hfactor leftIndex) rightIndex
    rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.transpose_apply] at hentry
    exact hentry.symm

theorem coLeverageScore_eq_sq_coVector (D : WeightedDesign (k + 1) k)
    {coVector : Fin (k + 1) → ℝ}
    (hentry : ∀ leftIndex rightIndex, complementProjection D leftIndex rightIndex
      = coVector leftIndex * coVector rightIndex) (index : Fin (k + 1)) :
    coLeverageScore D index = coVector index * coVector index := by
  rw [← complementProjection_diagonal, hentry]

/-! ## Part 2: the missing direction -/

/-- **THE CONVERSE OF THE CO-LEVERAGE CRITERION AT CORANK ONE.**  A dominating
`k`-subset has co-leverage ratios of total mass at most one.  The rank-one factor
turns the block gap into `diag (1 − t) − q qᵀ` on the selected slots, and the probe
`q_c / (1 − t_c)` reads the quadratic form as `β (1 − β)`. -/
theorem sum_coLeverageRatio_le_one_of_dominates (hk : 1 ≤ k) (D : WeightedDesign (k + 1) k)
    (selected : Finset (Fin (k + 1))) (hcard : selected.card = k)
    (hdominates : Dominates D selected) :
    ∑ atomIndex ∈ selected, coLeverageRatio D atomIndex ≤ 1 := by
  classical
  have hm : 2 ≤ k + 1 := by omega
  obtain ⟨coVector, _, hentry⟩ := exists_coVector_corankOne D
  set pick := selected.orderEmbOfFin hcard with hpickDef
  have hinj : Function.Injective pick := (selected.orderEmbOfFin hcard).injective
  have hcoWeightPos : ∀ slot : Fin k, 0 < 1 - D.weight (pick slot) := fun slot => by
    linarith [weight_lt_one D hm (pick slot)]
  set probe : Fin k → ℝ := fun slot => coVector (pick slot) / (1 - D.weight (pick slot))
    with hprobeDef
  set mass : ℝ := ∑ slot, coVector (pick slot) * probe slot with hmassDef
  have hmassEq : mass = ∑ atomIndex ∈ selected, coLeverageRatio D atomIndex := by
    rw [hmassDef, ← sum_orderEmbOfFin_eq_sum selected hcard (coLeverageRatio D)]
    refine Finset.sum_congr rfl fun slot _ => ?_
    simp only [hprobeDef, coLeverageRatio, coLeverageScore_eq_sq_coVector D hentry]
    ring
  have hmassNonneg : 0 ≤ mass := by
    rw [hmassDef]
    refine Finset.sum_nonneg fun slot _ => ?_
    have hterm : coVector (pick slot) * probe slot
        = coVector (pick slot) ^ 2 / (1 - D.weight (pick slot)) := by
      simp only [hprobeDef]; ring
    rw [hterm]
    exact div_nonneg (sq_nonneg _) (hcoWeightPos slot).le
  have hpsd : (Matrix.diagonal (fun slot => 1 - D.weight (pick slot))
      - (complementProjection D).submatrix pick pick).PosSemidef := by
    rw [← projectionBlock_sub_weightDiagonal_eq_coWeight_sub_complementBlock D pick hinj]
    exact (dominates_iff_posSemidef_projectionBlock_finset D selected hcard).mp hdominates
  have hrow : ∀ slot : Fin k, ((Matrix.diagonal (fun other => 1 - D.weight (pick other))
      - (complementProjection D).submatrix pick pick) *ᵥ probe) slot
      = coVector (pick slot) * (1 - mass) := by
    intro slot
    rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
    have hdiag : (1 - D.weight (pick slot)) * probe slot = coVector (pick slot) := by
      have hne := (hcoWeightPos slot).ne'
      rw [hprobeDef]
      field_simp
    have hoff : ((complementProjection D).submatrix pick pick *ᵥ probe) slot
        = coVector (pick slot) * mass := by
      rw [Matrix.mulVec, dotProduct, hmassDef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun other _ => ?_
      rw [Matrix.submatrix_apply, hentry]
      ring
    rw [hdiag, hoff]
    ring
  have hform : probe ⬝ᵥ ((Matrix.diagonal (fun slot => 1 - D.weight (pick slot))
      - (complementProjection D).submatrix pick pick) *ᵥ probe) = mass * (1 - mass) := by
    rw [dotProduct]
    have hterm : ∀ slot : Fin k, probe slot
        * ((Matrix.diagonal (fun other => 1 - D.weight (pick other))
            - (complementProjection D).submatrix pick pick) *ᵥ probe) slot
        = (coVector (pick slot) * probe slot) * (1 - mass) := by
      intro slot
      rw [hrow slot]
      ring
    rw [Finset.sum_congr rfl fun slot _ => hterm slot, ← Finset.sum_mul, ← hmassDef]
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 probe
  rw [star_trivial, hform] at hnonneg
  rcases eq_or_lt_of_le hmassNonneg with hzero | hpos
  · rw [hmassEq] at hzero
    linarith
  · rw [← hmassEq]
    nlinarith [hnonneg, hpos]

/-- **THE CO-LEVERAGE CRITERION IS AN EQUIVALENCE AT CORANK ONE.** -/
theorem corankOne_dominates_iff_sum_coLeverageRatio_le_one (hk : 1 ≤ k)
    (D : WeightedDesign (k + 1) k) (selected : Finset (Fin (k + 1)))
    (hcard : selected.card = k) :
    Dominates D selected ↔ ∑ atomIndex ∈ selected, coLeverageRatio D atomIndex ≤ 1 :=
  ⟨sum_coLeverageRatio_le_one_of_dominates hk D selected hcard,
    dominates_of_sum_coLeverageRatio_le_one D (by omega) selected hcard⟩

/-! ## Part 3: the strict twin -/

/-- **STRICT DOMINATION AT CORANK ONE IS STRICT CO-LEVERAGE MASS.**  Cauchy-Schwarz
against the co-weights in one direction, the same probe in the other. -/
theorem corankOne_posDef_gap_iff_sum_coLeverageRatio_lt_one (hk : 1 ≤ k)
    (D : WeightedDesign (k + 1) k) (selected : Finset (Fin (k + 1)))
    (hcard : selected.card = k) :
    (subsetSum D selected - 1).PosDef
      ↔ ∑ atomIndex ∈ selected, coLeverageRatio D atomIndex < 1 := by
  classical
  have hm : 2 ≤ k + 1 := by omega
  obtain ⟨coVector, _, hentry⟩ := exists_coVector_corankOne D
  set pick := selected.orderEmbOfFin hcard with hpickDef
  have hinj : Function.Injective pick := (selected.orderEmbOfFin hcard).injective
  have hcoWeightPos : ∀ slot : Fin k, 0 < 1 - D.weight (pick slot) := fun slot => by
    linarith [weight_lt_one D hm (pick slot)]
  set mass : ℝ := ∑ atomIndex ∈ selected, coLeverageRatio D atomIndex with hmassDef
  have hslotMass : ∑ slot, coVector (pick slot) * coVector (pick slot)
      / (1 - D.weight (pick slot)) = mass := by
    rw [hmassDef, ← sum_orderEmbOfFin_eq_sum selected hcard (coLeverageRatio D)]
    refine Finset.sum_congr rfl fun slot _ => ?_
    rw [coLeverageRatio, coLeverageScore_eq_sq_coVector D hentry]
  have hgap : (subsetSum D selected - 1).PosDef
      ↔ (Matrix.diagonal (fun slot => 1 - D.weight (pick slot))
          - (complementProjection D).submatrix pick pick).PosDef := by
    exact posDef_subsetSum_iff_coweight_sub_complementBlock D selected hcard
  rw [hgap]
  constructor
  · intro hposDef
    by_contra hcontra
    push Not at hcontra
    have hle : mass ≤ 1 := by
      rw [hmassDef]
      exact sum_coLeverageRatio_le_one_of_dominates hk D selected hcard
        ((dominates_iff_posSemidef_projectionBlock_finset D selected hcard).mpr
          (by rw [projectionBlock_sub_weightDiagonal_eq_coWeight_sub_complementBlock D pick hinj]
              exact hposDef.posSemidef))
    have hmassOne : mass = 1 := le_antisymm hle hcontra
    set probe : Fin k → ℝ := fun slot => coVector (pick slot) / (1 - D.weight (pick slot))
      with hprobeDef
    have hprobeMass : ∑ slot, coVector (pick slot) * probe slot = 1 := by
      have hrewrite : ∀ slot : Fin k, coVector (pick slot) * probe slot
          = coVector (pick slot) * coVector (pick slot) / (1 - D.weight (pick slot)) :=
        fun slot => by simp only [hprobeDef]; ring
      rw [Finset.sum_congr rfl fun slot _ => hrewrite slot, hslotMass, hmassOne]
    have hprobeNe : probe ≠ 0 := by
      intro hzero
      rw [hzero] at hprobeMass
      simp at hprobeMass
    have hrow : ∀ slot : Fin k, ((Matrix.diagonal (fun other => 1 - D.weight (pick other))
        - (complementProjection D).submatrix pick pick) *ᵥ probe) slot = 0 := by
      intro slot
      rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
      have hdiag : (1 - D.weight (pick slot)) * probe slot = coVector (pick slot) := by
        have hne := (hcoWeightPos slot).ne'
        simp only [hprobeDef]
        field_simp
      have hoff : ((complementProjection D).submatrix pick pick *ᵥ probe) slot
          = coVector (pick slot) := by
        rw [Matrix.mulVec, dotProduct]
        have hstep : ∀ other : Fin k,
            ((complementProjection D).submatrix pick pick) slot other * probe other
            = coVector (pick slot) * (coVector (pick other) * probe other) := by
          intro other
          rw [Matrix.submatrix_apply, hentry]
          ring
        rw [Finset.sum_congr rfl fun other _ => hstep other, ← Finset.mul_sum, hprobeMass,
          mul_one]
      rw [hdiag, hoff, sub_self]
    have hquad := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobeNe
    rw [star_trivial, dotProduct] at hquad
    rw [Finset.sum_congr rfl fun slot _ => by rw [hrow slot, mul_zero]] at hquad
    simp at hquad
  · intro hlt
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_of_transpose_eq ?_,
      fun testVec hne => ?_⟩
    · rw [Matrix.transpose_sub, Matrix.diagonal_transpose, Matrix.transpose_submatrix,
        complementProjection_transpose]
    · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
      have hdiag : testVec ⬝ᵥ (Matrix.diagonal (fun slot => 1 - D.weight (pick slot))
          *ᵥ testVec) = ∑ slot, (1 - D.weight (pick slot)) * testVec slot ^ 2 := by
        rw [dotProduct]
        exact Finset.sum_congr rfl fun slot _ => by rw [Matrix.mulVec_diagonal]; ring
      have hrank : testVec ⬝ᵥ ((complementProjection D).submatrix pick pick *ᵥ testVec)
          = (∑ slot, coVector (pick slot) * testVec slot) ^ 2 := by
        rw [dotProduct, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun leftSlot _ => ?_
        rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun rightSlot _ => ?_
        rw [Matrix.submatrix_apply, hentry]
        ring
      rw [hdiag, hrank]
      -- Cauchy-Schwarz against the co-weights
      have hcs : (∑ slot, coVector (pick slot) * testVec slot) ^ 2
          ≤ (∑ slot, coVector (pick slot) * coVector (pick slot) / (1 - D.weight (pick slot)))
            * ∑ slot, (1 - D.weight (pick slot)) * testVec slot ^ 2 := by
        have hsplit : ∀ slot : Fin k, coVector (pick slot) * testVec slot
            = (coVector (pick slot) / Real.sqrt (1 - D.weight (pick slot)))
              * (Real.sqrt (1 - D.weight (pick slot)) * testVec slot) := by
          intro slot
          have hsqrtNe : Real.sqrt (1 - D.weight (pick slot)) ≠ 0 :=
            ne_of_gt (Real.sqrt_pos.mpr (hcoWeightPos slot))
          field_simp
        rw [Finset.sum_congr rfl fun slot _ => hsplit slot]
        refine le_trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun slot => coVector (pick slot) / Real.sqrt (1 - D.weight (pick slot)))
          (fun slot => Real.sqrt (1 - D.weight (pick slot)) * testVec slot)) (le_of_eq ?_)
        refine congrArg₂ _ (Finset.sum_congr rfl fun slot _ => ?_)
          (Finset.sum_congr rfl fun slot _ => ?_)
        · rw [div_pow, Real.sq_sqrt (hcoWeightPos slot).le]
          ring
        · rw [mul_pow, Real.sq_sqrt (hcoWeightPos slot).le]
      have hquadPos : 0 < ∑ slot, (1 - D.weight (pick slot)) * testVec slot ^ 2 := by
        obtain ⟨slot, hslot⟩ := Function.ne_iff.mp hne
        refine Finset.sum_pos' (fun other _ =>
          mul_nonneg (hcoWeightPos other).le (sq_nonneg _)) ⟨slot, Finset.mem_univ slot, ?_⟩
        have hslotNe : testVec slot ≠ 0 := by simpa using hslot
        exact mul_pos (hcoWeightPos slot) ((sq_nonneg (testVec slot)).lt_of_ne
          (Ne.symm (pow_ne_zero 2 hslotNe)))
      rw [hslotMass] at hcs
      nlinarith [hcs, hquadPos, hlt]

/-! ## Part 4: the tie reading -/

/-- **A CORANK-ONE TIE IS TOTAL CO-LEVERAGE MASS ONE ON EVERY SUBSET.** -/
theorem corankOne_isTie_iff_forall_sum_coLeverageRatio_eq_one (hk : 1 ≤ k)
    (D : WeightedDesign (k + 1) k) :
    IsTie D ↔ ∀ selected : Finset (Fin (k + 1)), selected.card = k →
      ∑ atomIndex ∈ selected, coLeverageRatio D atomIndex = 1 := by
  constructor
  · intro htie selected hcard
    have hle := sum_coLeverageRatio_le_one_of_dominates hk D selected hcard
      (corankOne_isTie_dominates hk D htie hcard)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact absurd
        ((corankOne_posDef_gap_iff_sum_coLeverageRatio_lt_one hk D selected hcard).mpr hlt)
        (htie.2 selected hcard)
    · exact heq
  · intro hmass
    refine ⟨?_, fun selected hcard hposDef => ?_⟩
    · obtain ⟨dropped, hcard, hdominates⟩ := exists_erase_dominates_of_corank_one hk D
      exact ⟨Finset.univ.erase dropped, hcard, hdominates⟩
    · have hlt := (corankOne_posDef_gap_iff_sum_coLeverageRatio_lt_one hk D selected
        hcard).mp hposDef
      rw [hmass selected hcard] at hlt
      exact lt_irrefl 1 hlt

/-! ## Part 5: the regression against the landed corank-one tie criterion -/

/-- **THE TWO CORANK-ONE READINGS AGREE.**  `Gtz.isTie_iff_leverage_identity` pins
`k t_c l_c = (k - 1) + t_c` at every label of a tie.  That is exactly a co-leverage
ratio of `1/k`, so every `k`-subset of a tie carries total mass one — which is what
`Gtz.corankOne_isTie_iff_forall_sum_coLeverageRatio_eq_one` says, by a route that
shares no lemma with it. -/
theorem coLeverageRatio_eq_inv_rank_of_isTie (hk : 1 ≤ k) (D : WeightedDesign (k + 1) k)
    (htie : IsTie D) (atomIndex : Fin (k + 1)) :
    coLeverageRatio D atomIndex = 1 / (k : ℝ) := by
  have hm : 2 ≤ k + 1 := by omega
  have hidentity := (isTie_iff_leverage_identity hk D).mp htie atomIndex
  have hcoWeightPos : 0 < 1 - D.weight atomIndex := by
    linarith [weight_lt_one D hm atomIndex]
  have hrankPos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [coLeverageRatio, coLeverageScore]
  rw [div_eq_div_iff (ne_of_gt hcoWeightPos) (ne_of_gt hrankPos)]
  nlinarith [hidentity]

/-- The regression itself: the landed criterion delivers the total mass one that the
new equivalence predicts. -/
theorem sum_coLeverageRatio_eq_one_of_isTie_viaLeverageIdentity (hk : 1 ≤ k)
    (D : WeightedDesign (k + 1) k) (htie : IsTie D) (selected : Finset (Fin (k + 1)))
    (hcard : selected.card = k) :
    ∑ atomIndex ∈ selected, coLeverageRatio D atomIndex = 1 := by
  have hrankNe : ((k : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact ne_of_gt this
  rw [Finset.sum_congr rfl fun atomIndex _ =>
    coLeverageRatio_eq_inv_rank_of_isTie hk D htie atomIndex, Finset.sum_const, hcard,
    nsmul_eq_mul]
  field_simp

end Gtz

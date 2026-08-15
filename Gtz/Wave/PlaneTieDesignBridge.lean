import Gtz.Wave.PlaneTieClassification
import Gtz.Design.RankTwoTieCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The exact plane tie in weighted-design coordinates

`PlaneTieClassification` works with an abstract Parseval family in `R^2`, while
the reduction and Schur layers work with `WeightedDesign`, `subsetSum`,
`Matrix.PosSemidef`, and `Matrix.PosDef`.  This module is the lossless dictionary
between those interfaces.

For a weighted `(3,2)` design, its scaled atom rows form the abstract plane
frame.  Plane weak/strict domination then agrees exactly with PSD/PD of the
core pair gap, and the closed plane tie equation agrees exactly with `IsTie`.
The capstone exports every tied pair as a nonparallel PSD-singular gap together
with an explicit nonzero vector in its `mulVec` kernel.  This is the form used
by bordered-determinant and rank-one Schur consumers; it is stronger than a
determinant-zero statement and introduces no new obligation.
-/

namespace Gtz

open Matrix Finset

theorem scaledAtomRows_planeParseval {size : ℕ} (design : WeightedDesign size 2) :
    PlaneParseval (fun slot => scaledAtomRows design slot) := by
  apply planeParseval_of_entries
  · have hentry := congrFun (congrFun (transpose_mul_scaledAtomRows design) 0) 0
    simpa [Matrix.mul_apply, dotProduct] using hentry
  · have hentry := congrFun (congrFun (transpose_mul_scaledAtomRows design) 1) 1
    simpa [Matrix.mul_apply, dotProduct] using hentry
  · have hentry := congrFun (congrFun (transpose_mul_scaledAtomRows design) 0) 1
    simpa [Matrix.mul_apply, dotProduct] using hentry

theorem scaledAtomRows_dotProduct {size rank : ℕ} (design : WeightedDesign size rank)
    (slot : Fin size) (probe : Fin rank → ℝ) :
    scaledAtomRows design slot ⬝ᵥ probe
      = Real.sqrt (design.weight slot) * (design.atom slot ⬝ᵥ probe) := by
  rw [scaledAtomRows_row, smul_dotProduct, smul_eq_mul]

theorem scaledAtomRows_mass {size rank : ℕ} (design : WeightedDesign size rank)
    (slot : Fin size) :
    scaledAtomRows design slot ⬝ᵥ scaledAtomRows design slot
      = design.weight slot * leverageOf (design.atom slot) := by
  rw [scaledAtomRows_row, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    leverageOf_eq_dotProduct]
  have hsqrt := Real.sq_sqrt (design.weight_pos slot).le
  calc
    Real.sqrt (design.weight slot)
          * (Real.sqrt (design.weight slot) * (design.atom slot ⬝ᵥ design.atom slot))
        = Real.sqrt (design.weight slot) ^ 2
            * (design.atom slot ⬝ᵥ design.atom slot) := by ring
    _ = design.weight slot * (design.atom slot ⬝ᵥ design.atom slot) := by rw [hsqrt]

theorem planeTieWeight_scaledAtomRows (design : WeightedDesign 3 2)
    (slot : Fin 3) :
    planeTieWeight (fun label => scaledAtomRows design label) slot
      = 2 * design.weight slot * leverageOf (design.atom slot) - 1 := by
  rw [planeTieWeight, scaledAtomRows_mass]
  ring

theorem quadForm_pairGap_rankTwo (design : WeightedDesign 3 2)
    {left right : Fin 3} (hne : left ≠ right) (probe : Fin 2 → ℝ) :
    probe ⬝ᵥ ((subsetSum design ({left, right} : Finset (Fin 3)) - 1) *ᵥ probe)
      = (design.atom left ⬝ᵥ probe) ^ 2 + (design.atom right ⬝ᵥ probe) ^ 2
          - probe ⬝ᵥ probe := by
  rw [Matrix.sub_mulVec, dotProduct_sub, quadForm_subsetSum, Matrix.one_mulVec,
    Finset.sum_pair hne]
  simp only [momentCoord]

theorem planePairDominates_scaledAtomRows_iff_posSemidef (design : WeightedDesign 3 2)
    {left right : Fin 3} (hne : left ≠ right) :
    PlanePairDominates (scaledAtomRows design left) (scaledAtomRows design right)
        (design.weight left) (design.weight right)
      ↔ (subsetSum design ({left, right} : Finset (Fin 3)) - 1).PosSemidef := by
  have hweightLeft := design.weight_pos left
  have hweightRight := design.weight_pos right
  have hproduct : 0 < design.weight left * design.weight right :=
    mul_pos hweightLeft hweightRight
  have hleftSq : ∀ value : ℝ,
      (Real.sqrt (design.weight left) * value) ^ 2 = design.weight left * value ^ 2 := by
    intro value
    rw [mul_pow, Real.sq_sqrt hweightLeft.le]
  have hrightSq : ∀ value : ℝ,
      (Real.sqrt (design.weight right) * value) ^ 2 = design.weight right * value ^ 2 := by
    intro value
    rw [mul_pow, Real.sq_sqrt hweightRight.le]
  constructor
  · intro hdom
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe => ?_⟩
    · exact isHermitian_of_transpose_eq (transpose_pairGap design left right)
    · have hread := hdom probe
      rw [star_trivial]
      rw [quadForm_pairGap_rankTwo design hne]
      rw [scaledAtomRows_dotProduct, scaledAtomRows_dotProduct] at hread
      rw [hleftSq, hrightSq] at hread
      nlinarith
  · intro hpsd probe
    have hread := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 probe
    rw [star_trivial] at hread
    rw [quadForm_pairGap_rankTwo design hne] at hread
    rw [scaledAtomRows_dotProduct, scaledAtomRows_dotProduct]
    rw [hleftSq, hrightSq]
    nlinarith

theorem planePairDominatesStrict_scaledAtomRows_iff_posDef (design : WeightedDesign 3 2)
    {left right : Fin 3} (hne : left ≠ right) :
    PlanePairDominatesStrict (scaledAtomRows design left) (scaledAtomRows design right)
        (design.weight left) (design.weight right)
      ↔ (subsetSum design ({left, right} : Finset (Fin 3)) - 1).PosDef := by
  have hweightLeft := design.weight_pos left
  have hweightRight := design.weight_pos right
  have hproduct : 0 < design.weight left * design.weight right :=
    mul_pos hweightLeft hweightRight
  have hleftSq : ∀ value : ℝ,
      (Real.sqrt (design.weight left) * value) ^ 2 = design.weight left * value ^ 2 := by
    intro value
    rw [mul_pow, Real.sq_sqrt hweightLeft.le]
  have hrightSq : ∀ value : ℝ,
      (Real.sqrt (design.weight right) * value) ^ 2 = design.weight right * value ^ 2 := by
    intro value
    rw [mul_pow, Real.sq_sqrt hweightRight.le]
  constructor
  · intro hdom
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hprobe => ?_⟩
    · exact isHermitian_of_transpose_eq (transpose_pairGap design left right)
    · have hread := hdom probe hprobe
      rw [star_trivial]
      rw [quadForm_pairGap_rankTwo design hne]
      rw [scaledAtomRows_dotProduct, scaledAtomRows_dotProduct] at hread
      rw [hleftSq, hrightSq] at hread
      nlinarith
  · intro hposDef probe hprobe
    have hread := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobe
    rw [star_trivial] at hread
    rw [quadForm_pairGap_rankTwo design hne] at hread
    rw [scaledAtomRows_dotProduct, scaledAtomRows_dotProduct]
    rw [hleftSq, hrightSq]
    nlinarith

theorem isTie_iff_no_strict_scaledPlanePair (design : WeightedDesign 3 2) :
    IsTie design ↔
      ∀ left right : Fin 3, left ≠ right →
        ¬ PlanePairDominatesStrict (scaledAtomRows design left) (scaledAtomRows design right)
            (design.weight left) (design.weight right) := by
  constructor
  · intro htie left right hne hstrict
    exact htie.2 {left, right} (Finset.card_pair hne)
      ((planePairDominatesStrict_scaledAtomRows_iff_posDef design hne).mp hstrict)
  · intro hnostrict
    refine ⟨gtz_rank_two 3 design, ?_⟩
    intro selected hcard hposDef
    rw [Finset.card_eq_two] at hcard
    obtain ⟨left, right, hne, rfl⟩ := hcard
    exact hnostrict left right hne
      ((planePairDominatesStrict_scaledAtomRows_iff_posDef design hne).mpr hposDef)

theorem isTie_iff_planeTieWeight_scaledAtomRows (design : WeightedDesign 3 2) :
    IsTie design ↔
      ∀ slot, design.weight slot
        = planeTieWeight (fun label => scaledAtomRows design label) slot := by
  rw [isTie_iff_no_strict_scaledPlanePair]
  exact plane_three_tie_iff (scaledAtomRows_planeParseval design)
    design.weight_pos design.weight_sum_one

theorem isTie_iff_rankTwo_planeLeverageIdentity (design : WeightedDesign 3 2) :
    IsTie design ↔
      ∀ slot, 2 * design.weight slot * leverageOf (design.atom slot)
        = 1 + design.weight slot := by
  rw [isTie_iff_planeTieWeight_scaledAtomRows]
  constructor
  · intro h slot
    have hslot := h slot
    rw [planeTieWeight_scaledAtomRows] at hslot
    linarith
  · intro h slot
    rw [planeTieWeight_scaledAtomRows]
    linarith [h slot]

theorem isTie_rankTwo_three_pair_boundary (design : WeightedDesign 3 2)
    (htie : IsTie design) {left right : Fin 3} (hne : left ≠ right) :
    (subsetSum design ({left, right} : Finset (Fin 3)) - 1).PosSemidef
      ∧ ¬ (subsetSum design ({left, right} : Finset (Fin 3)) - 1).PosDef
      ∧ (subsetSum design ({left, right} : Finset (Fin 3)) - 1).det = 0
      ∧ pairBracket design left right ≠ 0
      ∧ ∃ probe : Fin 2 → ℝ, probe ≠ 0
          ∧ (subsetSum design ({left, right} : Finset (Fin 3)) - 1) *ᵥ probe = 0 := by
  let atom : Fin 3 → (Fin 2 → ℝ) := fun slot => scaledAtomRows design slot
  have hframe : PlaneParseval atom := scaledAtomRows_planeParseval design
  have hweights : ∀ slot, design.weight slot = planeTieWeight atom slot :=
    (isTie_iff_planeTieWeight_scaledAtomRows design).mp htie
  have hhalf : ∀ slot, 1 / 2 < atom slot ⬝ᵥ atom slot := by
    intro slot
    have hpos := design.weight_pos slot
    rw [hweights slot] at hpos
    simp only [planeTieWeight] at hpos
    linarith
  have hdom : PlanePairDominates (atom left) (atom right)
      (design.weight left) (design.weight right) := by
    rw [hweights left, hweights right]
    exact planeTie_pair_dominates hframe hhalf hne
  have hpsd := (planePairDominates_scaledAtomRows_iff_posSemidef design hne).mp hdom
  have hnotPosDef : ¬ (subsetSum design ({left, right} : Finset (Fin 3)) - 1).PosDef := by
    intro hposDef
    exact htie.2 {left, right} (Finset.card_pair hne) hposDef
  have hdet : (subsetSum design ({left, right} : Finset (Fin 3)) - 1).det = 0 := by
    by_contra hdetNe
    exact hnotPosDef (hpsd.posDef_iff_det_ne_zero.mpr hdetNe)
  have hindependent := planeTie_pair_independent hframe hhalf hne
  have hbracket : pairBracket design left right ≠ 0 := by
    intro hzero
    have hwedge := plane_three_wedge_sq hframe hne
    have hpositive : 0 < (atom left ⬝ᵥ atom left) + (atom right ⬝ᵥ atom right) - 1 := by
      linarith [hhalf left, hhalf right]
    have hzeroWedge : atom left 0 * atom right 1 - atom left 1 * atom right 0 = 0 := by
      change (Real.sqrt (design.weight left) * design.atom left 0)
              * (Real.sqrt (design.weight right) * design.atom right 1)
            - (Real.sqrt (design.weight left) * design.atom left 1)
              * (Real.sqrt (design.weight right) * design.atom right 0) = 0
      rw [show (Real.sqrt (design.weight left) * design.atom left 0)
              * (Real.sqrt (design.weight right) * design.atom right 1)
            - (Real.sqrt (design.weight left) * design.atom left 1)
              * (Real.sqrt (design.weight right) * design.atom right 0)
          = Real.sqrt (design.weight left) * Real.sqrt (design.weight right)
              * pairBracket design left right by
            simp only [pairBracket]
            ring,
        hzero, mul_zero]
    rw [hzeroWedge] at hwedge
    nlinarith
  let probe := planeTieProbe atom left right
  have hprobeNe : probe ≠ 0 := planeTieProbe_ne_zero hframe hhalf hne
  have hcert := planeTieProbe_certificate hframe hne
  have hquad : probe ⬝ᵥ
      ((subsetSum design ({left, right} : Finset (Fin 3)) - 1) *ᵥ probe) = 0 := by
    have hweightLeft := design.weight_pos left
    have hweightRight := design.weight_pos right
    rw [← hweights left, ← hweights right] at hcert
    rw [quadForm_pairGap_rankTwo design hne]
    simp only [atom, scaledAtomRows_dotProduct] at hcert
    have hleftSq :
        (Real.sqrt (design.weight left) * (design.atom left ⬝ᵥ probe)) ^ 2
          = design.weight left * (design.atom left ⬝ᵥ probe) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hweightLeft.le]
    have hrightSq :
        (Real.sqrt (design.weight right) * (design.atom right ⬝ᵥ probe)) ^ 2
          = design.weight right * (design.atom right ⬝ᵥ probe) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hweightRight.le]
    rw [hleftSq, hrightSq] at hcert
    nlinarith [mul_pos hweightLeft hweightRight]
  have hkernel := (hpsd.dotProduct_mulVec_zero_iff probe).mp hquad
  exact ⟨hpsd, hnotPosDef, hdet, hbracket, probe, hprobeNe, hkernel⟩

end Gtz

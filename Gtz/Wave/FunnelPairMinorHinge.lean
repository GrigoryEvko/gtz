/-
# The unit atom's pair-minor row, and the funnel with its corank floor

The hinge at `(6,3)` splits by leverage: `Gtz.isTie_sixThree_allHeavy_or_funnel`
sends a tie either to the all-heavy branch or to a UNIT ATOM with a dominator
that avoids it.  This module supplies the unit atom's own conservation law, then
strengthens the funnel so that every corollary of the adjugate law becomes
unconditional, then reads the weight budget for what the atoms OUTSIDE the
dominator must do.

## 1. A unit atom is inadmissible with everybody, and its row is `−t_a`

At `leverageOf a = 1` the pair minor loses its first factor entirely:

  **`Gtz.pairGapMinor_of_leverage_eq_one`: `pairGapMinor a b = −(a·b)²`** ,

which is the sharp form of the landed `Gtz.pairGapMinor_nonpos_of_leverage_eq_one`.
A unit atom is boundary admissible exactly with the atoms orthogonal to it.  Summing that against the design's weights and
reading Parseval at the atom itself gives a new exact law:

  **`Gtz.pairMinor_row_of_unitAtom`:
  `Σ_b t_a·t_b·pairGapMinor(g_a, g_b) = −t_a`** .

The landed `Gtz.pairMinor_budget` totals every row at one, so the remaining rows
of a design with a unit atom must carry `1 + t_a`
(`Gtz.pairMinor_offRow_total_of_unitAtom`).  **A unit atom is a pure debtor in
the pair-minor budget, and the size of its debt is exactly its weight.**

## 2. The funnel keeps the bound it was built from

`Gtz.unitAtom_exists_dominator_fixing` builds its triple from the landed
deflated gap bound and then DISCARDS the bound, so the bound and the funnel are
never available at the same triple.  This module separates the two steps
(`Gtz.dominates_and_fixes_of_deflatedGapBound`) and hands the bound back with the
dominator (`Gtz.isTie_sixThree_unitAtom_funnel_bounded`).  Any later law about
the deflated bound — a corank floor, a leverage floor, a determinant floor — then
applies to the funnel's own triple instead of to a different one.

Given a corank witness `0 < pairMinorTotal`, the adjugate law inverts: the
funnel's readings ARE the normalized pair minors of its dominator
(`Gtz.funnel_reading_sq_eq_pairMinor_div`), and two vanishing pair minors give a
parallel pair (`Gtz.funnel_parallel_of_two_pairMinors_zero`).

## 3. Outside the dominator, some atom reads the unit atom above one

The dominator's readings total exactly one, and its own weights cap what it can
carry of Parseval's total.  The cap is STRICT, because no single weight of a
triple exhausts the triple's weight sum.  What is left must be carried outside:

  **`Gtz.exists_outside_reading_sq_gt_one`: at a `(6,3)` funnel some atom that is
  neither the unit atom nor a member of the dominator reads the unit atom above
  one in square.**

Such an atom is strictly heavy by Cauchy-Schwarz, and its pair with the unit atom
has pair minor STRICTLY BELOW `−1`.  The landed version of this statement needed
the two-zero stratum; this one needs only the funnel.

[The `(5,3)` diamond tie and the `(6,3)` split diamond have no unit atom — their
leverages are `2` and `13/4`, and `13/4` — so no fixture inhabits the funnel
branch, and none of this is contradicted by them.]
-/
import Gtz.Wave.KTwoSixThreeFunnel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The unit atom's pair minors -/

/-- **A UNIT ATOM'S PAIR MINOR IS MINUS THE SQUARED PAIRING.**  The leverage
excess of the atom vanishes, so the first factor of the minor disappears. -/
theorem pairGapMinor_of_leverage_eq_one {a : Fin 3 → ℝ} (hunit : leverageOf a = 1)
    (b : Fin 3 → ℝ) : pairGapMinor a b = -(a ⬝ᵥ b) ^ 2 := by
  rw [pairGapMinor, hunit]; ring

/-- **A UNIT ATOM IS BOUNDARY ADMISSIBLE EXACTLY WITH ITS ORTHOGONAL PARTNERS.** -/
theorem pairGapMinor_eq_zero_iff_of_leverage_eq_one {a : Fin 3 → ℝ}
    (hunit : leverageOf a = 1) (b : Fin 3 → ℝ) :
    pairGapMinor a b = 0 ↔ a ⬝ᵥ b = 0 := by
  rw [pairGapMinor_of_leverage_eq_one hunit, neg_eq_zero]
  exact pow_eq_zero_iff (n := 2) (by norm_num)

/-- **THE UNIT ATOM'S ROW OF THE PAIR-MINOR BUDGET IS MINUS ITS WEIGHT.**  Every
entry of the row is minus a squared reading, and Parseval totals those readings
at the atom's own leverage.  A new exact law, at every design and every size. -/
theorem pairMinor_row_of_unitAtom (D : WeightedDesign m 3) {a : Fin m}
    (hunit : leverageOf (D.atom a) = 1) :
    ∑ b, D.weight a * (D.weight b * pairGapMinor (D.atom a) (D.atom b))
      = -D.weight a := by
  have hpar := parseval_probe_form D (D.atom a)
  have hself : D.atom a ⬝ᵥ D.atom a = 1 := by
    rw [dotProduct_self_eq_leverage]; exact hunit
  rw [hself] at hpar
  have hrw : ∑ b, D.weight a * (D.weight b * pairGapMinor (D.atom a) (D.atom b))
      = -(D.weight a * ∑ b, D.weight b * (D.atom b ⬝ᵥ D.atom a) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by
      rw [pairGapMinor_of_leverage_eq_one hunit, dotProduct_comm (D.atom a) (D.atom b)]
      ring
  rw [hrw, hpar]
  ring

/-- **THE OTHER ROWS CARRY THE DEBT.**  The landed pair-minor budget totals every
row at one, so a design with a unit atom leaves `1 + t_a` for its other rows. -/
theorem pairMinor_offRow_total_of_unitAtom (D : WeightedDesign m 3) {a : Fin m}
    (hunit : leverageOf (D.atom a) = 1) :
    ∑ c ∈ Finset.univ.erase a, ∑ b,
        D.weight c * (D.weight b * pairGapMinor (D.atom c) (D.atom b))
      = 1 + D.weight a := by
  have hbudget := pairMinor_budget D
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun c => ∑ b, D.weight c * (D.weight b * pairGapMinor (D.atom c) (D.atom b)))
    (Finset.mem_univ a)
  rw [pairMinor_row_of_unitAtom D hunit] at hsplit
  rw [hbudget] at hsplit
  linarith

/-! ## 2. The funnel keeps its bound -/

/-- **THE DEFLATED BOUND ALREADY CARRIES THE FUNNEL.**  At a tie with a unit
atom, any triple satisfying the deflated gap bound weakly dominates AND fixes the
atom.  The landed `Gtz.unitAtom_exists_dominator_fixing` proves exactly this and
then discards the bound, so the bound and the funnel are never available at the
same triple.  This statement keeps them together. -/
theorem dominates_and_fixes_of_deflatedGapBound (D : WeightedDesign (m + 1) 3)
    (hsize : 1 ≤ m) (htie : IsTie D) {a : Fin (m + 1)}
    (hunit : leverageOf (D.atom a) = 1)
    {T : Finset (Fin (m + 1))} (hcard : T.card = 3)
    (hbound : (((1 : ℝ) - D.weight a) • (subsetSum D T - 1)
        - D.weight a • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - atomMatrix (D.atom a))).PosSemidef) :
    Dominates D T ∧ subsetSum D T *ᵥ D.atom a = D.atom a := by
  have hweightPos := D.weight_pos a
  have hweightLtOne : D.weight a < 1 := weight_lt_one D (by omega) a
  have hmass : (0 : ℝ) < 1 - D.weight a := by linarith
  have hproj := posSemidef_one_sub_atomMatrix_of_unit hunit
  have hgapScaled : (((1 : ℝ) - D.weight a) • (subsetSum D T - 1)).PosSemidef := by
    have hsplit : ((1 : ℝ) - D.weight a) • (subsetSum D T - 1)
        = (((1 : ℝ) - D.weight a) • (subsetSum D T - 1)
            - D.weight a • (1 - atomMatrix (D.atom a)))
          + D.weight a • ((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (D.atom a)) := by
      module
    rw [hsplit]
    exact hbound.add (hproj.smul hweightPos.le)
  have hgap : (subsetSum D T - 1).PosSemidef := by
    have hunscale : subsetSum D T - 1
        = (((1 : ℝ) - D.weight a)⁻¹) • (((1 : ℝ) - D.weight a) • (subsetSum D T - 1)) := by
      rw [smul_smul, inv_mul_cancel₀ hmass.ne', one_smul]
    rw [hunscale]
    exact hgapScaled.smul (inv_pos.mpr hmass).le
  refine ⟨hgap, ?_⟩
  have hnotPD : ¬ (subsetSum D T - 1).PosDef := htie.2 T hcard
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hnotPD
  push Not at hnotPD
  obtain ⟨v, hvne, hvle⟩ := hnotPD hgap.1
  rw [star_trivial] at hvle
  have hvge : 0 ≤ v ⬝ᵥ ((subsetSum D T - 1) *ᵥ v) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hgap).2 v
    rwa [star_trivial] at h
  have hvzero : v ⬝ᵥ ((subsetSum D T - 1) *ᵥ v) = 0 := le_antisymm hvle hvge
  have hboundForm : 0 ≤ v ⬝ᵥ ((((1 : ℝ) - D.weight a) • (subsetSum D T - 1)
      - D.weight a • (1 - atomMatrix (D.atom a))) *ᵥ v) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hbound).2 v
    rwa [star_trivial] at h
  have hprojForm : 0 ≤ v ⬝ᵥ (((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - atomMatrix (D.atom a)) *ᵥ v) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hproj).2 v
    rwa [star_trivial] at h
  have hsplitForm : v ⬝ᵥ ((((1 : ℝ) - D.weight a) • (subsetSum D T - 1)
        - D.weight a • (1 - atomMatrix (D.atom a))) *ᵥ v)
      = ((1 : ℝ) - D.weight a) * (v ⬝ᵥ ((subsetSum D T - 1) *ᵥ v))
        - D.weight a * (v ⬝ᵥ (((1 : Matrix (Fin 3) (Fin 3) ℝ)
            - atomMatrix (D.atom a)) *ᵥ v)) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [hsplitForm, hvzero, mul_zero, zero_sub] at hboundForm
  have hcompZero : v ⬝ᵥ (((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - atomMatrix (D.atom a)) *ᵥ v) = 0 := by
    nlinarith [hboundForm, hprojForm, hweightPos]
  have hcompForm : v ⬝ᵥ (((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - atomMatrix (D.atom a)) *ᵥ v)
      = v ⬝ᵥ v - (D.atom a ⬝ᵥ v) ^ 2 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul, dotProduct_comm v (D.atom a)]
    ring
  have honline : v = (D.atom a ⬝ᵥ v) • D.atom a :=
    eq_smul_of_unit_complement_form_zero hunit (by rw [← hcompForm]; exact hcompZero)
  have hread : D.atom a ⬝ᵥ v ≠ 0 := by
    intro hzero
    apply hvne
    rw [honline, hzero, zero_smul]
  have hatomForm : D.atom a ⬝ᵥ ((subsetSum D T - 1) *ᵥ D.atom a) = 0 := by
    have hexpand : v ⬝ᵥ ((subsetSum D T - 1) *ᵥ v)
        = (D.atom a ⬝ᵥ v) ^ 2
          * (D.atom a ⬝ᵥ ((subsetSum D T - 1) *ᵥ D.atom a)) := by
      conv_lhs => rw [honline]
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
        smul_eq_mul]
      ring
    have hz := hvzero
    rw [hexpand] at hz
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hread
    · exact h
  have hsym : (subsetSum D T - 1)ᵀ = subsetSum D T - 1 := hgap.1
  have hkill := mulVec_eq_zero_of_form_eq_zero hgap hsym hatomForm
  have hfinal : subsetSum D T *ᵥ D.atom a - D.atom a = 0 := by
    have h : (subsetSum D T - 1) *ᵥ D.atom a
        = subsetSum D T *ᵥ D.atom a - D.atom a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [← h]; exact hkill
  funext i
  have hi := congrFun hfinal i
  simp only [Pi.sub_apply, Pi.zero_apply] at hi
  linarith

/-- **THE FUNNEL, WITH ITS BOUND.**  At `(6,3)` a tie with a unit atom has an
EXPLICIT triple that avoids the atom, weakly dominates, fixes the atom, and still
carries the deflated gap bound it was built from.  Every later law about that
bound now speaks about the funnel's own triple. -/
theorem isTie_sixThree_unitAtom_funnel_bounded (D : WeightedDesign 6 3) (htie : IsTie D)
    (a : Fin 6) (hunit : leverageOf (D.atom a) = 1) :
    ∃ x y z : Fin 6, x ≠ y ∧ x ≠ z ∧ y ≠ z
      ∧ a ∉ ({x, y, z} : Finset (Fin 6))
      ∧ Dominates D ({x, y, z} : Finset (Fin 6))
      ∧ subsetSum D ({x, y, z} : Finset (Fin 6)) *ᵥ D.atom a = D.atom a
      ∧ (((1 : ℝ) - D.weight a)
            • (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
          - D.weight a • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
            - atomMatrix (D.atom a))).PosSemidef := by
  have hweightPos := D.weight_pos a
  have hweightLtOne : D.weight a < 1 := weight_lt_one D (by norm_num) a
  have hshare : D.weight a * leverageOf (D.atom a) < 1 := by
    rw [hunit]; linarith
  obtain ⟨T, hcard, havoid, hbound⟩ :=
    exists_deflatedGapBound (m := 5) D (by norm_num)
      (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) a hshare
  obtain ⟨p, q, r, hpq, hpr, hqr, hT⟩ := Finset.card_eq_three.mp hcard
  subst hT
  obtain ⟨hgap, hfix⟩ :=
    dominates_and_fixes_of_deflatedGapBound (m := 5) D (by norm_num) htie hunit hcard hbound
  exact ⟨p, q, r, hpq, hpr, hqr, havoid, hgap, hfix, hbound⟩

/-! ## 3. The readings are the normalized pair minors -/

/-- **THE FUNNEL'S READINGS ARE ITS DOMINATOR'S NORMALIZED PAIR MINORS.**  With
the corank floor in hand the adjugate law inverts: each squared reading is the
opposite pair minor divided by their total. -/
theorem funnel_reading_sq_eq_pairMinor_div (D : WeightedDesign m 3)
    {a x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hunit : leverageOf (D.atom a) = 1)
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ D.atom a = D.atom a)
    (hpositive : 0 < pairMinorTotal (D.atom x) (D.atom y) (D.atom z)) :
    (D.atom x ⬝ᵥ D.atom a) ^ 2
      = pairGapMinor (D.atom y) (D.atom z)
          / pairMinorTotal (D.atom x) (D.atom y) (D.atom z) := by
  have hnorm : D.atom a ⬝ᵥ D.atom a = 1 := by
    rw [dotProduct_self_eq_leverage]; exact hunit
  obtain ⟨hfirst, -, -⟩ :=
    pairGapMinor_eq_pairMinorTotal_mul_reading_design D hxy hxz hyz hfix hnorm
  rw [hfirst]
  field_simp

/-- **TWO VANISHING PAIR MINORS GIVE A PARALLEL PAIR, WITH NO SIDE CONDITION.**
The corank floor discharges the hypothesis of
`Gtz.unitAtom_parallel_of_two_pairMinors_zero`. -/
theorem funnel_parallel_of_two_pairMinors_zero (D : WeightedDesign (m + 1) 3)
    {a x y z : Fin (m + 1)} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (havoid : a ∉ ({x, y, z} : Finset (Fin (m + 1))))
    (hunit : leverageOf (D.atom a) = 1)
    (hfix : subsetSum D ({x, y, z} : Finset (Fin (m + 1))) *ᵥ D.atom a = D.atom a)
    (hpositive : 0 < pairMinorTotal (D.atom x) (D.atom y) (D.atom z))
    (hminorXY : pairGapMinor (D.atom x) (D.atom y) = 0)
    (hminorXZ : pairGapMinor (D.atom x) (D.atom z) = 0) :
    HasParallelPair D :=
  unitAtom_parallel_of_two_pairMinors_zero D hxy hxz hyz havoid hunit hfix
    hpositive.ne' hminorXY hminorXZ

/-! ## 4. Outside the dominator, one atom reads above one -/

/-- **SOME ATOM OUTSIDE THE FUNNEL DOMINATOR READS THE UNIT ATOM ABOVE ONE.**
The dominator's readings total exactly one, and no member's weight exhausts the
triple's weight sum, so the dominator carries STRICTLY less of Parseval's total
than its own weight.  The remainder is carried by the two atoms outside. -/
theorem exists_outside_reading_sq_gt_one (D : WeightedDesign 6 3)
    {a : Fin 6} (hunit : leverageOf (D.atom a) = 1)
    {T : Finset (Fin 6)} (hcard : T.card = 3) (havoid : a ∉ T)
    (hfix : subsetSum D T *ᵥ D.atom a = D.atom a) :
    ∃ u : Fin 6, u ≠ a ∧ u ∉ T ∧ 1 < (D.atom u ⬝ᵥ D.atom a) ^ 2 := by
  classical
  set U : Finset (Fin 6) := Finset.univ \ insert a T with hU
  have hself : D.atom a ⬝ᵥ D.atom a = 1 := by
    rw [dotProduct_self_eq_leverage]; exact hunit
  -- the four labels of `insert a T` and the two of `U` exhaust the design
  have hinsCard : (insert a T).card = 4 := by
    rw [Finset.card_insert_of_notMem havoid, hcard]
  have hdisj : Disjoint (insert a T) U := Finset.disjoint_sdiff
  have huniv : insert a T ∪ U = Finset.univ := by
    rw [hU, Finset.union_sdiff_self_eq_union]
    exact Finset.union_eq_right.mpr (Finset.subset_univ _)
  -- Parseval, split across the two blocks
  have hpar := parseval_probe_form D (D.atom a)
  rw [hself, ← huniv, Finset.sum_union hdisj,
    Finset.sum_insert havoid, hself] at hpar
  -- the weights, split the same way
  have hweights := D.weight_sum_one
  rw [← huniv, Finset.sum_union hdisj, Finset.sum_insert havoid] at hweights
  -- the funnel budget
  have hbudget : ∑ c ∈ T, (D.atom c ⬝ᵥ D.atom a) ^ 2 = 1 :=
    unitAtom_readings_resolve (m := 5) D hunit hfix
  -- a member with a live reading, and a second member to beat its weight
  have hlive : ∃ c ∈ T, 0 < (D.atom c ⬝ᵥ D.atom a) ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have : ∑ c ∈ T, (D.atom c ⬝ᵥ D.atom a) ^ 2 = 0 :=
      le_antisymm (Finset.sum_nonpos fun c hc => hcon c hc)
        (Finset.sum_nonneg fun c _ => sq_nonneg _)
    rw [hbudget] at this
    exact absurd this one_ne_zero
  obtain ⟨c₀, hc₀T, hc₀pos⟩ := hlive
  have herase : (T.erase c₀).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hc₀T, hcard]
    norm_num
  obtain ⟨c₁, hc₁mem⟩ := herase
  have hc₁ne : c₁ ≠ c₀ := Finset.ne_of_mem_erase hc₁mem
  have hc₁T : c₁ ∈ T := Finset.mem_of_mem_erase hc₁mem
  have hstrictWeight : D.weight c₀ < ∑ d ∈ T, D.weight d :=
    Finset.single_lt_sum hc₁ne hc₀T hc₁T (D.weight_pos c₁)
      (fun d _ _ => (D.weight_pos d).le)
  -- the dominator carries strictly less than its own weight
  have hstrict : ∑ c ∈ T, D.weight c * (D.atom c ⬝ᵥ D.atom a) ^ 2
      < ∑ d ∈ T, D.weight d := by
    have hstep : ∑ c ∈ T, D.weight c * (D.atom c ⬝ᵥ D.atom a) ^ 2
        < ∑ c ∈ T, (∑ d ∈ T, D.weight d) * (D.atom c ⬝ᵥ D.atom a) ^ 2 := by
      refine Finset.sum_lt_sum (fun c hc => ?_) ⟨c₀, hc₀T, ?_⟩
      · exact mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := D.weight)
            (fun d _ => (D.weight_pos d).le) hc) (sq_nonneg _)
      · exact mul_lt_mul_of_pos_right hstrictWeight hc₀pos
    rwa [← Finset.mul_sum, hbudget, mul_one] at hstep
  -- so the outside block carries strictly more than its own weight
  have houtside : ∑ d ∈ U, D.weight d
      < ∑ c ∈ U, D.weight c * (D.atom c ⬝ᵥ D.atom a) ^ 2 := by linarith
  by_contra hcon
  push Not at hcon
  have hbound : ∑ c ∈ U, D.weight c * (D.atom c ⬝ᵥ D.atom a) ^ 2
      ≤ ∑ d ∈ U, D.weight d := by
    refine Finset.sum_le_sum fun c hc => ?_
    have hcU := Finset.mem_sdiff.mp hc
    have hne : c ≠ a := fun h => hcU.2 (by rw [h]; exact Finset.mem_insert_self a T)
    have hnT : c ∉ T := fun h => hcU.2 (Finset.mem_insert_of_mem h)
    have := hcon c hne hnT
    nlinarith [D.weight_pos c]
  linarith

/-- **THE OUTSIDE READER IS STRICTLY HEAVY.**  Cauchy-Schwarz against the unit
atom turns a squared reading above one into a leverage above one. -/
theorem one_lt_leverage_of_reading_sq_gt_one {a b : Fin 3 → ℝ}
    (hunit : leverageOf a = 1) (hread : 1 < (b ⬝ᵥ a) ^ 2) : 1 < leverageOf b := by
  have hcs : (b ⬝ᵥ a) ^ 2 ≤ leverageOf b * leverageOf a := by
    have hnn : 0 ≤ crossNormSq b a := by
      rw [crossNormSq, dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rw [crossNormSq_eq_leverage_mul_sub_sq] at hnn
    linarith
  rw [hunit, mul_one] at hcs
  linarith

/-- **THE OUTSIDE READER IS DEEPLY INADMISSIBLE WITH THE UNIT ATOM.**  Its pair
minor with the atom is minus its squared reading, so it sits strictly below
`−1`. -/
theorem pairGapMinor_lt_neg_one_of_reading_sq_gt_one {a b : Fin 3 → ℝ}
    (hunit : leverageOf a = 1) (hread : 1 < (b ⬝ᵥ a) ^ 2) :
    pairGapMinor a b < -1 := by
  rw [pairGapMinor_of_leverage_eq_one hunit, dotProduct_comm a b]
  linarith

/-! ## 5. The assembly at six points -/

/-- **THE FUNNEL BRANCH OF A `(6,3)` TIE, IN FULL.**  A tie with a unit atom
carries a triple avoiding the atom that weakly dominates it, fixes it, still carries the
deflated gap bound, and leaves outside it an atom that is strictly heavy and
deeply inadmissible with the unit atom.

Every piece is unconditional: the triple and its bound come from the landed
deflated gap bound, and the outside reader from Parseval against the funnel
budget. -/
theorem isTie_sixThree_funnel_structure (D : WeightedDesign 6 3) (htie : IsTie D)
    (a : Fin 6) (hunit : leverageOf (D.atom a) = 1) :
    ∃ x y z u : Fin 6, x ≠ y ∧ x ≠ z ∧ y ≠ z
      ∧ a ∉ ({x, y, z} : Finset (Fin 6))
      ∧ Dominates D ({x, y, z} : Finset (Fin 6))
      ∧ subsetSum D ({x, y, z} : Finset (Fin 6)) *ᵥ D.atom a = D.atom a
      ∧ (((1 : ℝ) - D.weight a)
            • (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
          - D.weight a • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
            - atomMatrix (D.atom a))).PosSemidef
      ∧ u ≠ a ∧ u ∉ ({x, y, z} : Finset (Fin 6))
      ∧ 1 < leverageOf (D.atom u)
      ∧ pairGapMinor (D.atom a) (D.atom u) < -1 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, havoid, hgap, hfix, hpositive⟩ :=
    isTie_sixThree_unitAtom_funnel_bounded D htie a hunit
  obtain ⟨u, hua, huT, hread⟩ :=
    exists_outside_reading_sq_gt_one D hunit
      (by rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
        Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton])
      havoid hfix
  exact ⟨x, y, z, u, hxy, hxz, hyz, havoid, hgap, hfix, hpositive, hua, huT,
    one_lt_leverage_of_reading_sq_gt_one hunit hread,
    pairGapMinor_lt_neg_one_of_reading_sq_gt_one hunit hread⟩

end Gtz

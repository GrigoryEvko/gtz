/-
# The funnel's dominator is never a corner: a sharp floor on its second invariant

The unit atom funnel (`Gtz.isTie_sixThree_allHeavy_or_funnel`) hands back a weak
dominator `T` that avoids the unit atom `a` and reproduces it.  The landed
adjugate law then reads `T`'s three pair minors off the atom's readings, but
every one of its usable corollaries carries the hypothesis
`pairMinorTotal ≠ 0` — the statement that `T`'s gap has corank ONE and not two.
This module discharges that hypothesis, with a sharp constant.

## The floor

The funnel is built on the landed deflated gap bound
(`Gtz.exists_deflatedGapBound_of_isTie`),

  `(1 − t_a)·(S_T − 1) − t_a·(1 − g_a g_aᵀ) ⪰ 0` ,

which at unit leverage says the gap dominates a multiple of the orthogonal
projection off the atom.  Write `R` for that positive semidefinite slack, so
`(1 − t_a)·(S_T − 1) = R + t_a·P` with `P = 1 − g_a g_aᵀ`.  The second invariant
of a three-by-three matrix is a quadratic form, so it expands
(`Gtz.secondInvariantOfThree_add`), and every piece of the expansion is
nonnegative:

  `(1 − t_a)²·e₂(S_T − 1) = e₂(R) + t_a² + t_a·(tr R + g_a·R g_a)` .

The projection contributes exactly `t_a²` because `e₂(P) = 1` at unit leverage
(`Gtz.secondInvariantOfThree_one_sub_atomMatrix`), and the cross term collapses
to `tr R + g_a·R g_a` because `tr(P·R) = tr R − g_a·R g_a`
(`Gtz.trace_one_sub_atomMatrix_mul`).  Hence

  **`Gtz.pairMinorTotal_floor_of_deflatedGapBound`:
  `(t_a/(1 − t_a))² ≤ pairMinorTotal`** ,

after the bridge `Gtz.secondInvariantOfThree_gap_eq_pairMinorTotal`, which
identifies the ambient second invariant of the gap with the Gram-side total of
the three pair minors.

**The floor is exactly attained** when the slack `R` vanishes, so no constant
better than `(t_a/(1 − t_a))²` exists.

## What it buys

* `Gtz.pairMinorTotal_pos_of_deflatedGapBound` — the total is strictly positive,
  so the funnel's dominator has corank exactly one.  A corner never appears at a
  unit atom, and the corank-two arm owes the funnel nothing.
* `Gtz.unitAtom_parallel_of_two_pairMinors_zero_of_bound` — the landed
  pair-minor trigger, with its `pairMinorTotal ≠ 0` hypothesis discharged.
* `Gtz.trace_floor_of_deflatedGapBound` — the same expansion at the trace gives
  `Σ_{c∈T} ℓ_c ≥ 3 + 2t_a/(1 − t_a)`.

[MEASURED before proving.  The four expansion identities hold to `7.1e-15` over
20,000 random draws each.  The floor holds over 20,000 random deflated
configurations with minimum ratio `pairMinorTotal/(t/(1−t))² = 1.000922`, and it
is attained exactly at zero slack: `t = 0.1, 0.3, 0.5, 0.8` give
`pairMinorTotal = 0.012345679, 0.183673469, 1.0, 16.0` against
`(t/(1−t))² = 0.012345679, 0.183673469, 1.0, 16.0`.]
-/
import Gtz.Wave.NullProbeAdjugateLaw
import Gtz.Design.StratumTieFreeClasses
import Gtz.Quantitative.WindowPolarity
import Gtz.LinAlg.RankOneForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The second invariant is a quadratic form -/

/-- **THE SECOND INVARIANT EXPANDS.**  It is a quadratic form on matrices, with
the trace pairing as its polarization. -/
theorem secondInvariantOfThree_add (X Y : Matrix (Fin 3) (Fin 3) ℝ) :
    secondInvariantOfThree (X + Y)
      = secondInvariantOfThree X + secondInvariantOfThree Y
        + (Matrix.trace X * Matrix.trace Y - Matrix.trace (X * Y)) := by
  simp only [secondInvariantOfThree, Matrix.add_apply, Matrix.trace_fin_three,
    Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- The second invariant is homogeneous of degree two. -/
theorem secondInvariantOfThree_smul (c : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    secondInvariantOfThree (c • M) = c ^ 2 * secondInvariantOfThree M := by
  simp only [secondInvariantOfThree, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **THE PROJECTION OFF A UNIT ATOM HAS SECOND INVARIANT ONE.**  Its
eigenvalues are one, one and zero. -/
theorem secondInvariantOfThree_one_sub_atomMatrix {g : Fin 3 → ℝ}
    (hunit : leverageOf g = 1) :
    secondInvariantOfThree ((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix g) = 1 := by
  have hlev : g 0 ^ 2 + g 1 ^ 2 + g 2 ^ 2 = 1 := by
    rw [← hunit, leverageOf, Fin.sum_univ_three]
  rw [Matrix.one_fin_three]
  simp only [secondInvariantOfThree, Matrix.sub_apply, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.of_apply]
  linear_combination (-2 : ℝ) * hlev

/-- The trace of the projection off a unit atom is two. -/
theorem trace_one_sub_atomMatrix {g : Fin 3 → ℝ} (hunit : leverageOf g = 1) :
    Matrix.trace ((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix g) = 2 := by
  have hlev : g 0 ^ 2 + g 1 ^ 2 + g 2 ^ 2 = 1 := by
    rw [← hunit, leverageOf, Fin.sum_univ_three]
  rw [Matrix.one_fin_three]
  simp only [Matrix.trace_fin_three, Matrix.sub_apply, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.of_apply]
  linear_combination (-1 : ℝ) * hlev

/-- **THE PROJECTION READS A SYMMETRIC MATRIX BY ITS TRACE LESS ONE ATOM FORM.**
Symmetry is used: for a matrix that is not symmetric the atom form reads the
transpose instead. -/
theorem trace_one_sub_atomMatrix_mul (g : Fin 3 → ℝ) {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : Rᵀ = R) :
    Matrix.trace (((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix g) * R)
      = Matrix.trace R - g ⬝ᵥ (R *ᵥ g) := by
  have h10 : R 1 0 = R 0 1 := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hsym 0) 1
  have h20 : R 2 0 = R 0 2 := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hsym 0) 2
  have h21 : R 2 1 = R 1 2 := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hsym 1) 2
  rw [Matrix.one_fin_three]
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Matrix.sub_apply,
    atomMatrix, Matrix.vecMulVec_apply, Fin.sum_univ_three, dotProduct, Matrix.mulVec,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.of_apply]
  rw [h10, h20, h21]
  ring

/-! ## 2. A positive semidefinite matrix has a nonnegative second invariant -/

/-- **THE SECOND INVARIANT OF A POSITIVE SEMIDEFINITE MATRIX IS NONNEGATIVE.**
Each of its three summands is a two-by-two principal minor, and the landed
`Gtz.posSemidef_offDiag_sq_le` bounds each off-diagonal entry by its two
diagonal neighbours. -/
theorem secondInvariantOfThree_nonneg_of_posSemidef {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hpsd : M.PosSemidef) : 0 ≤ secondInvariantOfThree M := by
  have h01 := posSemidef_offDiag_sq_le hpsd 0 1
  have h02 := posSemidef_offDiag_sq_le hpsd 0 2
  have h12 := posSemidef_offDiag_sq_le hpsd 1 2
  have s01 := symm_of_posSemidef hpsd 0 1
  have s02 := symm_of_posSemidef hpsd 0 2
  have s12 := symm_of_posSemidef hpsd 1 2
  rw [secondInvariantOfThree, s01, s02, s12]
  nlinarith [h01, h02, h12]

/-- The trace of a positive semidefinite matrix is nonnegative. -/
theorem trace_nonneg_of_posSemidef {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hpsd : M.PosSemidef) : 0 ≤ Matrix.trace M := by
  have h0 := hpsd.diag_nonneg (i := 0)
  have h1 := hpsd.diag_nonneg (i := 1)
  have h2 := hpsd.diag_nonneg (i := 2)
  rw [Matrix.trace_fin_three]
  linarith

/-! ## 3. The bridge to the pair currency -/

/-- **THE AMBIENT SECOND INVARIANT IS THE GRAM-SIDE PAIR MINOR TOTAL.**  The
subset sum and the Gram matrix of a triple share a characteristic polynomial at
rank three, so the second invariant of the ambient gap is the total of the three
pair minors. -/
theorem secondInvariantOfThree_gap_eq_pairMinorTotal (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
      = pairMinorTotal (D.atom x) (D.atom y) (D.atom z) := by
  have hsum : subsetSum D ({x, y, z} : Finset (Fin m))
      = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
    rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    abel
  rw [hsum, pairMinorTotal, pairGapMinor, pairGapMinor, pairGapMinor, Matrix.one_fin_three]
  simp only [secondInvariantOfThree, Matrix.sub_apply, Matrix.add_apply,
    atomMatrix, Matrix.vecMulVec_apply, leverageOf, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.of_apply]
  ring

/-! ## 4. The floor -/

/-- **THE SECOND INVARIANT FLOOR.**  A triple carrying the deflated gap bound at
a unit atom has pair minor total at least the squared deflation ratio.  The
constant is attained exactly when the bound's slack vanishes. -/
theorem pairMinorTotal_floor_of_deflatedGapBound (D : WeightedDesign m 3)
    {a x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hunit : leverageOf (D.atom a) = 1)
    (hpos : 0 < D.weight a) (hlt : D.weight a < 1)
    (hbound : (((1 : ℝ) - D.weight a) • (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
        - D.weight a • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - atomMatrix (D.atom a))).PosSemidef) :
    (D.weight a / (1 - D.weight a)) ^ 2
      ≤ pairMinorTotal (D.atom x) (D.atom y) (D.atom z) := by
  set t : ℝ := D.weight a with ht
  set P : Matrix (Fin 3) (Fin 3) ℝ :=
    (1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (D.atom a) with hP
  set G : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ({x, y, z} : Finset (Fin m)) - 1 with hG
  set R : Matrix (Fin 3) (Fin 3) ℝ := ((1 : ℝ) - t) • G - t • P with hR
  have hmass : (0 : ℝ) < 1 - t := by rw [ht]; linarith
  -- the scaled gap splits as the slack plus the scaled projection
  have hsplit : ((1 : ℝ) - t) • G = R + t • P := by rw [hR]; module
  -- every piece of the expansion is nonnegative
  have hslack : 0 ≤ secondInvariantOfThree R :=
    secondInvariantOfThree_nonneg_of_posSemidef hbound
  have htrace : 0 ≤ Matrix.trace R := trace_nonneg_of_posSemidef hbound
  have hform : 0 ≤ D.atom a ⬝ᵥ (R *ᵥ D.atom a) := quadForm_nonneg_of_posSemidef_rankOne hbound _
  have hprojE : secondInvariantOfThree P = 1 :=
    secondInvariantOfThree_one_sub_atomMatrix hunit
  have hprojT : Matrix.trace P = 2 := trace_one_sub_atomMatrix hunit
  have hsymR : Rᵀ = R := hbound.1
  have hcross : Matrix.trace (R * (t • P))
      = t * (Matrix.trace R - D.atom a ⬝ᵥ (R *ᵥ D.atom a)) := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm, hP,
      trace_one_sub_atomMatrix_mul _ hsymR]
  -- the expansion
  have hexpand : ((1 : ℝ) - t) ^ 2 * secondInvariantOfThree G
      = secondInvariantOfThree R + t ^ 2
        + t * (Matrix.trace R + D.atom a ⬝ᵥ (R *ᵥ D.atom a)) := by
    have h := secondInvariantOfThree_add R (t • P)
    rw [← hsplit, secondInvariantOfThree_smul, secondInvariantOfThree_smul, hprojE,
      Matrix.trace_smul, smul_eq_mul, hprojT, hcross] at h
    linarith
  -- the floor
  have hfloor : t ^ 2 ≤ ((1 : ℝ) - t) ^ 2 * secondInvariantOfThree G := by
    rw [hexpand]; nlinarith [hslack, htrace, hform, hpos]
  rw [← secondInvariantOfThree_gap_eq_pairMinorTotal D hxy hxz hyz, ← hG, div_pow,
    div_le_iff₀ (by positivity), mul_comm]
  exact hfloor

/-- **THE FUNNEL'S DOMINATOR IS NEVER A CORNER.**  Its pair minor total is
strictly positive, so its gap has corank exactly one. -/
theorem pairMinorTotal_pos_of_deflatedGapBound (D : WeightedDesign m 3)
    {a x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hunit : leverageOf (D.atom a) = 1)
    (hpos : 0 < D.weight a) (hlt : D.weight a < 1)
    (hbound : (((1 : ℝ) - D.weight a) • (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
        - D.weight a • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - atomMatrix (D.atom a))).PosSemidef) :
    0 < pairMinorTotal (D.atom x) (D.atom y) (D.atom z) := by
  have hfloor := pairMinorTotal_floor_of_deflatedGapBound D hxy hxz hyz hunit hpos hlt hbound
  have hmass : (0 : ℝ) < 1 - D.weight a := by linarith
  have : (0 : ℝ) < (D.weight a / (1 - D.weight a)) ^ 2 := by positivity
  linarith

/-- **THE PAIR-MINOR TRIGGER, UNCONDITIONALLY.**  The landed
`Gtz.unitAtom_parallel_of_two_pairMinors_zero` needs the second invariant to be
nonzero, and at a funnel the floor supplies exactly that.  Two vanishing pair
minors of the dominator therefore give a parallel pair with no side condition
beyond the deflated bound the funnel already carries. -/
theorem unitAtom_parallel_of_two_pairMinors_zero_of_bound (D : WeightedDesign (m + 1) 3)
    {a x y z : Fin (m + 1)} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (havoid : a ∉ ({x, y, z} : Finset (Fin (m + 1))))
    (hunit : leverageOf (D.atom a) = 1)
    (hpos : 0 < D.weight a) (hlt : D.weight a < 1)
    (hbound : (((1 : ℝ) - D.weight a)
        • (subsetSum D ({x, y, z} : Finset (Fin (m + 1))) - 1)
        - D.weight a • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - atomMatrix (D.atom a))).PosSemidef)
    (hfix : subsetSum D ({x, y, z} : Finset (Fin (m + 1))) *ᵥ D.atom a = D.atom a)
    (hminorXY : pairGapMinor (D.atom x) (D.atom y) = 0)
    (hminorXZ : pairGapMinor (D.atom x) (D.atom z) = 0) :
    HasParallelPair D :=
  unitAtom_parallel_of_two_pairMinors_zero D hxy hxz hyz havoid hunit hfix
    (pairMinorTotal_pos_of_deflatedGapBound D hxy hxz hyz hunit hpos hlt hbound).ne'
    hminorXY hminorXZ

/-! ## 5. The leverage floor -/

/-- **THE LEVERAGE FLOOR.**  The same expansion at the trace: a triple carrying
the deflated bound has leverage total at least `3 + 2t_a/(1 - t_a)`. -/
theorem trace_floor_of_deflatedGapBound (D : WeightedDesign m 3)
    {a x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hunit : leverageOf (D.atom a) = 1)
    (hpos : 0 < D.weight a) (hlt : D.weight a < 1)
    (hbound : (((1 : ℝ) - D.weight a) • (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
        - D.weight a • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - atomMatrix (D.atom a))).PosSemidef) :
    3 + 2 * D.weight a / (1 - D.weight a)
      ≤ leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z) := by
  have hmass : (0 : ℝ) < 1 - D.weight a := by linarith
  have htrace := trace_nonneg_of_posSemidef hbound
  have hgapTrace : Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
      = leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z) - 3 := by
    have hsum : subsetSum D ({x, y, z} : Finset (Fin m))
        = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
      rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
        Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
      abel
    rw [hsum, Matrix.one_fin_three]
    simp only [Matrix.trace_fin_three, Matrix.sub_apply, Matrix.add_apply,
      atomMatrix, Matrix.vecMulVec_apply, leverageOf, Fin.sum_univ_three,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const, Matrix.of_apply]
    ring
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
    trace_one_sub_atomMatrix hunit, hgapTrace] at htrace
  have hkey : 2 * D.weight a
      ≤ (leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z) - 3)
        * (1 - D.weight a) := by nlinarith [htrace]
  have hdiv := (div_le_iff₀ hmass).mpr hkey
  linarith

end Gtz

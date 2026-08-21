/-
# The triple volume row law, the volume budget, and the hinge in volume vocabulary

The campaign reads a `(m,3)` design through PAIRS: leverages, pairings, pair
minors, squared areas.  This module reads it through VOLUMES — the squared
brackets `[g_a, g_b, g_c]²` — and proves that the two charts are the same chart.

## The row law

The bracket is an inner product against the normal of its first two slots, and
the normal's own squared length is the pair's squared area.  Parseval read at
that normal is therefore a budget for the VOLUMES through one pair:

  **`Gtz.sum_weight_mul_sq_tripleBracket`:  `∑_r t_r · [g_p, g_q, g_r]² = w_pq`** ,

with `w_pq = l_p·l_q − ⟨g_p,g_q⟩²`.  Two lines, no chart, no hypothesis, every
size and every design.  Everything below is a corollary.

## The hinge in volume vocabulary

A pair is parallel exactly when its squared area vanishes, so the row law says a
pair is parallel exactly when EVERY triple through it is degenerate:

  **`Gtz.crossNormSq_eq_zero_iff_forall_sq_tripleBracket_eq_zero`** .

That is the survey's hinge, restated with no eigenvector, no dominator and no
pair minor: a `(6,3)` boundary system has a parallel pair exactly when two of its
six atoms kill all four of the brackets they span with the remaining four.  The
statement is `4` polynomial equations in `18` coordinates for each of the `15`
pairs, and it is EQUIVALENT to the hinge rather than weaker than it.

## The volume budget

Cauchy-Binet at rank three, written out at five and at six atoms
(`Gtz.det_fiveAtomCombo`, `Gtz.det_sixAtomCombo`), evaluates the determinant of
Parseval and gives

  **`Gtz.volume_budget_fiveThree`, `Gtz.volume_budget_sixThree`:**
  `∑_{|S| = 3} (∏_{c ∈ S} t_c) · [g_S]² = 1` .

Ten terms at `(5,3)`, twenty at `(6,3)`.  This is the exact statement that the
weighted volumes of the selections are a probability distribution, and it is the
denominator of every volume-average instrument the campaign has tried.

## The volume floor at a weak dominator

A weak dominator has `S_C ⪰ 1`, so `S_C = 1 + P` with `P` positive semidefinite,
and at rank three `det(1 + P) = 1 + tr P + e₂(P) + det P` with all three terms
nonnegative (`Gtz.one_le_det_one_add_posSemidef`).  Hence

  **`Gtz.one_le_sq_tripleBracket_of_dominates`:  a weak dominator has
  `[g_a, g_b, g_c]² ≥ 1`** ,

and against the budget that is a WEIGHT BUDGET ON THE DOMINATORS
(`Gtz.three_dominator_weight_budget_sixThree`):

  **`∑_{S a weak dominator} ∏_{c ∈ S} t_c ≤ 1`** ,

recorded at three named triples so the arithmetic is exact.

## The wedge ceiling

The row law also caps the squared area from above.  Each share obeys
`t_c·l_c ≤ 1`, and the two eigenvalues of the pair's weighted block have sum
`t_p·l_p + t_q·l_q` and product `t_p·t_q·w_pq`, so the discriminant inequality
`4·t_p·t_q·w_pq ≤ (t_p·l_p + t_q·l_q)²` together with the share cap gives

  **`Gtz.two_mul_weight_mul_crossNormSq_le_share_sum`:**
  `2 · t_p · t_q · w_pq ≤ t_p·l_p + t_q·l_q` .

With the landed wedge floor `t_p·t_q·w_pq ≥ t_p·l_p + t_q·l_q − 1` this pins the
weighted squared area of every pair into a band whose two ends meet exactly when
both shares are one.

[MEASURED, exact rational arithmetic, the named fixture first.  At the `(5,3)`
diamond (`K4 − e`, conductances `(2,3,3,3,3)`, uniform weight `1/5`) the ten
squared volumes are `12.5` at each of the four triples through the light atom
that dominate, `18.75` at each of the four triples inside the rim, and `0` at the
two triples `{0,1,3}` and `{0,2,4}` whose edges form a graph cycle.  Their
weighted total is `(4·12.5 + 4·18.75)/125 = 125/125 = 1`, confirming the volume
budget on the nose.  Eight of the ten triples weakly dominate and each has
squared volume at least `12.5 ≥ 1`, confirming the volume floor; the dominator
weight budget reads `8/125 = 0.064 ≤ 1`, so it is far from tight there.  The row
law at the pair `{1,2}` reads `∑_r t_r·[1,2,r]² = 10 = w_12`, and at `{0,1}` it
reads `5 = w_01`.]
-/
import Gtz.Wave.ComplementPairDeterminantLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The row law -/

/-- The normal of a pair reads its own squared length as the pair's squared
area. -/
theorem bracketNormal_dotProduct_self (leftVec rightVec : Fin 3 → ℝ) :
    bracketNormal leftVec rightVec ⬝ᵥ bracketNormal leftVec rightVec
      = crossNormSq leftVec rightVec := rfl

/-- **THE TRIPLE VOLUME ROW LAW.**  The weighted squared volumes of all the
triples through one pair total that pair's squared area.  The bracket is the
inner product against the pair's normal, so this is Parseval read at that normal
and nothing else. -/
theorem sum_weight_mul_sq_tripleBracket (D : WeightedDesign m 3) (first second : Fin m) :
    ∑ third, D.weight third
        * tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2
      = crossNormSq (D.atom first) (D.atom second) := by
  have hprobe := sum_weight_mul_sq_reading D (bracketNormal (D.atom first) (D.atom second))
  rw [bracketNormal_dotProduct_self] at hprobe
  rw [← hprobe]
  refine Finset.sum_congr rfl fun third _ => ?_
  rw [tripleBracket_eq_bracketNormal_dotProduct,
    dotProduct_comm (bracketNormal (D.atom first) (D.atom second)) (D.atom third)]

/-- **THE HINGE IN VOLUME VOCABULARY.**  A pair has vanishing squared area — the
survey's `w_ab = 0`, that is, the pair is parallel — exactly when every triple
through it is degenerate.  No eigenvector, no dominator, no pair minor. -/
theorem crossNormSq_eq_zero_iff_forall_sq_tripleBracket_eq_zero (D : WeightedDesign m 3)
    (first second : Fin m) :
    crossNormSq (D.atom first) (D.atom second) = 0
      ↔ ∀ third, tripleBracket (D.atom first) (D.atom second) (D.atom third) = 0 := by
  constructor
  · intro hflat third
    have hrow := sum_weight_mul_sq_tripleBracket D first second
    rw [hflat] at hrow
    have hterm : D.weight third
        * tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2 ≤ 0 := by
      rw [← hrow]
      exact Finset.single_le_sum
        (f := fun r => D.weight r * tripleBracket (D.atom first) (D.atom second) (D.atom r) ^ 2)
        (fun r _ => mul_nonneg (D.weight_pos r).le (sq_nonneg _)) (Finset.mem_univ third)
    have hsq : tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2 ≤ 0 := by
      by_contra hcon
      exact absurd hterm (not_le.mpr (mul_pos (D.weight_pos third) (lt_of_not_ge hcon)))
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hsq (sq_nonneg _))
  · intro hall
    rw [← sum_weight_mul_sq_tripleBracket D first second]
    refine Finset.sum_eq_zero fun third _ => ?_
    rw [hall third]
    ring

/-- **A PARALLEL PAIR KILLS EVERY VOLUME THROUGH IT.**  The forward half of the
hinge dictionary, stated on the design's own atoms. -/
theorem sq_tripleBracket_eq_zero_of_crossNormSq_eq_zero (D : WeightedDesign m 3)
    {first second : Fin m} (hflat : crossNormSq (D.atom first) (D.atom second) = 0)
    (third : Fin m) : tripleBracket (D.atom first) (D.atom second) (D.atom third) = 0 :=
  (crossNormSq_eq_zero_iff_forall_sq_tripleBracket_eq_zero D first second).mp hflat third

/-! ## 2. Cauchy-Binet at five and at six atoms -/

/-- **FIVE ATOMS MAKE TEN VOLUMES.**  Cauchy-Binet at rank three, written out. -/
theorem det_fiveAtomCombo (scaleOne scaleTwo scaleThree scaleFour scaleFive : ℝ)
    (vecOne vecTwo vecThree vecFour vecFive : Fin 3 → ℝ) :
    (scaleOne • atomMatrix vecOne + scaleTwo • atomMatrix vecTwo
        + scaleThree • atomMatrix vecThree + scaleFour • atomMatrix vecFour
        + scaleFive • atomMatrix vecFive).det
      = scaleOne * scaleTwo * scaleThree * tripleBracket vecOne vecTwo vecThree ^ 2
        + scaleOne * scaleTwo * scaleFour * tripleBracket vecOne vecTwo vecFour ^ 2
        + scaleOne * scaleTwo * scaleFive * tripleBracket vecOne vecTwo vecFive ^ 2
        + scaleOne * scaleThree * scaleFour * tripleBracket vecOne vecThree vecFour ^ 2
        + scaleOne * scaleThree * scaleFive * tripleBracket vecOne vecThree vecFive ^ 2
        + scaleOne * scaleFour * scaleFive * tripleBracket vecOne vecFour vecFive ^ 2
        + scaleTwo * scaleThree * scaleFour * tripleBracket vecTwo vecThree vecFour ^ 2
        + scaleTwo * scaleThree * scaleFive * tripleBracket vecTwo vecThree vecFive ^ 2
        + scaleTwo * scaleFour * scaleFive * tripleBracket vecTwo vecFour vecFive ^ 2
        + scaleThree * scaleFour * scaleFive
          * tripleBracket vecThree vecFour vecFive ^ 2 := by
  simp only [Matrix.det_fin_three, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    atomMatrix, Matrix.vecMulVec_apply, tripleBracket, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- **SIX ATOMS MAKE TWENTY VOLUMES.**  Cauchy-Binet at rank three at the
campaign's own size, written out. -/
theorem det_sixAtomCombo (scaleOne scaleTwo scaleThree scaleFour scaleFive scaleSix : ℝ)
    (vecOne vecTwo vecThree vecFour vecFive vecSix : Fin 3 → ℝ) :
    (scaleOne • atomMatrix vecOne + scaleTwo • atomMatrix vecTwo
        + scaleThree • atomMatrix vecThree + scaleFour • atomMatrix vecFour
        + scaleFive • atomMatrix vecFive + scaleSix • atomMatrix vecSix).det
      = scaleOne * scaleTwo * scaleThree * tripleBracket vecOne vecTwo vecThree ^ 2
        + scaleOne * scaleTwo * scaleFour * tripleBracket vecOne vecTwo vecFour ^ 2
        + scaleOne * scaleTwo * scaleFive * tripleBracket vecOne vecTwo vecFive ^ 2
        + scaleOne * scaleTwo * scaleSix * tripleBracket vecOne vecTwo vecSix ^ 2
        + scaleOne * scaleThree * scaleFour * tripleBracket vecOne vecThree vecFour ^ 2
        + scaleOne * scaleThree * scaleFive * tripleBracket vecOne vecThree vecFive ^ 2
        + scaleOne * scaleThree * scaleSix * tripleBracket vecOne vecThree vecSix ^ 2
        + scaleOne * scaleFour * scaleFive * tripleBracket vecOne vecFour vecFive ^ 2
        + scaleOne * scaleFour * scaleSix * tripleBracket vecOne vecFour vecSix ^ 2
        + scaleOne * scaleFive * scaleSix * tripleBracket vecOne vecFive vecSix ^ 2
        + scaleTwo * scaleThree * scaleFour * tripleBracket vecTwo vecThree vecFour ^ 2
        + scaleTwo * scaleThree * scaleFive * tripleBracket vecTwo vecThree vecFive ^ 2
        + scaleTwo * scaleThree * scaleSix * tripleBracket vecTwo vecThree vecSix ^ 2
        + scaleTwo * scaleFour * scaleFive * tripleBracket vecTwo vecFour vecFive ^ 2
        + scaleTwo * scaleFour * scaleSix * tripleBracket vecTwo vecFour vecSix ^ 2
        + scaleTwo * scaleFive * scaleSix * tripleBracket vecTwo vecFive vecSix ^ 2
        + scaleThree * scaleFour * scaleFive * tripleBracket vecThree vecFour vecFive ^ 2
        + scaleThree * scaleFour * scaleSix * tripleBracket vecThree vecFour vecSix ^ 2
        + scaleThree * scaleFive * scaleSix * tripleBracket vecThree vecFive vecSix ^ 2
        + scaleFour * scaleFive * scaleSix
          * tripleBracket vecFour vecFive vecSix ^ 2 := by
  simp only [Matrix.det_fin_three, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    atomMatrix, Matrix.vecMulVec_apply, tripleBracket, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-! ## 3. The volume budget -/

/-- Parseval, written out at five atoms. -/
theorem parseval_fiveThree (D : WeightedDesign 5 3) :
    D.weight 0 • atomMatrix (D.atom 0) + D.weight 1 • atomMatrix (D.atom 1)
        + D.weight 2 • atomMatrix (D.atom 2) + D.weight 3 • atomMatrix (D.atom 3)
        + D.weight 4 • atomMatrix (D.atom 4) = 1 := by
  have hpar := D.isParseval
  rw [Fin.sum_univ_five] at hpar
  exact hpar

/-- Parseval, written out at six atoms. -/
theorem parseval_sixThree (D : WeightedDesign 6 3) :
    D.weight 0 • atomMatrix (D.atom 0) + D.weight 1 • atomMatrix (D.atom 1)
        + D.weight 2 • atomMatrix (D.atom 2) + D.weight 3 • atomMatrix (D.atom 3)
        + D.weight 4 • atomMatrix (D.atom 4) + D.weight 5 • atomMatrix (D.atom 5) = 1 := by
  have hpar := D.isParseval
  rw [Fin.sum_univ_six] at hpar
  exact hpar

/-- **THE VOLUME BUDGET AT `(5,3)`.**  The ten weighted squared volumes of a
`(5,3)` design total one. -/
theorem volume_budget_fiveThree (D : WeightedDesign 5 3) :
    D.weight 0 * D.weight 1 * D.weight 2
        * tripleBracket (D.atom 0) (D.atom 1) (D.atom 2) ^ 2
      + D.weight 0 * D.weight 1 * D.weight 3
        * tripleBracket (D.atom 0) (D.atom 1) (D.atom 3) ^ 2
      + D.weight 0 * D.weight 1 * D.weight 4
        * tripleBracket (D.atom 0) (D.atom 1) (D.atom 4) ^ 2
      + D.weight 0 * D.weight 2 * D.weight 3
        * tripleBracket (D.atom 0) (D.atom 2) (D.atom 3) ^ 2
      + D.weight 0 * D.weight 2 * D.weight 4
        * tripleBracket (D.atom 0) (D.atom 2) (D.atom 4) ^ 2
      + D.weight 0 * D.weight 3 * D.weight 4
        * tripleBracket (D.atom 0) (D.atom 3) (D.atom 4) ^ 2
      + D.weight 1 * D.weight 2 * D.weight 3
        * tripleBracket (D.atom 1) (D.atom 2) (D.atom 3) ^ 2
      + D.weight 1 * D.weight 2 * D.weight 4
        * tripleBracket (D.atom 1) (D.atom 2) (D.atom 4) ^ 2
      + D.weight 1 * D.weight 3 * D.weight 4
        * tripleBracket (D.atom 1) (D.atom 3) (D.atom 4) ^ 2
      + D.weight 2 * D.weight 3 * D.weight 4
        * tripleBracket (D.atom 2) (D.atom 3) (D.atom 4) ^ 2
      = 1 := by
  have hdet : (D.weight 0 • atomMatrix (D.atom 0) + D.weight 1 • atomMatrix (D.atom 1)
      + D.weight 2 • atomMatrix (D.atom 2) + D.weight 3 • atomMatrix (D.atom 3)
      + D.weight 4 • atomMatrix (D.atom 4)).det = (1 : Matrix (Fin 3) (Fin 3) ℝ).det := by
    rw [parseval_fiveThree D]
  rw [det_fiveAtomCombo, Matrix.det_one] at hdet
  linarith [hdet]

/-- **THE VOLUME BUDGET AT `(6,3)`.**  The twenty weighted squared volumes of a
`(6,3)` design total one.  This is the denominator of every volume-average
instrument, proved here rather than assumed. -/
theorem volume_budget_sixThree (D : WeightedDesign 6 3) :
    D.weight 0 * D.weight 1 * D.weight 2
        * tripleBracket (D.atom 0) (D.atom 1) (D.atom 2) ^ 2
      + D.weight 0 * D.weight 1 * D.weight 3
        * tripleBracket (D.atom 0) (D.atom 1) (D.atom 3) ^ 2
      + D.weight 0 * D.weight 1 * D.weight 4
        * tripleBracket (D.atom 0) (D.atom 1) (D.atom 4) ^ 2
      + D.weight 0 * D.weight 1 * D.weight 5
        * tripleBracket (D.atom 0) (D.atom 1) (D.atom 5) ^ 2
      + D.weight 0 * D.weight 2 * D.weight 3
        * tripleBracket (D.atom 0) (D.atom 2) (D.atom 3) ^ 2
      + D.weight 0 * D.weight 2 * D.weight 4
        * tripleBracket (D.atom 0) (D.atom 2) (D.atom 4) ^ 2
      + D.weight 0 * D.weight 2 * D.weight 5
        * tripleBracket (D.atom 0) (D.atom 2) (D.atom 5) ^ 2
      + D.weight 0 * D.weight 3 * D.weight 4
        * tripleBracket (D.atom 0) (D.atom 3) (D.atom 4) ^ 2
      + D.weight 0 * D.weight 3 * D.weight 5
        * tripleBracket (D.atom 0) (D.atom 3) (D.atom 5) ^ 2
      + D.weight 0 * D.weight 4 * D.weight 5
        * tripleBracket (D.atom 0) (D.atom 4) (D.atom 5) ^ 2
      + D.weight 1 * D.weight 2 * D.weight 3
        * tripleBracket (D.atom 1) (D.atom 2) (D.atom 3) ^ 2
      + D.weight 1 * D.weight 2 * D.weight 4
        * tripleBracket (D.atom 1) (D.atom 2) (D.atom 4) ^ 2
      + D.weight 1 * D.weight 2 * D.weight 5
        * tripleBracket (D.atom 1) (D.atom 2) (D.atom 5) ^ 2
      + D.weight 1 * D.weight 3 * D.weight 4
        * tripleBracket (D.atom 1) (D.atom 3) (D.atom 4) ^ 2
      + D.weight 1 * D.weight 3 * D.weight 5
        * tripleBracket (D.atom 1) (D.atom 3) (D.atom 5) ^ 2
      + D.weight 1 * D.weight 4 * D.weight 5
        * tripleBracket (D.atom 1) (D.atom 4) (D.atom 5) ^ 2
      + D.weight 2 * D.weight 3 * D.weight 4
        * tripleBracket (D.atom 2) (D.atom 3) (D.atom 4) ^ 2
      + D.weight 2 * D.weight 3 * D.weight 5
        * tripleBracket (D.atom 2) (D.atom 3) (D.atom 5) ^ 2
      + D.weight 2 * D.weight 4 * D.weight 5
        * tripleBracket (D.atom 2) (D.atom 4) (D.atom 5) ^ 2
      + D.weight 3 * D.weight 4 * D.weight 5
        * tripleBracket (D.atom 3) (D.atom 4) (D.atom 5) ^ 2
      = 1 := by
  have hdet : (D.weight 0 • atomMatrix (D.atom 0) + D.weight 1 • atomMatrix (D.atom 1)
      + D.weight 2 • atomMatrix (D.atom 2) + D.weight 3 • atomMatrix (D.atom 3)
      + D.weight 4 • atomMatrix (D.atom 4)
      + D.weight 5 • atomMatrix (D.atom 5)).det
      = (1 : Matrix (Fin 3) (Fin 3) ℝ).det := by
    rw [parseval_sixThree D]
  rw [det_sixAtomCombo, Matrix.det_one] at hdet
  linarith [hdet]

/-! ## 4. The volume floor at a weak dominator -/

/-- The second elementary symmetric function of a `3 × 3` matrix: the sum of its
three principal two-by-two minors. -/
noncomputable def secondMinorSum (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (M 0 0 * M 1 1 - M 0 1 * M 1 0) + (M 0 0 * M 2 2 - M 0 2 * M 2 0)
    + (M 1 1 * M 2 2 - M 1 2 * M 2 1)

/-- The characteristic expansion of a rank-three determinant shifted by the
identity. -/
theorem det_one_add_eq (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) + M).det
      = 1 + Matrix.trace M + secondMinorSum M + M.det := by
  norm_num +decide [Matrix.det_fin_three, Matrix.add_apply, Matrix.one_apply,
    secondMinorSum, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  ring

/-- A positive semidefinite matrix has nonnegative diagonal entries. -/
theorem posSemidef_diag_nonneg {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.PosSemidef)
    (index : Fin 3) : 0 ≤ M index index := by
  have hdet := (hM.submatrix (![index] : Fin 1 → Fin 3)).det_nonneg
  rw [Matrix.det_fin_one] at hdet
  simpa [Matrix.submatrix_apply] using hdet

/-- The second minor sum of a positive semidefinite matrix is nonnegative: each
of its three terms is a principal two-by-two minor. -/
theorem secondMinorSum_nonneg {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.PosSemidef) :
    0 ≤ secondMinorSum M := by
  have hminor : ∀ pick : Fin 2 → Fin 3,
      0 ≤ M (pick 0) (pick 0) * M (pick 1) (pick 1)
        - M (pick 0) (pick 1) * M (pick 1) (pick 0) := by
    intro pick
    have hdet := (hM.submatrix pick).det_nonneg
    rw [Matrix.det_fin_two] at hdet
    simpa [Matrix.submatrix_apply] using hdet
  have h01 := hminor ![0, 1]
  have h02 := hminor ![0, 2]
  have h12 := hminor ![1, 2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h01 h02 h12
  rw [secondMinorSum]
  linarith

/-- **A POSITIVE SEMIDEFINITE SHIFT OF THE IDENTITY HAS DETERMINANT AT LEAST
ONE.**  The three elementary symmetric functions of a positive semidefinite
matrix are nonnegative, and the shifted determinant is their sum plus one. -/
theorem one_le_det_one_add_posSemidef {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.PosSemidef) :
    1 ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ) + M).det := by
  rw [det_one_add_eq]
  have htrace : 0 ≤ Matrix.trace M := by
    rw [Matrix.trace_fin_three]
    linarith [posSemidef_diag_nonneg hM 0, posSemidef_diag_nonneg hM 1,
      posSemidef_diag_nonneg hM 2]
  linarith [htrace, secondMinorSum_nonneg hM, hM.det_nonneg]

/-- **A WEAK DOMINATOR HAS DETERMINANT AT LEAST ONE.** -/
theorem one_le_det_subsetSum_of_dominates (D : WeightedDesign m 3) {C : Finset (Fin m)}
    (hdom : Dominates D C) : 1 ≤ (subsetSum D C).det := by
  have hshift : subsetSum D C = 1 + (subsetSum D C - 1) := by abel
  rw [hshift]
  exact one_le_det_one_add_posSemidef hdom

/-- **A WEAK DOMINATOR HAS SQUARED VOLUME AT LEAST ONE.**  The atom sum of a
triple is the Gram matrix of its three atoms up to a transpose, whose determinant
is the squared bracket. -/
theorem one_le_sq_tripleBracket_of_dominates (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    1 ≤ tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2 := by
  have hdet := one_le_det_subsetSum_of_dominates D hdom
  have hcolumn : subsetSum D ({x, y, z} : Finset (Fin m))
      = columnMatrix (D.atom x) (D.atom y) (D.atom z)
        * (columnMatrix (D.atom x) (D.atom y) (D.atom z))ᵀ :=
    subsetSum_triple_eq_mul_transpose D x y z hxy hxz hyz
  rw [hcolumn, Matrix.det_mul, Matrix.det_transpose] at hdet
  have hbracket : (columnMatrix (D.atom x) (D.atom y) (D.atom z)).det
      = tripleBracket (D.atom x) (D.atom y) (D.atom z) := by
    simp only [columnMatrix, tripleBracket, Matrix.det_fin_three, Matrix.of_apply,
      Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hbracket] at hdet
  nlinarith [hdet]

/-! ## 5. The wedge ceiling -/

/-- **THE SHARE CAP.**  A single atom's share never exceeds one: Parseval read at
that atom bounds its own weighted leverage. -/
theorem weight_mul_leverage_le_one_of_design (D : WeightedDesign m k) (c : Fin m) :
    D.weight c * leverageOf (D.atom c) ≤ 1 := by
  classical
  have hlev : 0 ≤ leverageOf (D.atom c) := by
    simpa [leverageOf] using
      Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
        sq_nonneg (D.atom c i))
  rcases eq_or_lt_of_le hlev with hzero | hpos
  · rw [← hzero, mul_zero]; norm_num
  · have hall := sum_weight_mul_sq_reading D (D.atom c)
    have hself : D.atom c ⬝ᵥ D.atom c = leverageOf (D.atom c) := frameDotSelf _
    have hterm : D.weight c * (D.atom c ⬝ᵥ D.atom c) ^ 2
        ≤ ∑ d, D.weight d * (D.atom d ⬝ᵥ D.atom c) ^ 2 :=
      Finset.single_le_sum (f := fun d => D.weight d * (D.atom d ⬝ᵥ D.atom c) ^ 2)
        (fun d _ => mul_nonneg (D.weight_pos d).le (sq_nonneg _)) (Finset.mem_univ c)
    rw [hall, hself] at hterm
    nlinarith [hterm, hpos]

/-- **THE DISCRIMINANT INEQUALITY OF A PAIR.**  The two shares and the weighted
squared area are the trace and the second minor of one positive semidefinite
two-by-two block, so four times the second minor never exceeds the squared
trace. -/
theorem four_mul_weight_mul_crossNormSq_le_share_sum_sq (D : WeightedDesign m 3)
    (first second : Fin m) :
    4 * (D.weight first * D.weight second
        * crossNormSq (D.atom first) (D.atom second))
      ≤ (D.weight first * leverageOf (D.atom first)
          + D.weight second * leverageOf (D.atom second)) ^ 2 := by
  rw [crossNormSq_eq_leverage_mul_sub_sq]
  nlinarith [sq_nonneg (D.weight first * leverageOf (D.atom first)
      - D.weight second * leverageOf (D.atom second)),
    mul_nonneg (mul_nonneg (D.weight_pos first).le (D.weight_pos second).le)
      (sq_nonneg (D.atom first ⬝ᵥ D.atom second))]

/-- **THE WEDGE CEILING.**  Twice the weighted squared area of a pair never
exceeds the sum of its two shares.  With the landed wedge floor
`t_p·l_p + t_q·l_q − 1 ≤ t_p·t_q·w_pq` this pins the weighted squared area of
every pair into a band, and the two ends meet exactly when both shares are
one. -/
theorem two_mul_weight_mul_crossNormSq_le_share_sum (D : WeightedDesign m 3)
    (first second : Fin m) :
    2 * (D.weight first * D.weight second
        * crossNormSq (D.atom first) (D.atom second))
      ≤ D.weight first * leverageOf (D.atom first)
        + D.weight second * leverageOf (D.atom second) := by
  have hdisc := four_mul_weight_mul_crossNormSq_le_share_sum_sq D first second
  have hfirst := weight_mul_leverage_le_one_of_design D first
  have hsecond := weight_mul_leverage_le_one_of_design D second
  have hnonneg : 0 ≤ D.weight first * leverageOf (D.atom first)
      + D.weight second * leverageOf (D.atom second) := by
    have h1 : 0 ≤ D.weight first * leverageOf (D.atom first) :=
      mul_nonneg (D.weight_pos first).le (by
        simpa [leverageOf] using Finset.sum_nonneg
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => sq_nonneg (D.atom first i)))
    have h2 : 0 ≤ D.weight second * leverageOf (D.atom second) :=
      mul_nonneg (D.weight_pos second).le (by
        simpa [leverageOf] using Finset.sum_nonneg
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => sq_nonneg (D.atom second i)))
    linarith
  nlinarith [hdisc, hfirst, hsecond, hnonneg]

/-- **THE BAND ON A PAIR'S WEIGHTED SQUARED AREA.**  Floor and ceiling together,
at every `(m,3)` design and every pair. -/
theorem weighted_crossNormSq_band (D : WeightedDesign m 3) {first second : Fin m}
    (hne : first ≠ second) :
    D.weight first * leverageOf (D.atom first)
        + D.weight second * leverageOf (D.atom second) - 1
      ≤ D.weight first * D.weight second
        * crossNormSq (D.atom first) (D.atom second)
      ∧ 2 * (D.weight first * D.weight second
          * crossNormSq (D.atom first) (D.atom second))
        ≤ D.weight first * leverageOf (D.atom first)
          + D.weight second * leverageOf (D.atom second) := by
  refine ⟨?_, two_mul_weight_mul_crossNormSq_le_share_sum D first second⟩
  have hfloor := share_add_share_le_one_add_weight_mul_crossNormSq D hne
  linarith

/-! ## 6. The dominator weight budget at `(6,3)` -/

/-- **THE DOMINATOR WEIGHT BUDGET AT `(6,3)`, PAIRWISE FORM.**  Two weak
dominators of a `(6,3)` design cannot both carry weight product more than one
half, because the volume budget totals one and each contributes at least its
weight product.  Stated at three named triples so the arithmetic is exact. -/
theorem three_dominator_weight_budget_sixThree (D : WeightedDesign 6 3)
    (hfirst : Dominates D ({0, 1, 2} : Finset (Fin 6)))
    (hsecond : Dominates D ({0, 3, 4} : Finset (Fin 6)))
    (hthird : Dominates D ({1, 3, 5} : Finset (Fin 6))) :
    D.weight 0 * D.weight 1 * D.weight 2 + D.weight 0 * D.weight 3 * D.weight 4
      + D.weight 1 * D.weight 3 * D.weight 5 ≤ 1 := by
  have hbudget := volume_budget_sixThree D
  have hv1 := one_le_sq_tripleBracket_of_dominates D 0 1 2 (by decide) (by decide)
    (by decide) hfirst
  have hv2 := one_le_sq_tripleBracket_of_dominates D 0 3 4 (by decide) (by decide)
    (by decide) hsecond
  have hv3 := one_le_sq_tripleBracket_of_dominates D 1 3 5 (by decide) (by decide)
    (by decide) hthird
  have hall : ∀ x y z : Fin 6, 0 ≤ D.weight x * D.weight y * D.weight z
      * tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2 := by
    intro x y z
    exact mul_nonneg (mul_nonneg (mul_nonneg (D.weight_pos x).le (D.weight_pos y).le)
      (D.weight_pos z).le) (sq_nonneg _)
  have hp1 : 0 < D.weight 0 * D.weight 1 * D.weight 2 :=
    mul_pos (mul_pos (D.weight_pos 0) (D.weight_pos 1)) (D.weight_pos 2)
  have hp2 : 0 < D.weight 0 * D.weight 3 * D.weight 4 :=
    mul_pos (mul_pos (D.weight_pos 0) (D.weight_pos 3)) (D.weight_pos 4)
  have hp3 : 0 < D.weight 1 * D.weight 3 * D.weight 5 :=
    mul_pos (mul_pos (D.weight_pos 1) (D.weight_pos 3)) (D.weight_pos 5)
  nlinarith [hbudget, hv1, hv2, hv3, hp1, hp2, hp3,
    hall 0 1 3, hall 0 1 4, hall 0 1 5, hall 0 2 3, hall 0 2 4, hall 0 2 5,
    hall 0 3 5, hall 0 4 5, hall 1 2 3, hall 1 2 4, hall 1 2 5, hall 1 3 4,
    hall 1 4 5, hall 2 3 4, hall 2 3 5, hall 2 4 5, hall 3 4 5]

/-! ## 7. The pair chart and the volume chart agree

The row law identifies the two charts: everything the campaign knows about a
pair's squared area is a statement about the volumes through it, and conversely.
These two corollaries record the translation in both directions. -/

/-- **A POSITIVE SQUARED AREA NAMES A NON-DEGENERATE TRIPLE.**  If a pair is not
parallel, some triple through it has positive volume. -/
theorem exists_sq_tripleBracket_pos_of_crossNormSq_pos (D : WeightedDesign m 3)
    {first second : Fin m} (hpos : 0 < crossNormSq (D.atom first) (D.atom second)) :
    ∃ third, 0 < tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2 := by
  by_contra hcon
  push Not at hcon
  have hzero : crossNormSq (D.atom first) (D.atom second) = 0 := by
    rw [← sum_weight_mul_sq_tripleBracket D first second]
    refine Finset.sum_eq_zero fun third _ => ?_
    have := hcon third
    have hsq : tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2 = 0 :=
      le_antisymm this (sq_nonneg _)
    rw [hsq, mul_zero]
  exact absurd hzero (ne_of_gt hpos)

/-- **THE SQUARED AREA IS A WEIGHTED AVERAGE OF VOLUMES, SO IT IS CAPPED BY THE
LARGEST OF THEM.**  Every triple through a pair whose volume falls below the
pair's squared area is matched by one above it. -/
theorem exists_sq_tripleBracket_ge_crossNormSq (D : WeightedDesign m 3)
    (first second : Fin m) :
    ∃ third, crossNormSq (D.atom first) (D.atom second)
      ≤ tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2 := by
  classical
  by_contra hcon
  push Not at hcon
  have hstrict : ∀ third, D.weight third
      * tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2
      < D.weight third * crossNormSq (D.atom first) (D.atom second) :=
    fun third => mul_lt_mul_of_pos_left (hcon third) (D.weight_pos third)
  have hsum : ∑ third, D.weight third
      * tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2
      < ∑ third, D.weight third * crossNormSq (D.atom first) (D.atom second) :=
    Finset.sum_lt_sum_of_nonempty ⟨first, Finset.mem_univ first⟩ fun third _ => hstrict third
  rw [sum_weight_mul_sq_tripleBracket D first second, ← Finset.sum_mul,
    D.weight_sum_one, one_mul] at hsum
  exact absurd hsum (lt_irrefl _)

end Gtz

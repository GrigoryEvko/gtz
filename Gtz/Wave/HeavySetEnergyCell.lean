import Gtz.Wave.TripleDeterminantSharp
import Gtz.Wave.ProjectionBlockObjective

/-!
# The triple energy, the aggregate cell, and the subset row budget

The quarter-slack cell (`Gtz.tripleDetForm_pos_of_quarterSlack`) prices the third
Sylvester minor by THREE separate pair conditions, one for each pairing.  This
file prices it by ONE condition on the pairings TOGETHER, and supplies the
projection-side budget that bounds that one quantity from the diagonal.

## The aggregate cell

Write `E = u² + v² + w²` for the **triple energy** of the three pairings and
`M = max p (max q r)` for the largest surplus.  Then

  * `p w² + q v² + r u² ≤ M · E`, because each surplus is at most `M` and the
    three squares total `E` — one inequality where the quarter-slack cell spends
    three,
  * `27 (u v w)² ≤ E³`, the arithmetic-geometric mean inequality on the three
    squares, which is what bounds the cross term.

So `M · E < p q r` together with `4 E³ < 27 (p q r − M E)²` forces the minor
positive, for EITHER sign of the triple product.  That is
`Gtz.tripleDetForm_pos_of_aggregate`, and it is root free and polynomial.

The aggregate hypothesis pays for the two smaller minors as well: `u² ≤ E` and
`M ≥ r` give `u² < p q` directly, and likewise for the other two pairs
(`Gtz.sq_lt_of_aggregate_first` and its companions).  So the cell is standalone
in the same sense the quarter-slack cell is — it assumes no triangle and it
needs no separate pair hypothesis.

## The two cells are INCOMPARABLE, and this file says so

Quarter-slack does not imply the aggregate condition: at `p = 10`, `q = r = 1`
the quarter-slack bound leaves `E` as large as `(pq + pr + qr)/4 = 21/4`, while
the aggregate condition needs `M E = 10 E < p q r = 10`, i.e. `E < 1`.
`Gtz.not_aggregate_of_quarterSlack_witness` records that.  The containment fails
in the other direction too, so neither cell subsumes the other and a covering
argument should read their union.

## The subset row budget

`Gtz.sum_erase_sq_projectionRow` gives the off-diagonal energy of a row of the
projection chart as exactly `t_c (1 − t_c)`.  Restricting the row sum to a subset
and adding over the subset gives

  `∑_{c ∈ T} ∑_{d ∈ T.erase c} P_cd² ≤ ∑_{c ∈ T} t_c (1 − t_c)`,

`Gtz.sum_sq_offDiag_subset_le_sum_coupling`, generic in size and rank.  At a
triple that is `2 E ≤ κ_a + κ_b + κ_c` (`Gtz.two_mul_tripleEnergyAt_le`), so the
one quantity the aggregate cell reads is bounded by the DIAGONAL alone.  The
per-entry corollary `Gtz.sq_projectionOffDiag_le_coupling` bounds a single
pairing square by either endpoint's coupling.

## The pigeonhole, and its price

Double counting inside a set gives a label whose own in-set energy is at least
the average (`Gtz.exists_label_in_set_energy_ge_average`), so dropping it leaves
a triple of small energy.  The resulting existence cell is honest but weak, and
the census below found it fires at `0.01%` of canonical points.  The double count
is landed because it is the reusable half, not because the cell is good.

## The global energy law, and where it is tight

Adding the row law over every label gives an EXACT identity,
`Gtz.sum_offDiag_sq_projection_eq`: the total off-diagonal energy of the chart is
`rank − ∑_c t_c²`.  One variance step then caps it,

  `∑_{c ≠ d} P_cd² ≤ rank − rank²/size`,

`Gtz.sum_offDiag_sq_projection_le`, **with equality exactly when every leverage
diagonal equals `rank/size`** (`Gtz.sum_offDiag_sq_projection_eq_iff_flat`).  At
`(6,3)` that is `t_c ≡ 1/2`, which is the equiangular profile — so the total
coupling the cells must fight is largest at exactly the configuration where every
sign-blind certificate is known to fail.  That is not a coincidence and this file
records it.

## Measured, on the canonical measure

Points are sampled as `P = F (Fᵀ F)⁻¹ Fᵀ` for an integer `6 × 3` matrix `F` with
no zero row and no two rows parallel, and a positive rational weight vector.
Five box widths, roughly twenty thousand accepted points each, exact rational
arithmetic, zero unsound firings for every cell here.

| heavy count | share | sign-free ceiling | aggregate | quarter slack |
|---|---|---|---|---|
| 3 | 0.1% | 100% | 100% | 100% |
| 4 | 5.0% | 100% | **100%** | 93.6% |
| 5 | 38.8% | 100% | 99.7% | 87.1% |
| 6 | 56.1% | 99.98% | 98.1% | 84.5% |

The aggregate cell decides every sampled design whose heavy set has four labels,
at every box width.  The ceiling column is the strongest a sign-blind cell can
reach (`Gtz.signFreeMargin_pos_iff_both_signs`), and it is not exhausted by the
quarter-slack constant.
-/

namespace Gtz

open Matrix Finset

variable {size rank m k : ℕ}

/-! ## 1. The triple energy and the arithmetic-geometric step -/

/-- The **triple energy**: the three pairings squared and added.  It is the one
quantity the aggregate cell reads about the off-diagonal. -/
def tripleEnergy (u v w : ℝ) : ℝ := u ^ 2 + v ^ 2 + w ^ 2

theorem tripleEnergy_nonneg (u v w : ℝ) : 0 ≤ tripleEnergy u v w := by
  rw [tripleEnergy]; positivity

theorem sq_le_tripleEnergy_first (u v w : ℝ) : u ^ 2 ≤ tripleEnergy u v w := by
  rw [tripleEnergy]; nlinarith [sq_nonneg v, sq_nonneg w]

theorem sq_le_tripleEnergy_second (u v w : ℝ) : v ^ 2 ≤ tripleEnergy u v w := by
  rw [tripleEnergy]; nlinarith [sq_nonneg u, sq_nonneg w]

theorem sq_le_tripleEnergy_third (u v w : ℝ) : w ^ 2 ≤ tripleEnergy u v w := by
  rw [tripleEnergy]; nlinarith [sq_nonneg u, sq_nonneg v]

theorem tripleEnergy_comm_first (u v w : ℝ) : tripleEnergy u v w = tripleEnergy v u w := by
  rw [tripleEnergy, tripleEnergy]; ring

theorem tripleEnergy_comm_third (u v w : ℝ) : tripleEnergy u v w = tripleEnergy u w v := by
  rw [tripleEnergy, tripleEnergy]; ring

/-- **The arithmetic-geometric step, on the three squares.**  Three nonnegative
reals are bounded in product by the cube of their third-mean.  Applied to
`u², v², w²` it caps the squared triple product by `E³/27`, and that is the only
place the cross term of the determinant is ever touched. -/
theorem twentySeven_mul_prod_le_cube (bigA bigB bigC : ℝ)
    (hA : 0 ≤ bigA) (hB : 0 ≤ bigB) (hC : 0 ≤ bigC) :
    27 * (bigA * bigB * bigC) ≤ (bigA + bigB + bigC) ^ 3 := by
  nlinarith [sq_nonneg (bigA - bigB), sq_nonneg (bigA - bigC), sq_nonneg (bigB - bigC),
    sq_nonneg (bigA + bigB - 2 * bigC), sq_nonneg (bigA + bigC - 2 * bigB),
    sq_nonneg (bigB + bigC - 2 * bigA), mul_nonneg hA hB, mul_nonneg hA hC,
    mul_nonneg hB hC, mul_nonneg (mul_nonneg hA hB) hC]

/-- **The cross-term cap.**  `27 (u v w)² ≤ E³` with `E` the triple energy. -/
theorem twentySeven_mul_sq_prod_le_tripleEnergy_cube (u v w : ℝ) :
    27 * (u * v * w) ^ 2 ≤ tripleEnergy u v w ^ 3 := by
  have hexpand : (u * v * w) ^ 2 = u ^ 2 * v ^ 2 * w ^ 2 := by ring
  rw [hexpand, tripleEnergy]
  exact twentySeven_mul_prod_le_cube _ _ _ (sq_nonneg u) (sq_nonneg v) (sq_nonneg w)

/-! ## 2. The largest surplus -/

/-- The largest of the three surpluses. -/
noncomputable def maxSurplus (p q r : ℝ) : ℝ := max p (max q r)

theorem le_maxSurplus_first (p q r : ℝ) : p ≤ maxSurplus p q r := le_max_left _ _

theorem le_maxSurplus_second (p q r : ℝ) : q ≤ maxSurplus p q r :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem le_maxSurplus_third (p q r : ℝ) : r ≤ maxSurplus p q r :=
  le_trans (le_max_right _ _) (le_max_right _ _)

theorem maxSurplus_pos (p q r : ℝ) (hp : 0 < p) : 0 < maxSurplus p q r :=
  lt_of_lt_of_le hp (le_maxSurplus_first p q r)

theorem maxSurplus_nonneg (p q r : ℝ) (hp : 0 ≤ p) : 0 ≤ maxSurplus p q r :=
  le_trans hp (le_maxSurplus_first p q r)

/-- **The one inequality that replaces three.**  The surplus-weighted sum of the
three pairing squares is at most the largest surplus times the triple energy. -/
theorem weighted_sq_sum_le_maxSurplus_mul_tripleEnergy (p q r u v w : ℝ) :
    p * w ^ 2 + q * v ^ 2 + r * u ^ 2 ≤ maxSurplus p q r * tripleEnergy u v w := by
  have hpm := le_maxSurplus_first p q r
  have hqm := le_maxSurplus_second p q r
  have hrm := le_maxSurplus_third p q r
  rw [tripleEnergy]
  nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg w, hpm, hqm, hrm]

/-! ## 3. The aggregate cell -/

/-- **THE AGGREGATE CELL, real arithmetic.**  One condition on the triple energy
replaces the quarter-slack cell's three pair conditions, and the minor comes out
positive for either sign of the triple product.

The first hypothesis makes the surplus-weighted square sum strictly smaller than
the diagonal product.  The second says the gap left over dominates the
arithmetic-geometric cap on the cross term.  Both are polynomial and neither
reads a square root. -/
theorem tripleDetForm_pos_of_aggregate (p q r u v w : ℝ)
    (_hp : 0 < p) (_hq : 0 < q) (_hr : 0 < r)
    (hgap : maxSurplus p q r * tripleEnergy u v w < p * q * r)
    (hcross : 4 * tripleEnergy u v w ^ 3
      < 27 * (p * q * r - maxSurplus p q r * tripleEnergy u v w) ^ 2) :
    0 < tripleDetForm p q r u v w := by
  set bigE : ℝ := tripleEnergy u v w with hE
  set bigM : ℝ := maxSurplus p q r with hM
  have hgapPos : 0 < p * q * r - bigM * bigE := by linarith
  have hweighted : p * w ^ 2 + q * v ^ 2 + r * u ^ 2 ≤ bigM * bigE :=
    weighted_sq_sum_le_maxSurplus_mul_tripleEnergy p q r u v w
  have hcap : 27 * (u * v * w) ^ 2 ≤ bigE ^ 3 :=
    twentySeven_mul_sq_prod_le_tripleEnergy_cube u v w
  have hsq : (2 * (u * v * w)) ^ 2 < (p * q * r - bigM * bigE) ^ 2 := by
    have hfour : 4 * (27 * (u * v * w) ^ 2) ≤ 4 * bigE ^ 3 := by linarith
    nlinarith [hcap, hcross, hfour]
  have hlower : -(p * q * r - bigM * bigE) < 2 * (u * v * w) := by
    nlinarith [hsq, hgapPos, sq_nonneg (2 * (u * v * w) + (p * q * r - bigM * bigE))]
  rw [tripleDetForm]
  linarith

/-! ## 4. The aggregate cell pays for the two smaller minors -/

/-- The aggregate gap hypothesis bounds the first pairing square by the product
of its two surpluses.  The mechanism is that the third surplus is at most the
maximum, so dividing the gap by the maximum leaves at most `p q`. -/
theorem sq_lt_of_aggregate_first (p q r u v w : ℝ)
    (hp : 0 < p) (_hq : 0 < q) (hr : 0 < r)
    (hgap : maxSurplus p q r * tripleEnergy u v w < p * q * r) :
    u ^ 2 < p * q := by
  have hMpos : 0 < maxSurplus p q r := maxSurplus_pos p q r hp
  have hrm : r ≤ maxSurplus p q r := le_maxSurplus_third p q r
  have hsq : u ^ 2 ≤ tripleEnergy u v w := sq_le_tripleEnergy_first u v w
  have hEnn : 0 ≤ tripleEnergy u v w := tripleEnergy_nonneg u v w
  nlinarith [hgap, hsq, hrm, hMpos, hp, hr, hEnn]

theorem sq_lt_of_aggregate_second (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (_hr : 0 < r)
    (hgap : maxSurplus p q r * tripleEnergy u v w < p * q * r) :
    v ^ 2 < p * r := by
  have hMpos : 0 < maxSurplus p q r := maxSurplus_pos p q r hp
  have hqm : q ≤ maxSurplus p q r := le_maxSurplus_second p q r
  have hsq : v ^ 2 ≤ tripleEnergy u v w := sq_le_tripleEnergy_second u v w
  have hEnn : 0 ≤ tripleEnergy u v w := tripleEnergy_nonneg u v w
  nlinarith [hgap, hsq, hqm, hMpos, hp, hq, hEnn]

theorem sq_lt_of_aggregate_third (p q r u v w : ℝ)
    (hp : 0 < p) (_hq : 0 < q) (_hr : 0 < r)
    (hgap : maxSurplus p q r * tripleEnergy u v w < p * q * r) :
    w ^ 2 < q * r := by
  have hMpos : 0 < maxSurplus p q r := maxSurplus_pos p q r hp
  have hpm : p ≤ maxSurplus p q r := le_maxSurplus_first p q r
  have hsq : w ^ 2 ≤ tripleEnergy u v w := sq_le_tripleEnergy_third u v w
  have hEnn : 0 ≤ tripleEnergy u v w := tripleEnergy_nonneg u v w
  nlinarith [hgap, hsq, hpm, hMpos, hp, hEnn]

/-! ## 5. The cell at the atom level -/

/-- **THE AGGREGATE CELL ON THE TRIPLE GRAM.**  Three strictly heavy atoms whose
pairings carry small enough total energy give a strict dominator, with no
triangle hypothesis and no reading of the triple product's sign. -/
theorem tripleGram_posDef_of_aggregate (a b c : Fin 3 → ℝ)
    (ha : 1 < leverageOf a) (hb : 1 < leverageOf b) (hc : 1 < leverageOf c)
    (hgap : maxSurplus (leverageOf a - 1) (leverageOf b - 1) (leverageOf c - 1)
        * tripleEnergy (a ⬝ᵥ b) (a ⬝ᵥ c) (b ⬝ᵥ c)
      < (leverageOf a - 1) * (leverageOf b - 1) * (leverageOf c - 1))
    (hcross : 4 * tripleEnergy (a ⬝ᵥ b) (a ⬝ᵥ c) (b ⬝ᵥ c) ^ 3
      < 27 * ((leverageOf a - 1) * (leverageOf b - 1) * (leverageOf c - 1)
          - maxSurplus (leverageOf a - 1) (leverageOf b - 1) (leverageOf c - 1)
            * tripleEnergy (a ⬝ᵥ b) (a ⬝ᵥ c) (b ⬝ᵥ c)) ^ 2) :
    (tripleGram a b c - 1).PosDef := by
  have hp : 0 < leverageOf a - 1 := by linarith
  have hq : 0 < leverageOf b - 1 := by linarith
  have hr : 0 < leverageOf c - 1 := by linarith
  rw [tripleGram_posDef_iff_pairVocabulary]
  refine ⟨hp, ?_, ?_⟩
  · rw [pairGapMinor]
    have := sq_lt_of_aggregate_first (leverageOf a - 1) (leverageOf b - 1) (leverageOf c - 1)
      (a ⬝ᵥ b) (a ⬝ᵥ c) (b ⬝ᵥ c) hp hq hr hgap
    linarith
  · rw [tripleGapDet_eq_tripleDetForm]
    exact tripleDetForm_pos_of_aggregate _ _ _ _ _ _ hp hq hr hgap hcross

/-- **THE AGGREGATE CELL AT THE DESIGN LEVEL.**  The consumer form: a strict
dominator on three named labels. -/
theorem subsetSum_posDef_of_aggregate {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : 1 < leverageOf (D.atom x)) (hy : 1 < leverageOf (D.atom y))
    (hz : 1 < leverageOf (D.atom z))
    (hgap : maxSurplus (leverageOf (D.atom x) - 1) (leverageOf (D.atom y) - 1)
          (leverageOf (D.atom z) - 1)
        * tripleEnergy (D.atom x ⬝ᵥ D.atom y) (D.atom x ⬝ᵥ D.atom z) (D.atom y ⬝ᵥ D.atom z)
      < (leverageOf (D.atom x) - 1) * (leverageOf (D.atom y) - 1) * (leverageOf (D.atom z) - 1))
    (hcross : 4 * tripleEnergy (D.atom x ⬝ᵥ D.atom y) (D.atom x ⬝ᵥ D.atom z)
          (D.atom y ⬝ᵥ D.atom z) ^ 3
      < 27 * ((leverageOf (D.atom x) - 1) * (leverageOf (D.atom y) - 1)
            * (leverageOf (D.atom z) - 1)
          - maxSurplus (leverageOf (D.atom x) - 1) (leverageOf (D.atom y) - 1)
              (leverageOf (D.atom z) - 1)
            * tripleEnergy (D.atom x ⬝ᵥ D.atom y) (D.atom x ⬝ᵥ D.atom z)
              (D.atom y ⬝ᵥ D.atom z)) ^ 2) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef :=
  (subsetSum_posDef_iff_tripleGram D x y z hxy hxz hyz).mpr
    (tripleGram_posDef_of_aggregate _ _ _ hx hy hz hgap hcross)

/-! ## 6. The two cells are incomparable -/

/-- **QUARTER SLACK DOES NOT IMPLY THE AGGREGATE CONDITION.**  At surpluses
`(10, 1, 1)` and pairings `(1, 1, 0)` every quarter-slack inequality holds, the
maximum surplus is `10`, the triple energy is `2`, and `10 · 2 = 20` is already
larger than `10 · 1 · 1`.  So the aggregate gap hypothesis fails while quarter
slack holds, and neither cell contains the other. -/
theorem not_aggregate_of_quarterSlack_witness :
    (4 * (1 : ℝ) ^ 2 < 10 * 1 ∧ 4 * (1 : ℝ) ^ 2 < 10 * 1 ∧ 4 * (0 : ℝ) ^ 2 < 1 * 1)
      ∧ ¬ (maxSurplus (10 : ℝ) 1 1 * tripleEnergy 1 1 0 < 10 * 1 * 1) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ?_⟩
  rw [maxSurplus, tripleEnergy]
  norm_num

/-- **THE AGGREGATE CELL REACHES WHERE QUARTER SLACK CANNOT.**  At surpluses
`(1, 1, 1)` and pairings `(7/10, 0, 0)` the quarter-slack inequality `4 u² < p q`
fails by a factor near two, while both aggregate hypotheses hold.  The mechanism
is that quarter slack charges every pair its own quarter whether or not that pair
carries any energy, and the aggregate condition charges the total once. -/
theorem aggregate_beyond_quarterSlack_witness :
    ¬ (4 * ((7 : ℝ) / 10) ^ 2 < 1 * 1)
      ∧ maxSurplus (1 : ℝ) 1 1 * tripleEnergy (7/10) 0 0 < 1 * 1 * 1
      ∧ 4 * tripleEnergy ((7 : ℝ)/10) 0 0 ^ 3
        < 27 * (1 * 1 * 1 - maxSurplus (1 : ℝ) 1 1 * tripleEnergy (7/10) 0 0) ^ 2 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [maxSurplus, tripleEnergy]; norm_num
  · rw [maxSurplus, tripleEnergy]; norm_num

/-- The witness above really does give a positive minor, at either sign. -/
theorem tripleDetForm_pos_at_beyond_witness :
    0 < tripleDetForm (1 : ℝ) 1 1 (7/10) 0 0 := by
  rw [tripleDetForm]; norm_num

/-- On the equilateral locus the two cells meet exactly at the quarter-slack
constant: at `p = q = r = 1` and `u = v = w = 1/2` the aggregate cross condition
holds with equality, which is the same boundary the equilateral factorization
`(P − 2t)(P + t)²` reports. -/
theorem aggregate_meets_quarterSlack_on_equilateral :
    4 * tripleEnergy ((1 : ℝ)/2) (1/2) (1/2) ^ 3
      = 27 * (1 * 1 * 1 - maxSurplus (1 : ℝ) 1 1 * tripleEnergy (1/2) (1/2) (1/2)) ^ 2 := by
  rw [maxSurplus, tripleEnergy]; norm_num

/-! ## 7. The projection-side budget for the triple energy -/

/-- The **coupling** of a label: the off-diagonal energy of its projection row,
which `Gtz.sum_erase_sq_projectionRow` computes as `t_c (1 − t_c)`. -/
noncomputable def couplingOf (design : WeightedDesign size rank) (rowIndex : Fin size) : ℝ :=
  projectionOfDesign design rowIndex rowIndex * (1 - projectionOfDesign design rowIndex rowIndex)

theorem couplingOf_nonneg (design : WeightedDesign size rank) (rowIndex : Fin size) :
    0 ≤ couplingOf design rowIndex := by
  rw [couplingOf]
  have hlo := projectionOfDesign_diagonal_nonneg design rowIndex
  have hhi := projectionDiagonal_le_one' design rowIndex
  nlinarith

theorem couplingOf_le_quarter (design : WeightedDesign size rank) (rowIndex : Fin size) :
    couplingOf design rowIndex ≤ 1 / 4 := by
  rw [couplingOf]
  nlinarith [sq_nonneg (projectionOfDesign design rowIndex rowIndex - 1 / 2)]

theorem sum_erase_sq_projectionRow_eq_couplingOf (design : WeightedDesign size rank)
    (rowIndex : Fin size) :
    ∑ colIndex ∈ Finset.univ.erase rowIndex, projectionOfDesign design rowIndex colIndex ^ 2
      = couplingOf design rowIndex := by
  rw [couplingOf]
  exact sum_erase_sq_projectionRow design rowIndex

/-- **A SINGLE PAIRING SQUARE IS CAPPED BY EITHER ENDPOINT'S COUPLING.**  One
term of a nonnegative sum never exceeds the sum. -/
theorem sq_projectionOffDiag_le_coupling (design : WeightedDesign size rank)
    {rowIndex colIndex : Fin size} (hne : rowIndex ≠ colIndex) :
    projectionOfDesign design rowIndex colIndex ^ 2 ≤ couplingOf design rowIndex := by
  classical
  rw [← sum_erase_sq_projectionRow_eq_couplingOf design rowIndex]
  refine Finset.single_le_sum (f := fun colIdx => projectionOfDesign design rowIndex colIdx ^ 2)
    (fun colIdx _ => sq_nonneg _) ?_
  exact Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ colIndex⟩

/-- **THE SUBSET ROW BUDGET.**  Restricting each projection row's off-diagonal
sum to a subset and adding over that subset gives a budget on the whole subset's
off-diagonal energy, read off the diagonal alone.  Generic in size and rank. -/
theorem sum_sq_offDiag_subset_le_sum_coupling (design : WeightedDesign size rank)
    (chosen : Finset (Fin size)) :
    ∑ rowIndex ∈ chosen, ∑ colIndex ∈ chosen.erase rowIndex,
        projectionOfDesign design rowIndex colIndex ^ 2
      ≤ ∑ rowIndex ∈ chosen, couplingOf design rowIndex := by
  classical
  refine Finset.sum_le_sum fun rowIndex _ => ?_
  rw [← sum_erase_sq_projectionRow_eq_couplingOf design rowIndex]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun colIdx _ _ => sq_nonneg _)
  intro colIdx hmem
  rw [Finset.mem_erase] at hmem ⊢
  exact ⟨hmem.1, Finset.mem_univ colIdx⟩

/-- The triple energy of three labels, in the projection chart. -/
noncomputable def tripleEnergyAt (design : WeightedDesign size rank) (x y z : Fin size) : ℝ :=
  tripleEnergy (projectionOfDesign design x y) (projectionOfDesign design x z)
    (projectionOfDesign design y z)

/-- **THE TRIPLE ENERGY IS HALF THE THREE COUPLINGS AT MOST.**  Each label's two
in-triple pairings are two terms of that label's row budget, so adding the three
row budgets counts every pairing twice. -/
theorem two_mul_tripleEnergyAt_le (design : WeightedDesign size rank)
    {x y z : Fin size} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    2 * tripleEnergyAt design x y z
      ≤ couplingOf design x + couplingOf design y + couplingOf design z := by
  classical
  have hsym := projectionOfDesign_transpose design
  have hyx : projectionOfDesign design y x = projectionOfDesign design x y := by
    have hstep := congrArg (fun mat => mat y x) hsym
    simp only [Matrix.transpose_apply] at hstep
    exact hstep.symm
  have hzx : projectionOfDesign design z x = projectionOfDesign design x z := by
    have hstep := congrArg (fun mat => mat z x) hsym
    simp only [Matrix.transpose_apply] at hstep
    exact hstep.symm
  have hzy : projectionOfDesign design z y = projectionOfDesign design y z := by
    have hstep := congrArg (fun mat => mat z y) hsym
    simp only [Matrix.transpose_apply] at hstep
    exact hstep.symm
  -- each row contributes its two in-triple pairings
  have hrowx : projectionOfDesign design x y ^ 2 + projectionOfDesign design x z ^ 2
      ≤ couplingOf design x := by
    rw [← sum_erase_sq_projectionRow_eq_couplingOf design x]
    have hsub : ({y, z} : Finset (Fin size)) ⊆ Finset.univ.erase x := by
      intro idx hidx
      rw [Finset.mem_insert, Finset.mem_singleton] at hidx
      rcases hidx with rfl | rfl
      · exact Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ _⟩
      · exact Finset.mem_erase.mpr ⟨hxz.symm, Finset.mem_univ _⟩
    have hpair : ∑ colIdx ∈ ({y, z} : Finset (Fin size)),
        projectionOfDesign design x colIdx ^ 2
        = projectionOfDesign design x y ^ 2 + projectionOfDesign design x z ^ 2 := by
      rw [Finset.sum_insert (by simpa using hyz), Finset.sum_singleton]
    rw [← hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun colIdx _ _ => sq_nonneg _)
  have hrowy : projectionOfDesign design x y ^ 2 + projectionOfDesign design y z ^ 2
      ≤ couplingOf design y := by
    rw [← sum_erase_sq_projectionRow_eq_couplingOf design y]
    have hsub : ({x, z} : Finset (Fin size)) ⊆ Finset.univ.erase y := by
      intro idx hidx
      rw [Finset.mem_insert, Finset.mem_singleton] at hidx
      rcases hidx with rfl | rfl
      · exact Finset.mem_erase.mpr ⟨hxy, Finset.mem_univ _⟩
      · exact Finset.mem_erase.mpr ⟨hyz.symm, Finset.mem_univ _⟩
    have hpair : ∑ colIdx ∈ ({x, z} : Finset (Fin size)),
        projectionOfDesign design y colIdx ^ 2
        = projectionOfDesign design x y ^ 2 + projectionOfDesign design y z ^ 2 := by
      rw [Finset.sum_insert (by simpa using hxz), Finset.sum_singleton, hyx]
    rw [← hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun colIdx _ _ => sq_nonneg _)
  have hrowz : projectionOfDesign design x z ^ 2 + projectionOfDesign design y z ^ 2
      ≤ couplingOf design z := by
    rw [← sum_erase_sq_projectionRow_eq_couplingOf design z]
    have hsub : ({x, y} : Finset (Fin size)) ⊆ Finset.univ.erase z := by
      intro idx hidx
      rw [Finset.mem_insert, Finset.mem_singleton] at hidx
      rcases hidx with rfl | rfl
      · exact Finset.mem_erase.mpr ⟨hxz, Finset.mem_univ _⟩
      · exact Finset.mem_erase.mpr ⟨hyz, Finset.mem_univ _⟩
    have hpair : ∑ colIdx ∈ ({x, y} : Finset (Fin size)),
        projectionOfDesign design z colIdx ^ 2
        = projectionOfDesign design z x ^ 2 + projectionOfDesign design z y ^ 2 := by
      rw [Finset.sum_insert (by simpa using hxy), Finset.sum_singleton]
    rw [hzx, hzy] at hpair
    rw [← hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun colIdx _ _ => sq_nonneg _)
  rw [tripleEnergyAt, tripleEnergy]
  linarith

/-- The triple energy never exceeds three quarters, since each coupling is capped
at a quarter. -/
theorem tripleEnergyAt_le_three_eighths (design : WeightedDesign size rank)
    {x y z : Fin size} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    tripleEnergyAt design x y z ≤ 3 / 8 := by
  have hbudget := two_mul_tripleEnergyAt_le design hxy hxz hyz
  have hx := couplingOf_le_quarter design x
  have hy := couplingOf_le_quarter design y
  have hz := couplingOf_le_quarter design z
  linarith

/-! ## 8. The pigeonhole inside a four-set -/

/-- **THE FOUR-SET DOUBLE COUNT.**  Removing a label from a four-set removes its
two in-set pairings from both sides of the count, so the four triples' energies
total exactly the four-set's own off-diagonal energy.  A label whose in-set
energy is at least the average therefore leaves a triple of at most half the
four-set energy. -/
theorem exists_label_in_set_energy_ge_average (design : WeightedDesign size rank)
    (chosen : Finset (Fin size)) (hne : chosen.Nonempty) :
    ∃ dropLabel ∈ chosen,
      (∑ rowIndex ∈ chosen, ∑ colIndex ∈ chosen.erase rowIndex,
          projectionOfDesign design rowIndex colIndex ^ 2)
        ≤ (chosen.card : ℝ)
          * ∑ colIndex ∈ chosen.erase dropLabel,
              projectionOfDesign design dropLabel colIndex ^ 2 := by
  classical
  obtain ⟨dropLabel, hmem, hmax⟩ :=
    chosen.exists_max_image
      (fun rowIndex => ∑ colIndex ∈ chosen.erase rowIndex,
        projectionOfDesign design rowIndex colIndex ^ 2) hne
  refine ⟨dropLabel, hmem, ?_⟩
  calc (∑ rowIndex ∈ chosen, ∑ colIndex ∈ chosen.erase rowIndex,
          projectionOfDesign design rowIndex colIndex ^ 2)
      ≤ ∑ _rowIndex ∈ chosen, ∑ colIndex ∈ chosen.erase dropLabel,
          projectionOfDesign design dropLabel colIndex ^ 2 :=
        Finset.sum_le_sum fun rowIndex hrow => hmax rowIndex hrow
    _ = (chosen.card : ℝ)
          * ∑ colIndex ∈ chosen.erase dropLabel,
              projectionOfDesign design dropLabel colIndex ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **THE PIGEONHOLE CELL IS WEAK, AND THIS IS WHY.**  Bounding one pairing
square by the whole triple energy costs a factor three against bounding it by its
own row, so the resulting existence cell needs a surplus product larger than any
surplus product available at `(6,3)`, where every surplus is strictly below one.
The census found it fires at one hundredth of a percent of canonical points. -/
theorem tripleEnergy_bound_is_lossy (u v w : ℝ) :
    u ^ 2 ≤ tripleEnergy u v w ∧ tripleEnergy u v w ≤ 3 * max (u ^ 2) (max (v ^ 2) (w ^ 2)) := by
  refine ⟨sq_le_tripleEnergy_first u v w, ?_⟩
  have h1 : u ^ 2 ≤ max (u ^ 2) (max (v ^ 2) (w ^ 2)) := le_max_left _ _
  have h2 : v ^ 2 ≤ max (u ^ 2) (max (v ^ 2) (w ^ 2)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have h3 : w ^ 2 ≤ max (u ^ 2) (max (v ^ 2) (w ^ 2)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  rw [tripleEnergy]
  linarith

/-! ## 9. The heavy-set consumer form -/

/-- **THE AGGREGATE CELL FIRES INSIDE THE HEAVY SET.**  Every strict dominator
lies in the heavy set (`Gtz.subset_heavyLabels_of_posDef`), so a cell only ever
has to be tested there.  This is the existence form the consumer wants. -/
def AggregateCellFiresOnHeavy (design : WeightedDesign size 3) : Prop :=
  ∃ x ∈ heavyLabels design, ∃ y ∈ heavyLabels design, ∃ z ∈ heavyLabels design,
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      maxSurplus (leverageOf (design.atom x) - 1) (leverageOf (design.atom y) - 1)
          (leverageOf (design.atom z) - 1)
        * tripleEnergy (design.atom x ⬝ᵥ design.atom y) (design.atom x ⬝ᵥ design.atom z)
            (design.atom y ⬝ᵥ design.atom z)
      < (leverageOf (design.atom x) - 1) * (leverageOf (design.atom y) - 1)
          * (leverageOf (design.atom z) - 1) ∧
      4 * tripleEnergy (design.atom x ⬝ᵥ design.atom y) (design.atom x ⬝ᵥ design.atom z)
            (design.atom y ⬝ᵥ design.atom z) ^ 3
        < 27 * ((leverageOf (design.atom x) - 1) * (leverageOf (design.atom y) - 1)
              * (leverageOf (design.atom z) - 1)
            - maxSurplus (leverageOf (design.atom x) - 1) (leverageOf (design.atom y) - 1)
                (leverageOf (design.atom z) - 1)
              * tripleEnergy (design.atom x ⬝ᵥ design.atom y) (design.atom x ⬝ᵥ design.atom z)
                  (design.atom y ⬝ᵥ design.atom z)) ^ 2

/-- **THE CONSUMER BRIDGE.**  A firing of the aggregate cell inside the heavy set
produces the existential the projection block statement asks for. -/
theorem exists_posDef_of_aggregateCellFiresOnHeavy {size : ℕ} (design : WeightedDesign size 3)
    (hfires : AggregateCellFiresOnHeavy design) :
    ∃ selected : Finset (Fin size), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef := by
  classical
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hgap, hcross⟩ := hfires
  refine ⟨({x, y, z} : Finset (Fin size)), ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hyz
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact not_or.mpr ⟨hxy, hxz⟩
  · exact subsetSum_posDef_of_aggregate design x y z hxy hxz hyz
      ((mem_heavyLabels_iff_one_lt_leverage design x).mp hx)
      ((mem_heavyLabels_iff_one_lt_leverage design y).mp hy)
      ((mem_heavyLabels_iff_one_lt_leverage design z).mp hz) hgap hcross

/-- The heavy set carries at least three labels at rank three, so the aggregate
cell always has a triple to be tested on. -/
theorem three_le_card_heavyLabels_rankThree (design : WeightedDesign size 3) :
    3 ≤ (heavyLabels design).card :=
  rank_le_card_heavyLabels design (by norm_num)

/-! ## 10. The global energy law -/

/-- **THE TOTAL OFF-DIAGONAL ENERGY, EXACTLY.**  Adding the row law over every
label turns a statement about the off-diagonal into one about the diagonal: the
chart's whole off-diagonal energy is the rank minus the diagonal's square sum.
Idempotence enters through the row law and the trace identity, and nothing else
is used. -/
theorem sum_offDiag_sq_projection_eq (design : WeightedDesign size rank) :
    ∑ rowIndex : Fin size, ∑ colIndex ∈ Finset.univ.erase rowIndex,
        projectionOfDesign design rowIndex colIndex ^ 2
      = (rank : ℝ) - ∑ rowIndex : Fin size, projectionOfDesign design rowIndex rowIndex ^ 2 := by
  classical
  have hrow : ∀ rowIndex : Fin size,
      ∑ colIndex ∈ Finset.univ.erase rowIndex,
          projectionOfDesign design rowIndex colIndex ^ 2
        = projectionOfDesign design rowIndex rowIndex
          - projectionOfDesign design rowIndex rowIndex ^ 2 := by
    intro rowIndex
    rw [sum_erase_sq_projectionRow design rowIndex]
    ring
  rw [Finset.sum_congr rfl fun rowIndex _ => hrow rowIndex, Finset.sum_sub_distrib,
    sum_projectionDiagonal design]

/-- The diagonal square sum never falls below the flat value.  This is the
variance step, written without any inner-product machinery: the sum of squared
deviations from the mean is nonnegative. -/
theorem sq_rank_div_card_le_sum_sq_projectionDiagonal (design : WeightedDesign size rank)
    (hsize : 0 < size) :
    (rank : ℝ) ^ 2 / (size : ℝ)
      ≤ ∑ rowIndex : Fin size, projectionOfDesign design rowIndex rowIndex ^ 2 := by
  classical
  have hsizeR : (0 : ℝ) < (size : ℝ) := by exact_mod_cast hsize
  set flat : ℝ := (rank : ℝ) / (size : ℝ) with hflat
  have hcard : (Finset.univ : Finset (Fin size)).card = size := by simp
  have hnn : (0 : ℝ)
      ≤ ∑ rowIndex : Fin size, (projectionOfDesign design rowIndex rowIndex - flat) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpoint : ∀ rowIndex : Fin size,
      (projectionOfDesign design rowIndex rowIndex - flat) ^ 2
        = projectionOfDesign design rowIndex rowIndex ^ 2
          - 2 * flat * projectionOfDesign design rowIndex rowIndex + flat ^ 2 :=
    fun rowIndex => by ring
  rw [Finset.sum_congr rfl fun rowIndex _ => hpoint rowIndex, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul,
    sum_projectionDiagonal design] at hnn
  rw [hflat] at hnn
  field_simp at hnn ⊢
  nlinarith [hnn, hsizeR]

/-- **THE GLOBAL ENERGY CAP.**  The chart's total off-diagonal energy is at most
`rank − rank²/size`.  At `(6,3)` that is `3 − 3/2 = 3/2`, so the fifteen unordered
pairings carry at most three quarters of squared coupling between them. -/
theorem sum_offDiag_sq_projection_le (design : WeightedDesign size rank) (hsize : 0 < size) :
    ∑ rowIndex : Fin size, ∑ colIndex ∈ Finset.univ.erase rowIndex,
        projectionOfDesign design rowIndex colIndex ^ 2
      ≤ (rank : ℝ) - (rank : ℝ) ^ 2 / (size : ℝ) := by
  rw [sum_offDiag_sq_projection_eq design]
  have := sq_rank_div_card_le_sum_sq_projectionDiagonal design hsize
  linarith

/-- **THE CAP IS ATTAINED EXACTLY AT THE FLAT PROFILE.**  Equality in the global
energy cap forces every leverage diagonal to the flat value `rank/size`.  At
`(6,3)` that value is one half, which is the equiangular profile — so the total
coupling is largest exactly where every sign-blind certificate is known to fail. -/
theorem sum_offDiag_sq_projection_eq_iff_flat (design : WeightedDesign size rank)
    (hsize : 0 < size)
    (hattained : ∑ rowIndex : Fin size, ∑ colIndex ∈ Finset.univ.erase rowIndex,
        projectionOfDesign design rowIndex colIndex ^ 2
      = (rank : ℝ) - (rank : ℝ) ^ 2 / (size : ℝ)) :
    ∀ rowIndex : Fin size,
      projectionOfDesign design rowIndex rowIndex = (rank : ℝ) / (size : ℝ) := by
  classical
  have hsizeR : (0 : ℝ) < (size : ℝ) := by exact_mod_cast hsize
  set flat : ℝ := (rank : ℝ) / (size : ℝ) with hflat
  have hcard : (Finset.univ : Finset (Fin size)).card = size := by simp
  rw [sum_offDiag_sq_projection_eq design] at hattained
  have hsq : ∑ rowIndex : Fin size, projectionOfDesign design rowIndex rowIndex ^ 2
      = (rank : ℝ) ^ 2 / (size : ℝ) := by linarith
  have hpoint : ∀ rowIndex : Fin size,
      (projectionOfDesign design rowIndex rowIndex - flat) ^ 2
        = projectionOfDesign design rowIndex rowIndex ^ 2
          - 2 * flat * projectionOfDesign design rowIndex rowIndex + flat ^ 2 :=
    fun rowIndex => by ring
  have hzero : ∑ rowIndex : Fin size,
      (projectionOfDesign design rowIndex rowIndex - flat) ^ 2 = 0 := by
    rw [Finset.sum_congr rfl fun rowIndex _ => hpoint rowIndex, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul,
      sum_projectionDiagonal design, hsq, hflat]
    field_simp
    ring
  intro rowIndex
  have hterm : (projectionOfDesign design rowIndex rowIndex - flat) ^ 2 = 0 := by
    by_contra hne
    have hpos : 0 < (projectionOfDesign design rowIndex rowIndex - flat) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
    have hother : 0 ≤ ∑ other ∈ Finset.univ.erase rowIndex,
        (projectionOfDesign design other other - flat) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun other : Fin size => (projectionOfDesign design other other - flat) ^ 2)
      (Finset.mem_univ rowIndex)
    rw [hzero] at hsplit
    linarith
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hterm
  linarith [this]

/-! ## 11. The coupling is capped by the surplus -/

/-- **A LABEL'S COUPLING IS CAPPED BY ONE MINUS ITS SURPLUS.**  A heavy label is
therefore weakly coupled, and the heavier it is the weaker its coupling.  The two
steps are that the diagonal never exceeds one and that the surplus never exceeds
the diagonal, the second because every weight is strictly positive. -/
theorem couplingOf_le_one_sub_surplus (design : WeightedDesign size rank) (rowIndex : Fin size) :
    couplingOf design rowIndex
      ≤ 1 - (projectionOfDesign design rowIndex rowIndex - design.weight rowIndex) := by
  rw [couplingOf]
  have hlo := projectionOfDesign_diagonal_nonneg design rowIndex
  have hhi := projectionDiagonal_le_one' design rowIndex
  have hw := design.weight_pos rowIndex
  nlinarith

/-- The triple energy is capped by the three surpluses, read off the diagonal
alone.  Combined with `Gtz.two_mul_tripleEnergyAt_le` this bounds the one
quantity the aggregate cell reads without touching a single pairing. -/
theorem two_mul_tripleEnergyAt_le_three_sub_surplus (design : WeightedDesign size rank)
    {x y z : Fin size} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    2 * tripleEnergyAt design x y z
      ≤ 3 - ((projectionOfDesign design x x - design.weight x)
          + (projectionOfDesign design y y - design.weight y)
          + (projectionOfDesign design z z - design.weight z)) := by
  have hbudget := two_mul_tripleEnergyAt_le design hxy hxz hyz
  have hx := couplingOf_le_one_sub_surplus design x
  have hy := couplingOf_le_one_sub_surplus design y
  have hz := couplingOf_le_one_sub_surplus design z
  linarith

/-! ## 12. Counting the strongly coupled partners -/

/-- The partners of a label whose pairing square reaches a threshold. -/
noncomputable def strongPartners (design : WeightedDesign size rank) (rowIndex : Fin size)
    (threshold : ℝ) : Finset (Fin size) :=
  (Finset.univ.erase rowIndex).filter
    fun colIndex => threshold ≤ projectionOfDesign design rowIndex colIndex ^ 2

/-- **EVERY LABEL HAS FEW STRONG PARTNERS.**  The row budget is a fixed quantity,
so the number of partners carrying at least a given share of it is bounded by the
ratio.  With the universal quarter cap on the coupling, a label has at most
`1/(4 τ)` partners above `τ`. -/
theorem card_strongPartners_mul_le_coupling (design : WeightedDesign size rank)
    (rowIndex : Fin size) {threshold : ℝ} :
    ((strongPartners design rowIndex threshold).card : ℝ) * threshold
      ≤ couplingOf design rowIndex := by
  classical
  have hmem : ∀ colIndex ∈ strongPartners design rowIndex threshold,
      threshold ≤ projectionOfDesign design rowIndex colIndex ^ 2 := by
    intro colIndex hcol
    rw [strongPartners, Finset.mem_filter] at hcol
    exact hcol.2
  have hsubset : strongPartners design rowIndex threshold ⊆ Finset.univ.erase rowIndex := by
    intro colIndex hcol
    rw [strongPartners, Finset.mem_filter] at hcol
    exact hcol.1
  have hlower : ((strongPartners design rowIndex threshold).card : ℝ) * threshold
      ≤ ∑ colIndex ∈ strongPartners design rowIndex threshold,
          projectionOfDesign design rowIndex colIndex ^ 2 := by
    rw [mul_comm]
    calc threshold * ((strongPartners design rowIndex threshold).card : ℝ)
        = ∑ _colIndex ∈ strongPartners design rowIndex threshold, threshold := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ colIndex ∈ strongPartners design rowIndex threshold,
            projectionOfDesign design rowIndex colIndex ^ 2 :=
          Finset.sum_le_sum hmem
  have hupper : ∑ colIndex ∈ strongPartners design rowIndex threshold,
      projectionOfDesign design rowIndex colIndex ^ 2 ≤ couplingOf design rowIndex := by
    rw [← sum_erase_sq_projectionRow_eq_couplingOf design rowIndex]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun colIndex _ _ => sq_nonneg _)
  linarith

/-- The quarter cap turns the partner count into an absolute bound. -/
theorem card_strongPartners_mul_le_quarter (design : WeightedDesign size rank)
    (rowIndex : Fin size) {threshold : ℝ} :
    ((strongPartners design rowIndex threshold).card : ℝ) * threshold ≤ 1 / 4 :=
  le_trans (card_strongPartners_mul_le_coupling design rowIndex)
    (couplingOf_le_quarter design rowIndex)

/-- **AT MOST THREE PARTNERS PASS ONE SIXTEENTH.**  A label of six has five
partners, and the quarter cap leaves at most four of them above `1/16`.  The
count is one place the ambient size and the rank both enter. -/
theorem card_strongPartners_le_four (design : WeightedDesign size rank)
    (rowIndex : Fin size) :
    ((strongPartners design rowIndex (1 / 16)).card : ℝ) ≤ 4 := by
  have hbound := card_strongPartners_mul_le_quarter design rowIndex (threshold := 1 / 16)
  linarith

end Gtz

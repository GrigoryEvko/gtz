/-
# Diagonal dominance at the projection, and a leverage cell for classical GTZ

`Gtz.gtzOriginal_iff_frameProjectionCovering` proves that classical GTZ IS the
statement `Gtz.FrameProjectionCovering`: for a frame `A` with `Aᵀ A = 1`, some
`k`-subset of rows makes the principal block of `A Aᵀ` dominate `(1/n) • 1`.
Every route to that domination in the corpus expands leading minors of the
block.

This file supplies a determinant-free route and then removes the off-diagonal
data entirely.

## PROVED here, kernel-checked, unconditional

* `Gtz.posDef_of_diagonallyDominant` — **a general lemma the corpus lacked.**  A
  real symmetric matrix whose every diagonal entry beats the absolute sum of its
  own row off the diagonal is positive definite.  Generic in the dimension, with
  no idempotence, no rank and no cardinality hypothesis.
* `Gtz.projection_offDiag_sq_energy` — the landed row law
  `Gtz.projection_row_energy` written with squares rather than products.  The row
  law itself is NOT reproved here: the corpus already carries it.
* `Gtz.projectionCovering_of_rowDominance` — the dominance cell for the covering
  statement, stated on the intrinsic projection.
* `Gtz.sq_absOffRow_le_card_mul_energy` and
  `Gtz.projectionCovering_of_leverageBudget` — **THE LEVERAGE BUDGET.**  A
  `k`-subset witnesses the covering as soon as every chosen row satisfies

    `(k - 1) * P a a * (1 - P a a) < (P a a - 1 / n) ^ 2`,

  which names only the diagonal of the projection.  No off-diagonal entry and no
  determinant appear.
* `Gtz.projectionCovering_sixThree_of_sevenNinths` — the rank-three reading.  At
  `n = 6` and `k = 3` the budget closes at leverage `7 / 9`, exactly: the
  quadratic `108 d ^ 2 - 84 d + 1` takes the value `1` there.

## What the budget says, and what it does not

The budget is one-sided.  It certifies a covering and never refutes one.  Its
threshold is a genuine cell boundary rather than an artifact: at `n = 6` and
`k = 3` the quadratic has roots near `0.0121` and `0.7657`, and the diagonal of
a rank-three projection on six rows is at least... nothing in general, but a row
useful to the covering must already exceed `1 / 6`, which is above the lower
root.  So only the upper branch is reachable and `7 / 9` is the first round
number past it.

Since `∑_a P a a = k`, three rows of leverage `7 / 9` cost `7 / 3` of the total
`3`, leaving `2 / 3` for the other three rows.  The cell is therefore a real
region and not a vacuous one, and it is exactly the regime where the frame is
close to a partition of the coordinates.
-/
import Gtz.LinAlg.ProjectionForm
import Gtz.Wave.SharedPrivateCircuitSaturation

namespace Gtz

open Finset Matrix

/-! ## The general lemma -/

/-- **Diagonal dominance implies positive definiteness.**  The proof is a
completion of squares: off the diagonal the term `M a b * x a * x b` is at least
`- |M a b| * ((x a) ^ 2 + (x b) ^ 2) / 2`, and summing that bound along rows and
along columns — which agree, because the matrix is symmetric — leaves exactly
the row margins. -/
theorem sum_ite_zero_eq_sum_erase {rank : ℕ} (f : Fin rank → ℝ) (a : Fin rank) :
    ∑ b, (if b = a then 0 else f b) = ∑ b ∈ Finset.univ.erase a, f b := by
  classical
  rw [← Finset.sum_erase_add Finset.univ (fun b => if b = a then 0 else f b)
    (Finset.mem_univ a)]
  have hlast : (if a = a then (0 : ℝ) else f a) = 0 := if_pos rfl
  rw [hlast, add_zero]
  exact Finset.sum_congr rfl fun b hb => by rw [if_neg (Finset.mem_erase.mp hb).1]

/-- **Diagonal dominance implies positive definiteness.** -/
theorem posDef_of_diagonallyDominant {rank : ℕ} (mat : Matrix (Fin rank) (Fin rank) ℝ)
    (hsymm : matᵀ = mat)
    (hdom : ∀ a : Fin rank, ∑ b ∈ Finset.univ.erase a, |mat a b| < mat a a) :
    mat.PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobe => ?_⟩
  rw [star_trivial]
  have hentry : ∀ a b : Fin rank, mat a b = mat b a := fun a b =>
    congrFun (congrFun hsymm b) a
  -- The quadratic form as a double sum.
  have hform : probe ⬝ᵥ (mat *ᵥ probe)
      = ∑ a, ∑ b, mat a b * probe a * probe b := by
    show ∑ a, probe a * (mat *ᵥ probe) a = _
    refine Finset.sum_congr rfl fun a _ => ?_
    show probe a * ∑ b, mat a b * probe b = _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  -- The off-diagonal minorant, row by row.
  have hrowBound : ∀ a : Fin rank,
      mat a a * probe a ^ 2
          - (∑ b ∈ Finset.univ.erase a, |mat a b| * probe a ^ 2) / 2
          - (∑ b ∈ Finset.univ.erase a, |mat a b| * probe b ^ 2) / 2
        ≤ ∑ b, mat a b * probe a * probe b := by
    intro a
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ a)]
    have hdiag : mat a a * probe a * probe a = mat a a * probe a ^ 2 := by ring
    rw [hdiag]
    have hmerge : (∑ b ∈ Finset.univ.erase a, |mat a b| * probe a ^ 2) / 2
          + (∑ b ∈ Finset.univ.erase a, |mat a b| * probe b ^ 2) / 2
        = ∑ b ∈ Finset.univ.erase a, |mat a b| * (probe a ^ 2 + probe b ^ 2) / 2 := by
      rw [← add_div, ← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun b _ => by ring
    have hoff : - ∑ b ∈ Finset.univ.erase a, |mat a b| * (probe a ^ 2 + probe b ^ 2) / 2
        ≤ ∑ b ∈ Finset.univ.erase a, mat a b * probe a * probe b := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun b _ => ?_
      have hsq : |probe a| * |probe b| ≤ (probe a ^ 2 + probe b ^ 2) / 2 := by
        nlinarith [sq_nonneg (|probe a| - |probe b|), sq_abs (probe a), sq_abs (probe b)]
      have habs : |mat a b * probe a * probe b|
          ≤ |mat a b| * (probe a ^ 2 + probe b ^ 2) / 2 := by
        rw [abs_mul, abs_mul]
        nlinarith [abs_nonneg (mat a b), hsq, abs_nonneg (probe a), abs_nonneg (probe b)]
      linarith [neg_abs_le (mat a b * probe a * probe b)]
    linarith
  -- The column half of the off-diagonal weight equals the row half.
  have hcolumn : ∑ a, (∑ b ∈ Finset.univ.erase a, |mat a b| * probe b ^ 2)
      = ∑ a, probe a ^ 2 * ∑ b ∈ Finset.univ.erase a, |mat a b| := by
    simp only [← sum_ite_zero_eq_sum_erase]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hab : a = b
    · simp [hab]
    · have hba : b ≠ a := fun h => hab h.symm
      rw [if_neg hab, if_neg hba, hentry a b]
      ring
  have hrowSum : ∑ a, (∑ b ∈ Finset.univ.erase a, |mat a b| * probe a ^ 2)
      = ∑ a, probe a ^ 2 * ∑ b ∈ Finset.univ.erase a, |mat a b| :=
    Finset.sum_congr rfl fun a _ => by rw [← Finset.sum_mul]; ring
  -- Assemble.
  have hminor : ∑ a, probe a ^ 2
        * (mat a a - ∑ b ∈ Finset.univ.erase a, |mat a b|)
      ≤ probe ⬝ᵥ (mat *ᵥ probe) := by
    rw [hform]
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun a _ => hrowBound a)
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
      hrowSum, hcolumn]
    have harith : ∀ X Y : ℝ, X - Y / 2 - Y / 2 = X - Y := fun X Y => by ring
    rw [harith, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  -- Some coordinate is nonzero, and every summand is nonnegative.
  obtain ⟨label, hlabel⟩ : ∃ label : Fin rank, probe label ≠ 0 := by
    by_contra hall
    exact hprobe (funext fun label => not_not.mp (fun h => hall ⟨label, h⟩))
  refine lt_of_lt_of_le ?_ hminor
  refine Finset.sum_pos' (fun a _ => mul_nonneg (sq_nonneg _)
    (sub_nonneg.mpr (hdom a).le)) ⟨label, Finset.mem_univ label, ?_⟩
  exact mul_pos (by positivity) (sub_pos.mpr (hdom label))

/-! ## The row law of a projection

The corpus already proves the row law as `Gtz.projection_row_energy`, in the
off-diagonal form and with products rather than squares.  Only the change of
notation is done here.
-/

/-- **The landed row law, written with squares.**  The off-diagonal energy of a
row of a symmetric idempotent is the diagonal entry times its own defect. -/
theorem projection_offDiag_sq_energy {size : ℕ} {proj : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : projᵀ = proj) (hidem : proj * proj = proj) (a : Fin size) :
    ∑ b ∈ Finset.univ.erase a, proj a b ^ 2 = proj a a * (1 - proj a a) := by
  rw [← projection_row_energy hsymm hidem a]
  exact Finset.sum_congr rfl fun b _ => sq (proj a b) ▸ rfl

/-! ## The dominance cell for the covering statement -/

/-- **The covering from row dominance.**  A `k`-subset of rows whose block is
diagonally dominant against the shift `1 / n` witnesses the covering.  The block
is `PosDef`, which is stronger than the `PosSemidef` the statement asks for. -/
theorem projectionCovering_of_rowDominance {size rank : ℕ}
    (proj : Matrix (Fin size) (Fin size) ℝ) (hsymm : projᵀ = proj)
    (rowPick : Fin rank → Fin size) (_hinj : Function.Injective rowPick)
    (hdom : ∀ a : Fin rank,
      ∑ b ∈ Finset.univ.erase a, |proj (rowPick a) (rowPick b)|
        < proj (rowPick a) (rowPick a) - (size : ℝ)⁻¹) :
    (proj.submatrix rowPick rowPick - (size : ℝ)⁻¹ • 1).PosSemidef := by
  classical
  refine (posDef_of_diagonallyDominant _ ?_ ?_).posSemidef
  · ext a b
    simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.submatrix_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    have hentry : proj (rowPick b) (rowPick a) = proj (rowPick a) (rowPick b) :=
      congrFun (congrFun hsymm (rowPick a)) (rowPick b)
    rw [hentry]
    by_cases hab : a = b
    · simp [hab]
    · have hba : b ≠ a := fun h => hab h.symm
      simp [hab, hba]
  · intro a
    have hoff : ∀ b ∈ Finset.univ.erase a,
        |(proj.submatrix rowPick rowPick - (size : ℝ)⁻¹ • 1) a b|
          = |proj (rowPick a) (rowPick b)| := by
      intro b hb
      have hba : ¬ a = b := fun h => (Finset.mem_erase.mp hb).1 h.symm
      simp [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply, hba]
    rw [Finset.sum_congr rfl hoff]
    have hdiag : (proj.submatrix rowPick rowPick - (size : ℝ)⁻¹ • 1) a a
        = proj (rowPick a) (rowPick a) - (size : ℝ)⁻¹ := by
      simp [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply]
    rw [hdiag]
    exact hdom a

/-! ## The leverage budget

Cauchy–Schwarz against the constant one turns the absolute off-diagonal row into
the off-diagonal energy, and the row law of a projection names that energy by the
diagonal entry alone.
-/

/-- **Cauchy–Schwarz on the absolute off-diagonal row of the picked block.** -/
theorem sq_absOffRow_le_card_mul_energy {size rank : ℕ}
    (proj : Matrix (Fin size) (Fin size) ℝ) (rowPick : Fin rank → Fin size)
    (a : Fin rank) :
    (∑ b ∈ Finset.univ.erase a, |proj (rowPick a) (rowPick b)|) ^ 2
      ≤ ((Finset.univ.erase a).card : ℝ)
        * ∑ b ∈ Finset.univ.erase a, proj (rowPick a) (rowPick b) ^ 2 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase a)
    (fun _ => (1 : ℝ)) (fun b => |proj (rowPick a) (rowPick b)|)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at hcs
  exact hcs

/-- **THE LEVERAGE BUDGET.**  A `k`-subset witnesses the covering as soon as
every chosen row satisfies one inequality in its own diagonal entry.

The off-diagonal entries of the block never appear.  The proof spends
Cauchy–Schwarz, the projection row law, and the general dominance lemma. -/
theorem projectionCovering_of_leverageBudget {size rank : ℕ}
    (proj : Matrix (Fin size) (Fin size) ℝ) (hsymm : projᵀ = proj)
    (hidem : proj * proj = proj)
    (rowPick : Fin rank → Fin size) (hinj : Function.Injective rowPick)
    (hshift : ∀ a : Fin rank, (size : ℝ)⁻¹ < proj (rowPick a) (rowPick a))
    (hbudget : ∀ a : Fin rank,
      ((rank : ℝ) - 1) * (proj (rowPick a) (rowPick a)
          * (1 - proj (rowPick a) (rowPick a)))
        < (proj (rowPick a) (rowPick a) - (size : ℝ)⁻¹) ^ 2) :
    (proj.submatrix rowPick rowPick - (size : ℝ)⁻¹ • 1).PosSemidef := by
  classical
  refine projectionCovering_of_rowDominance proj hsymm rowPick hinj fun a => ?_
  set absRow := ∑ b ∈ Finset.univ.erase a, |proj (rowPick a) (rowPick b)| with habsRow
  have hnonneg : 0 ≤ absRow := Finset.sum_nonneg fun b _ => abs_nonneg _
  have hcs := sq_absOffRow_le_card_mul_energy proj rowPick a
  -- The picked energy is bounded by the whole off-diagonal energy of the row.
  have himg : ∑ c ∈ (Finset.univ.erase a).image rowPick, proj (rowPick a) c ^ 2
      = ∑ b ∈ Finset.univ.erase a, proj (rowPick a) (rowPick b) ^ 2 :=
    Finset.sum_image (fun x _ y _ h => hinj h)
  have hsubset : ∑ b ∈ Finset.univ.erase a, proj (rowPick a) (rowPick b) ^ 2
      ≤ ∑ c ∈ Finset.univ.erase (rowPick a), proj (rowPick a) c ^ 2 := by
    rw [← himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun c _ _ => sq_nonneg _)
    intro c hc
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_erase.mpr
      ⟨fun h => (Finset.mem_erase.mp hb).1 (hinj h), Finset.mem_univ _⟩
  have hrankOne : (1 : ℝ) ≤ (rank : ℝ) := by
    have hpos : 1 ≤ rank := Fin.pos a
    exact_mod_cast hpos
  have hcard : ((Finset.univ.erase a).card : ℝ) = (rank : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (Fin.pos a), Nat.cast_one]
  have henergy := projection_offDiag_sq_energy hsymm hidem (rowPick a)
  have hshifted := hshift a
  have hbudgeted := hbudget a
  have hdiagNonneg : 0 ≤ proj (rowPick a) (rowPick a) * (1 - proj (rowPick a) (rowPick a)) := by
    rw [← henergy]
    exact Finset.sum_nonneg fun c _ => sq_nonneg _
  have hsq : absRow ^ 2 < (proj (rowPick a) (rowPick a) - (size : ℝ)⁻¹) ^ 2 := by
    have hbound : absRow ^ 2
        ≤ ((rank : ℝ) - 1) * (proj (rowPick a) (rowPick a)
            * (1 - proj (rowPick a) (rowPick a))) := by
      refine hcs.trans ?_
      rw [hcard]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      rw [← henergy]
      exact hsubset
    linarith
  nlinarith [hsq, hnonneg, sub_pos.mpr hshifted]

/-! ## The rank-three reading

At `size = 6` and `rank = 3` the budget clears to `0 < 108 d ^ 2 - 84 d + 1`,
whose value at `d = 7 / 9` is exactly `1`.  The quadratic increases past its
vertex `7 / 18`, so every leverage at least `7 / 9` clears it.
-/

/-- **THE SIX-THREE LEVERAGE CELL.**  Three rows of a rank-three projection on
six coordinates, each of leverage at least `7 / 9`, witness the covering. -/
theorem projectionCovering_sixThree_of_sevenNinths
    (proj : Matrix (Fin 6) (Fin 6) ℝ) (hsymm : projᵀ = proj)
    (hidem : proj * proj = proj)
    (rowPick : Fin 3 → Fin 6) (hinj : Function.Injective rowPick)
    (hlev : ∀ a : Fin 3, 7 / 9 ≤ proj (rowPick a) (rowPick a)) :
    (proj.submatrix rowPick rowPick - (6 : ℝ)⁻¹ • 1).PosSemidef := by
  refine projectionCovering_of_leverageBudget proj hsymm hidem rowPick hinj
    (fun a => lt_of_lt_of_le (by norm_num) (hlev a)) fun a => ?_
  have hd := hlev a
  -- The diagonal of a projection never exceeds one, by the row law.
  have hle : proj (rowPick a) (rowPick a) ≤ 1 := by
    have henergy := projection_offDiag_sq_energy hsymm hidem (rowPick a)
    have hnonneg : 0 ≤ ∑ b ∈ Finset.univ.erase (rowPick a), proj (rowPick a) b ^ 2 :=
      Finset.sum_nonneg fun b _ => sq_nonneg _
    nlinarith [henergy, hnonneg, hd]
  have hpos : (0 : ℝ) < proj (rowPick a) (rowPick a) := by linarith
  norm_num
  nlinarith [mul_nonneg hpos.le (by linarith : (0 : ℝ) ≤ 9 * proj (rowPick a) (rowPick a) - 7),
    hd, hle]

end Gtz

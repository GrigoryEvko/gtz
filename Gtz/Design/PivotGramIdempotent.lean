/-
# The full-selection pivot Gram is a co-weighted idempotent

`Gtz.descent_identity` reads the trace identity at the full base set and prices
the DIAGONAL of the inverse Gram of the atoms: `Σ_c (1 − t_c) b_c = k`.  Nothing
landed prices the OFF-diagonal.  This module does, and the price is exact.

Write `fullPivotGram D c d = a_c ⬝ (S_univ − 1)⁻¹ a_d`.  Parseval says that
`Σ_c (1 − t_c) a_c a_cᵀ` IS the full gap, so inserting it between two inverses
collapses one of them:

  `Σ_j (1 − t_j) · P c j · P j d = P c d`          (the idempotent law)

`P` is an idempotent for the co-weighted inner product.  Four consequences
follow, and none of them needs a square root.

The diagonal of the law is a ROW ENERGY identity: the pivot of an atom is the
co-weighted energy of its whole row of cross pivots.  Isolating the diagonal
term of that sum gives a per-atom CAP, `(1 − t_c) · b_c ≤ 1`, which is the first
upper bound the campaign carries on a full-selection pivot.  The cap is RIGID:
an atom that attains it has every cross pivot zero, so it decouples from the
other five.  And summing the row energies against the co-weights returns the
rank, which is the Frobenius reading of the same idempotent.

The cap also sharpens the counting.  `Gtz.card_pivot_le_one_ge` counts the atoms
of pivot at most one.  The same identity counts the atoms of pivot strictly
below one, because the heavy atoms carry co-weight summing strictly below one.
At `(6,3)` that is a free candidate set of three labels, and by
`Gtz.residualPairing_diag` those are exactly the labels whose residual pairing
diagonal is positive.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.TraceIdentity
import Gtz.Reduction.DescentLadder
import Gtz.Design.ResidualPairingLaw

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ### The pivot Gram at the full selection -/

/-- The inverse Gram of two atoms against the full gap, at every size and rank.
Its diagonal is the full-selection pivot. -/
noncomputable def fullPivotGram (D : WeightedDesign m k) (c d : Fin m) : ℝ :=
  D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom d)

/-- The diagonal of the pivot Gram is the full-selection pivot. -/
theorem fullPivotGram_diag (D : WeightedDesign m k) (c : Fin m) :
    fullPivotGram D c c = pivot D Finset.univ c :=
  (pivot_eq_dot D Finset.univ c).symm

/-- The full gap is symmetric at every size and rank. -/
theorem fullExcess_transpose (D : WeightedDesign m k) :
    (subsetSum D Finset.univ - 1)ᵀ = subsetSum D Finset.univ - 1 := by
  have hsym : (subsetSum D Finset.univ)ᵀ = subsetSum D Finset.univ := by
    rw [subsetSum, Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun label _ => by
      rw [atomMatrix, Matrix.transpose_vecMulVec]
  rw [Matrix.transpose_sub, hsym, Matrix.transpose_one]

/-- The inverse of the full gap is symmetric. -/
theorem fullExcess_inv_transpose (D : WeightedDesign m k) :
    ((subsetSum D Finset.univ - 1)⁻¹)ᵀ = (subsetSum D Finset.univ - 1)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, fullExcess_transpose]

/-- The pivot Gram is symmetric. -/
theorem fullPivotGram_comm (D : WeightedDesign m k) (c d : Fin m) :
    fullPivotGram D c d = fullPivotGram D d c :=
  dotProduct_mulVec_comm_of_transpose (fullExcess_inv_transpose D) (D.atom c) (D.atom d)

/-- A rank-one atom acts on a probe by scaling the atom vector. -/
theorem atomMatrix_mulVec (g y : Fin k → ℝ) :
    atomMatrix g *ᵥ y = (g ⬝ᵥ y) • g := by
  funext i
  simp only [atomMatrix, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### The idempotent law -/

/-- **The co-weighted idempotent law.**  Parseval reads the full gap as the
co-weighted atom sum, so inserting it between the two inverses of a product of
pivot Gram entries cancels one inverse and returns a single entry.  No
positivity beyond the invertibility of the gap is used. -/
theorem sum_coweight_mul_fullPivotGram_mul (D : WeightedDesign m k) (hm : 2 ≤ m)
    (c d : Fin m) :
    ∑ j, (1 - D.weight j) * (fullPivotGram D c j * fullPivotGram D j d)
      = fullPivotGram D c d := by
  classical
  have hposU := posDef_fullExcess D hm
  have hdet : IsUnit (subsetSum D Finset.univ - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hposU.det_pos)
  have hsymInv := fullExcess_inv_transpose D
  -- every summand is one quadratic reading of the co-weighted atom
  have hterm : ∀ j : Fin m,
      (1 - D.weight j) * (fullPivotGram D c j * fullPivotGram D j d)
        = ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c) ⬝ᵥ
            (((1 - D.weight j) • atomMatrix (D.atom j)) *ᵥ
              ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom d)) := by
    intro j
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix_mulVec,
      dotProduct_smul, smul_eq_mul]
    have hcj : fullPivotGram D c j
        = ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c) ⬝ᵥ D.atom j := by
      rw [fullPivotGram, dotProduct_mulVec_comm_of_transpose hsymInv,
        dotProduct_comm]
    rw [hcj, fullPivotGram]
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← dotProduct_sum, ← Matrix.sum_mulVec,
    ← fullExcess_eq_coParseval D, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec, fullPivotGram, dotProduct_comm,
    dotProduct_mulVec_comm_of_transpose hsymInv]

/-- **The row energy law.**  The full-selection pivot of an atom is the
co-weighted energy of its row of cross pivots.  This is the diagonal of the
idempotent law, read through the symmetry of the Gram. -/
theorem sum_coweight_mul_fullPivotGram_sq (D : WeightedDesign m k) (hm : 2 ≤ m)
    (c : Fin m) :
    ∑ j, (1 - D.weight j) * fullPivotGram D c j ^ 2 = pivot D Finset.univ c := by
  rw [← fullPivotGram_diag D c, ← sum_coweight_mul_fullPivotGram_mul D hm c c]
  exact Finset.sum_congr rfl fun j _ => by
    rw [fullPivotGram_comm D j c]
    ring

/-! ### The cap on a full-selection pivot -/

/-- **The pivot cap.**  Every full-selection pivot is at most the reciprocal of
its atom's co-weight.  The row energy law dominates the whole row by its own
diagonal term, and the pivot is nonnegative. -/
theorem coweight_mul_pivot_univ_le_one (D : WeightedDesign m k) (hm : 2 ≤ m)
    (c : Fin m) :
    (1 - D.weight c) * pivot D Finset.univ c ≤ 1 := by
  classical
  have hrow := sum_coweight_mul_fullPivotGram_sq D hm c
  have hnonneg := pivot_nonneg D Finset.univ (posDef_fullExcess D hm) c
  -- the diagonal term alone is at most the whole nonnegative row energy
  have hrest : (1 - D.weight c) * fullPivotGram D c c ^ 2
      ≤ ∑ j, (1 - D.weight j) * fullPivotGram D c j ^ 2 := by
    refine Finset.single_le_sum (f := fun j => (1 - D.weight j) * fullPivotGram D c j ^ 2)
      (fun j _ => mul_nonneg (one_sub_weight_mem D hm j).1.le (sq_nonneg _))
      (Finset.mem_univ c)
  rw [hrow, fullPivotGram_diag] at hrest
  -- `(1−t) b² ≤ b` with `b ≥ 0` forces `(1−t) b ≤ 1`
  by_contra hgt
  push Not at hgt
  have hbpos : 0 < pivot D Finset.univ c := by
    rcases hnonneg.lt_or_eq with h | h
    · exact h
    · rw [← h] at hgt; simp at hgt; linarith [(one_sub_weight_mem D hm c).1]
  nlinarith [hrest, hgt, hbpos]

/-- The pivot cap in reciprocal form. -/
theorem pivot_univ_le_inv_coweight (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    pivot D Finset.univ c ≤ (1 - D.weight c)⁻¹ := by
  have hpos := (one_sub_weight_mem D hm c).1
  rw [inv_eq_one_div, le_div_iff₀ hpos]
  nlinarith [coweight_mul_pivot_univ_le_one D hm c]

/-! ### The off-diagonal energy and its rigidity -/

/-- **The off-diagonal energy is the diagonal defect.**  Removing the diagonal
term from the row energy leaves exactly the slack of the pivot cap, scaled by
the pivot. -/
theorem sum_erase_coweight_mul_fullPivotGram_sq (D : WeightedDesign m k) (hm : 2 ≤ m)
    (c : Fin m) :
    ∑ j ∈ Finset.univ.erase c, (1 - D.weight j) * fullPivotGram D c j ^ 2
      = pivot D Finset.univ c * (1 - (1 - D.weight c) * pivot D Finset.univ c) := by
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun j => (1 - D.weight j) * fullPivotGram D c j ^ 2) (Finset.mem_univ c)
  rw [sum_coweight_mul_fullPivotGram_sq D hm c] at hsplit
  rw [fullPivotGram_diag] at hsplit
  have hexpand : pivot D Finset.univ c * (1 - (1 - D.weight c) * pivot D Finset.univ c)
      = pivot D Finset.univ c - (1 - D.weight c) * pivot D Finset.univ c ^ 2 := by ring
  rw [hexpand]
  linarith [hsplit]

/-- **Rigidity at the cap.**  An atom whose pivot attains the cap has every
cross pivot to another atom equal to zero.  Such an atom decouples from the rest
of the design in the inverse Gram. -/
theorem fullPivotGram_eq_zero_of_pivot_eq_cap (D : WeightedDesign m k) (hm : 2 ≤ m)
    {c : Fin m} (hcap : (1 - D.weight c) * pivot D Finset.univ c = 1)
    {j : Fin m} (hj : j ≠ c) :
    fullPivotGram D c j = 0 := by
  classical
  have hsum := sum_erase_coweight_mul_fullPivotGram_sq D hm c
  rw [hcap] at hsum
  simp only [sub_self, mul_zero] at hsum
  have hterm : ∀ i ∈ Finset.univ.erase c,
      0 ≤ (1 - D.weight i) * fullPivotGram D c i ^ 2 := fun i _ =>
    mul_nonneg (one_sub_weight_mem D hm i).1.le (sq_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum j
    (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  have hcoPos := (one_sub_weight_mem D hm j).1
  have : fullPivotGram D c j ^ 2 = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · linarith
    · exact h
  exact pow_eq_zero_iff (by norm_num) |>.mp this

/-- **The Frobenius reading.**  Summing the row energies against the co-weights
returns the rank: the co-weighted Frobenius norm of the pivot Gram is `k`. -/
theorem sum_sum_coweight_mul_fullPivotGram_sq (D : WeightedDesign m k) (hm : 2 ≤ m) :
    ∑ c, ∑ j, (1 - D.weight c) * ((1 - D.weight j) * fullPivotGram D c j ^ 2)
      = (k : ℝ) := by
  rw [← descent_identity D hm]
  exact Finset.sum_congr rfl fun c _ => by
    rw [← Finset.mul_sum, sum_coweight_mul_fullPivotGram_sq D hm c]

/-! ### The sharp candidate count -/

/-- **The strict droppable count.**  `Gtz.card_pivot_le_one_ge` counts the atoms
of pivot at most one.  The heavy atoms, those of pivot at least one, carry
co-weight summing strictly below their number, so at most `k` of them exist and
at least `m − k` atoms carry pivot STRICTLY below one.  This is sharper than the
landed non-strict count, and at `(6,3)` it hands back three labels. -/
theorem card_pivot_lt_one_ge (D : WeightedDesign m k) (hmk : k + 2 ≤ m) :
    m ≤ k + (Finset.univ.filter
      (fun c => pivot D Finset.univ c < 1)).card := by
  classical
  have hm : 2 ≤ m := by omega
  set heavy := Finset.univ.filter (fun c => (1 : ℝ) ≤ pivot D Finset.univ c) with hheavy
  have hposDef := posDef_fullExcess D hm
  have hcoPos : ∀ c, (0 : ℝ) < 1 - D.weight c := fun c => (one_sub_weight_mem D hm c).1
  -- the heavy set is not everything
  have hne : heavy ≠ Finset.univ := by
    intro hall
    have hbig : (m : ℝ) - 1 ≤ (k : ℝ) := by
      have hsum : ∑ c, (1 - D.weight c) ≤ ∑ c, (1 - D.weight c) * pivot D Finset.univ c := by
        refine Finset.sum_le_sum fun c _ => ?_
        have hc : (1 : ℝ) ≤ pivot D Finset.univ c := by
          have : c ∈ heavy := by rw [hall]; exact Finset.mem_univ c
          rw [hheavy] at this
          exact (Finset.mem_filter.mp this).2
        nlinarith [hcoPos c]
      rw [sum_one_sub_weight, descent_identity D hm] at hsum
      exact hsum
    have : (k : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hmk
    linarith
  -- the heavy weights sum strictly below one
  have hwlt : ∑ c ∈ heavy, D.weight c < 1 := by
    have hcompl : heavyᶜ.Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
      have hle : heavy.card ≤ m := by simpa using Finset.card_le_univ heavy
      have hneq : heavy.card ≠ m := fun heq =>
        hne (Finset.eq_univ_of_card heavy (by rw [heq, Fintype.card_fin]))
      omega
    have hsplit : ∑ c ∈ heavy, D.weight c + ∑ c ∈ heavyᶜ, D.weight c = 1 := by
      rw [Finset.sum_add_sum_compl]; exact D.weight_sum_one
    have hpos : 0 < ∑ c ∈ heavyᶜ, D.weight c :=
      Finset.sum_pos (fun c _ => D.weight_pos c) hcompl
    linarith
  -- the identity bounds the heavy cardinality by the rank
  have hcard : heavy.card ≤ k := by
    have hlow : (heavy.card : ℝ) - ∑ c ∈ heavy, D.weight c
        ≤ ∑ c ∈ heavy, (1 - D.weight c) * pivot D Finset.univ c := by
      have hstep : ∀ c ∈ heavy,
          1 - D.weight c ≤ (1 - D.weight c) * pivot D Finset.univ c := by
        intro c hc
        rw [hheavy] at hc
        nlinarith [hcoPos c, (Finset.mem_filter.mp hc).2]
      calc (heavy.card : ℝ) - ∑ c ∈ heavy, D.weight c
          = ∑ c ∈ heavy, (1 - D.weight c) := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ _ := Finset.sum_le_sum hstep
    have hrest : 0 ≤ ∑ c ∈ heavyᶜ, (1 - D.weight c) * pivot D Finset.univ c :=
      Finset.sum_nonneg fun c _ =>
        mul_nonneg (hcoPos c).le (pivot_nonneg D Finset.univ hposDef c)
    have htotal : ∑ c ∈ heavy, (1 - D.weight c) * pivot D Finset.univ c
        + ∑ c ∈ heavyᶜ, (1 - D.weight c) * pivot D Finset.univ c = (k : ℝ) := by
      rw [Finset.sum_add_sum_compl]; exact descent_identity D hm
    have hreal : (heavy.card : ℝ) < (k : ℝ) + 1 := by linarith
    have hnat : heavy.card < k + 1 := by exact_mod_cast hreal
    omega
  -- the light set is the complement of the heavy set
  have hcompl : Finset.univ.filter (fun c => pivot D Finset.univ c < 1) = heavyᶜ := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, hheavy,
      not_le]
  rw [hcompl, Finset.card_compl, Fintype.card_fin]
  omega

/-! ### The `(6,3)` reading through the residual pairing -/

variable (design : WeightedDesign 6 3)

/-- The pivot Gram is the residual pairing's cross term. -/
theorem crossPivot_eq_fullPivotGram (c d : Fin 6) :
    crossPivot design c d = fullPivotGram design c d := by
  rw [crossPivot, fullPivotGram, fullGap]

/-- **A floor on the residual pairing diagonal.**  The pivot cap reads on the
pairing as a lower bound that no design can breach. -/
theorem residualPairing_diag_ge (c : Fin 6) :
    -(design.weight c) / (1 - design.weight c) ≤ residualPairing design c c := by
  have hm : (2 : ℕ) ≤ 6 := by norm_num
  have hpos := (one_sub_weight_mem design hm c).1
  have hcap := coweight_mul_pivot_univ_le_one design hm c
  rw [residualPairing_diag, div_le_iff₀ hpos]
  nlinarith [hcap]

/-- **The free candidate triple at `(6,3)`.**  At least three of the six labels
carry a strictly positive residual pairing diagonal.  By
`Gtz.noStrict_iff_no_tripleMinor` the A1 residual asks for a positive definite
principal triple of that pairing, and this is the first free restriction on
where such a triple can sit. -/
theorem three_le_card_residualPairing_diag_pos :
    3 ≤ (Finset.univ.filter
      (fun c => 0 < residualPairing design c c)).card := by
  classical
  have hcount := card_pivot_lt_one_ge design (by norm_num)
  have hset : Finset.univ.filter (fun c => 0 < residualPairing design c c)
      = Finset.univ.filter (fun c => pivot design Finset.univ c < 1) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, residualPairing_diag]
    constructor <;> intro h <;> linarith
  rw [hset]
  omega

end Gtz

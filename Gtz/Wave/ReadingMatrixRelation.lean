import Gtz.Wave.MemberGramPushThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The reading matrix is a generalized inverse of the weight defect

Let `V` be the atom matrix of a design, `F` a subset whose gap
`A = S_F − 1` is invertible, and

  `Dm := diag( 1_{a ∈ F} − t_a )` ,   `P := Vᵀ A⁻¹ V` .

Parseval says the weighted atoms resolve the identity, so the SAME defect
diagonal rebuilds the gap (`Gtz.atoms_weightDefect_eq_gap`):

  `V · Dm · Vᵀ = S_F − 1` .

Substituting twice gives an exact QUADRATIC relation on the whole matrix of
readings (`Gtz.reading_matrix_generalized_inverse`):

  `P · Dm · P = P` .

Its TRACE is the coweight ledger `Σ_{a∈F}(1 − t_a)·r_a − Σ_{b∉F} t_b·r_b = 3`,
because `tr(Dm·P) = tr(A⁻¹ V Dm Vᵀ) = tr(A⁻¹A) = 3`.  The ledger is one
scalar; the relation is `m(m+1)/2` of them, and the campaign has been
deriving its shadows one at a time.

## Why this is the ambient ideal

`P` is symmetric of rank three and `P·Dm` is idempotent.  Conversely, given
`P = VᵀA⁻¹V`, the relation `P·Dm·P = P` is EQUIVALENT to `V·Dm·Vᵀ = A`, that
is, to weighted Parseval.  So a certificate written against these equations
consumes Parseval automatically, in reading coordinates, with no frame and no
positivity.

## The scalar family

Entry by entry (`Gtz.reading_relation_split`):

  `Σ_{b∈F}(1−t_b)·P_ab·P_bc − Σ_{b∉F} t_b·P_ab·P_bc = P_ac` .

On the diagonal at a MEMBER `d ∈ F` (`Gtz.reading_relation_member_diag`), the
`b = d` term is `(1−t_d)·r_d²`, so

  `r_d·(1 − (1−t_d)·r_d) = Σ_{b∈F, b≠d}(1−t_b)·P_db² − Σ_{b∉F} t_b·P_db²` .

Every coefficient on the first sum is nonnegative, which gives the quadratic
floor `Gtz.reading_member_diag_floor`:

  `0 ≤ r_d·(1 − (1−t_d)·r_d) + Σ_{b∉F} t_b·P_db²` .

A member whose reading exceeds `1/(1−t_d)` makes the left summand negative,
so the EXCLUDED atoms must carry the cross readings.  That ties the member
floors to the excluded cross readings, and no aggregate of the campaign —
ledger, trace pinch, S-floor — sees it, because all of them are traces.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The atom matrix and the weight defect -/

/-- The atom matrix of a design: the columns are the atoms. -/
def atomsMatrix (D : WeightedDesign m 3) : Matrix (Fin 3) (Fin m) ℝ :=
  Matrix.of fun i a => D.atom a i

@[simp] theorem atomsMatrix_apply (D : WeightedDesign m 3) (i : Fin 3) (a : Fin m) :
    atomsMatrix D i a = D.atom a i := rfl

/-- The weight defect of a subset: one on the members, minus the weight
everywhere. -/
noncomputable def weightDefect (D : WeightedDesign m 3) (F : Finset (Fin m)) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal fun a => (if a ∈ F then (1 : ℝ) else 0) - D.weight a

/-- Conjugating any diagonal by the atom matrix rebuilds the matching weighted
atom sum. -/
theorem atomsMatrix_diagonal_conj (D : WeightedDesign m 3) (dg : Fin m → ℝ) :
    atomsMatrix D * Matrix.diagonal dg * (atomsMatrix D)ᵀ
      = ∑ a, dg a • atomMatrix (D.atom a) := by
  classical
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, atomMatrix, Matrix.vecMulVec_apply, atomsMatrix,
    Matrix.of_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **THE DEFECT REBUILDS THE GAP.**  Parseval turns the weight defect into
the subset gap: `V·Dm·Vᵀ = S_F − 1`. -/
theorem atoms_weightDefect_eq_gap (D : WeightedDesign m 3) (F : Finset (Fin m)) :
    atomsMatrix D * weightDefect D F * (atomsMatrix D)ᵀ = subsetSum D F - 1 := by
  classical
  rw [weightDefect, atomsMatrix_diagonal_conj]
  have hsplit : ∀ a : Fin m,
      ((if a ∈ F then (1 : ℝ) else 0) - D.weight a) • atomMatrix (D.atom a)
        = (if a ∈ F then atomMatrix (D.atom a) else 0)
          - D.weight a • atomMatrix (D.atom a) := by
    intro a
    by_cases ha : a ∈ F <;> simp [ha, sub_smul]
  rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_sub_distrib,
    Finset.sum_ite_mem, Finset.univ_inter, D.isParseval]
  rfl

/-! ## 2. The reading matrix -/

/-- The matrix of readings of every atom pair at the inverse gap. -/
noncomputable def readingMatrix (D : WeightedDesign m 3) (F : Finset (Fin m)) :
    Matrix (Fin m) (Fin m) ℝ :=
  (atomsMatrix D)ᵀ * (subsetSum D F - 1)⁻¹ * atomsMatrix D

/-- The entries of the reading matrix are the readings. -/
theorem readingMatrix_apply (D : WeightedDesign m 3) (F : Finset (Fin m))
    (a b : Fin m) :
    readingMatrix D F a b
      = D.atom a ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom b) := by
  simp only [readingMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    atomsMatrix, Matrix.of_apply, dotProduct, Matrix.mulVec, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **THE READINGS ARE SYMMETRIC.**  `P_ab = P_ba` — the cross reading of two
atoms does not depend on which one is probed. -/
theorem readingMatrix_symm (D : WeightedDesign m 3) (F : Finset (Fin m))
    (a b : Fin m) : readingMatrix D F a b = readingMatrix D F b a := by
  have hT : (readingMatrix D F)ᵀ = readingMatrix D F := by
    rw [readingMatrix, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_nonsing_inv,
      Matrix.transpose_sub, Matrix.transpose_one, subsetSum_transpose,
      Matrix.mul_assoc]
  exact congrFun (congrFun hT b) a

/-! ## 3. The relation -/

/-- **THE READING MATRIX IS A GENERALIZED INVERSE OF THE DEFECT.**

  `P · Dm · P = P` ,  `P = Vᵀ(S_F − 1)⁻¹V` ,  `Dm = diag(1_{a∈F} − t_a)` .

An identity at every design and every subset with invertible gap: no
positivity, no tie, no corner.  Its trace is the coweight ledger, and its
entries are the whole ambient ideal of the reading arena. -/
theorem reading_matrix_generalized_inverse (D : WeightedDesign m 3)
    (F : Finset (Fin m)) (hdet : IsUnit (subsetSum D F - 1).det) :
    readingMatrix D F * weightDefect D F * readingMatrix D F
      = readingMatrix D F := by
  set A : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hA
  set V : Matrix (Fin 3) (Fin m) ℝ := atomsMatrix D with hV
  have hgap : V * weightDefect D F * Vᵀ = A := by
    rw [hV, hA]; exact atoms_weightDefect_eq_gap D F
  calc readingMatrix D F * weightDefect D F * readingMatrix D F
      = Vᵀ * A⁻¹ * (V * weightDefect D F * Vᵀ) * (A⁻¹ * V) := by
        simp only [readingMatrix, ← hV, ← hA, Matrix.mul_assoc]
    _ = Vᵀ * (A⁻¹ * A) * (A⁻¹ * V) := by
        rw [hgap]; simp only [Matrix.mul_assoc]
    _ = Vᵀ * A⁻¹ * V := by
        rw [Matrix.nonsing_inv_mul A hdet, Matrix.mul_one, Matrix.mul_assoc]
    _ = readingMatrix D F := by simp only [readingMatrix, ← hV, ← hA]

/-- The entry form of the relation: one scalar equation for each pair. -/
theorem reading_relation_entry (D : WeightedDesign m 3) (F : Finset (Fin m))
    (hdet : IsUnit (subsetSum D F - 1).det) (a c : Fin m) :
    ∑ b, ((if b ∈ F then (1 : ℝ) else 0) - D.weight b)
        * (readingMatrix D F a b * readingMatrix D F b c)
      = readingMatrix D F a c := by
  have hac := congrFun (congrFun (reading_matrix_generalized_inverse D F hdet) a) c
  rw [Matrix.mul_apply] at hac
  simp only [weightDefect, Matrix.mul_diagonal] at hac
  rw [← hac]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **THE SCALAR FAMILY.**  Members enter with the coweight `1 − t_b`, excluded
atoms with `−t_b`:

  `Σ_{b∈F}(1−t_b)·P_ab·P_bc − Σ_{b∉F} t_b·P_ab·P_bc = P_ac` . -/
theorem reading_relation_split (D : WeightedDesign m 3) (F : Finset (Fin m))
    (hdet : IsUnit (subsetSum D F - 1).det) (a c : Fin m) :
    (∑ b ∈ F, (1 - D.weight b)
        * (readingMatrix D F a b * readingMatrix D F b c))
      - ∑ b ∈ Fᶜ, D.weight b
          * (readingMatrix D F a b * readingMatrix D F b c)
      = readingMatrix D F a c := by
  classical
  rw [← reading_relation_entry D F hdet a c, ← Finset.sum_add_sum_compl F]
  have h1 : ∀ b ∈ F, ((if b ∈ F then (1 : ℝ) else 0) - D.weight b)
      * (readingMatrix D F a b * readingMatrix D F b c)
      = (1 - D.weight b) * (readingMatrix D F a b * readingMatrix D F b c) := by
    intro b hb; simp only [hb, ite_true]
  have h2 : ∀ b ∈ Fᶜ, ((if b ∈ F then (1 : ℝ) else 0) - D.weight b)
      * (readingMatrix D F a b * readingMatrix D F b c)
      = -(D.weight b * (readingMatrix D F a b * readingMatrix D F b c)) := by
    intro b hb
    simp only [Finset.mem_compl.mp hb, ite_false]; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_neg_distrib]
  ring

/-- **THE DIAGONAL RELATION.**  At `a = c` every cross reading enters squared:

  `Σ_{b∈F}(1−t_b)·P_ab² − Σ_{b∉F} t_b·P_ab² = r_a` . -/
theorem reading_relation_diag (D : WeightedDesign m 3) (F : Finset (Fin m))
    (hdet : IsUnit (subsetSum D F - 1).det) (a : Fin m) :
    (∑ b ∈ F, (1 - D.weight b) * readingMatrix D F a b ^ 2)
      - ∑ b ∈ Fᶜ, D.weight b * readingMatrix D F a b ^ 2
      = readingMatrix D F a a := by
  rw [← reading_relation_split D F hdet a a]
  congr 1
  · exact Finset.sum_congr rfl fun b _ => by
      rw [readingMatrix_symm D F b a]; ring
  · exact Finset.sum_congr rfl fun b _ => by
      rw [readingMatrix_symm D F b a]; ring

/-- **THE MEMBER DIAGONAL.**  For a member `d ∈ F` the `b = d` term of the
diagonal relation is `(1−t_d)·r_d²`, so

  `r_d·(1 − (1−t_d)·r_d) = Σ_{b∈F, b≠d}(1−t_b)·P_db² − Σ_{b∉F} t_b·P_db²` .

A member reading past `1/(1−t_d)` makes the left side negative and so forces
the EXCLUDED atoms to carry the cross readings. -/
theorem reading_relation_member_diag (D : WeightedDesign m 3) (F : Finset (Fin m))
    (hdet : IsUnit (subsetSum D F - 1).det) (d : Fin m) (hd : d ∈ F) :
    readingMatrix D F d d * (1 - (1 - D.weight d) * readingMatrix D F d d)
      = (∑ b ∈ F.erase d, (1 - D.weight b) * readingMatrix D F d b ^ 2)
        - ∑ b ∈ Fᶜ, D.weight b * readingMatrix D F d b ^ 2 := by
  classical
  have hdiag := reading_relation_diag D F hdet d
  rw [← Finset.add_sum_erase F _ hd] at hdiag
  nlinarith [hdiag, sq_nonneg (readingMatrix D F d d)]

/-- **THE QUADRATIC FLOOR.**  Every coweight `1 − t_b` is nonnegative, so the
member diagonal gives an inequality with no cross readings of the members:

  `0 ≤ r_d·(1 − (1−t_d)·r_d) + Σ_{b∉F} t_b·P_db²` . -/
theorem reading_member_diag_floor (D : WeightedDesign m 3) (F : Finset (Fin m))
    (hdet : IsUnit (subsetSum D F - 1).det) (d : Fin m) (hd : d ∈ F) :
    0 ≤ readingMatrix D F d d
          * (1 - (1 - D.weight d) * readingMatrix D F d d)
        + ∑ b ∈ Fᶜ, D.weight b * readingMatrix D F d b ^ 2 := by
  classical
  have hrel := reading_relation_member_diag D F hdet d hd
  have hnonneg : 0 ≤ ∑ b ∈ F.erase d,
      (1 - D.weight b) * readingMatrix D F d b ^ 2 := by
    refine Finset.sum_nonneg fun b _ => ?_
    have hb : D.weight b ≤ 1 := by
      rw [← D.weight_sum_one]
      exact Finset.single_le_sum (fun c _ => (D.weight_pos c).le) (Finset.mem_univ b)
    exact mul_nonneg (by linarith) (sq_nonneg _)
  linarith

/-! ## 4. The heavy-inside cell

At the corner `Z1` the surviving four-set is `F = {y} ∪ Cᶜ`, whose complement
is the EXCLUDED PAIR `{x, z}`.  The member diagonal at an outside atom `d`
therefore reads

  `r_d·(1 − (1−t_d)·r_d) + t_x·P_dx² + t_z·P_dz² ≥ 0` ,

a quadratic tie between the outside floor and the two excluded cross
readings.  A reading past `1/(1−t_d)` makes the first summand negative and
forces the excluded pair to carry the difference. -/

/-- The complement of the surviving four-set is the excluded pair. -/
theorem corner_fourSet_compl_eq_pair {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) :
    ((insert y (({x, y, z} : Finset (Fin 6))ᶜ))ᶜ : Finset (Fin 6)) = {x, z} := by
  classical
  rw [Finset.compl_insert, compl_compl]
  ext a
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hay, rfl | h⟩
    · exact Or.inl rfl
    · rcases h with rfl | rfl
      · exact absurd rfl hay
      · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨hxy, Or.inl rfl⟩
    · exact ⟨Ne.symm hyz, Or.inr (Or.inr rfl)⟩

/-- **THE EXCLUDED PAIR CARRIES THE MEMBER DIAGONAL.**  On the surviving
four-set of the corner, every outside atom `d` obeys

  `r_d·(1 − (1−t_d)·r_d) + t_x·P_dx² + t_z·P_dz² ≥ 0` ,

with `P_dx`, `P_dz` the cross readings of `d` against the two EXCLUDED atoms.
No tie, no cell, no floor: only that the four-set gap is positive definite. -/
theorem corner_fourSet_member_diag_floor (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    {d : Fin 6} (hd : d ∈ (({x, y, z} : Finset (Fin 6))ᶜ)) :
    0 ≤ (D.atom d ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom d))
          * (1 - (1 - D.weight d)
              * (D.atom d ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                  - 1)⁻¹ *ᵥ D.atom d)))
        + D.weight x
            * (D.atom d ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom x)) ^ 2
        + D.weight z
            * (D.atom d ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom z)) ^ 2 := by
  classical
  set F : Finset (Fin 6) := insert y (({x, y, z} : Finset (Fin 6))ᶜ) with hF
  have hdet : IsUnit (subsetSum D F - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hAy.det_pos)
  have hdF : d ∈ F := Finset.mem_insert_of_mem hd
  have hfl := reading_member_diag_floor D F hdet d hdF
  rw [hF, corner_fourSet_compl_eq_pair hxy hxz hyz] at hfl
  have hxs : x ∉ ({z} : Finset (Fin 6)) := by simp [hxz]
  rw [Finset.sum_insert hxs, Finset.sum_singleton] at hfl
  simpa only [readingMatrix_apply, hF, add_assoc] using hfl

end Gtz

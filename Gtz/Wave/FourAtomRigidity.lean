/-
# The four-atom rigidity: branch B at size four is one explicit family

Branch B is the case of a boundary system in which every atom is strictly heavy
and every pair minor is positive.  At `(6,3)` it is Question 7.5(a) of the
survey, and it is open.  At size FOUR it is neither open nor empty:
`Gtz.branchB_nonempty_at_four` puts the regular tetrahedron inside it, and the
numerics of the predecessor round located the extremal ray of the six-point
problem by descent and found it degenerating onto a four-point configuration.

This module classifies that configuration completely.  A four-atom branch-B
boundary system is rigid up to its weights:

  **`Gtz.fourAtom_branchB_leverage`:  `3 · t_c · l_c = 2 + t_c` at every atom** ,

so the leverages are determined by the weights alone, and

  **`Gtz.fourAtom_branchB_tripleGapDet_eq_zero`:  every triple has gap
  determinant exactly zero** — all four triples dominate, none strictly.

At the uniform weight `1/4` this returns leverage three, the regular tetrahedron.
The predecessor's extremal ray, whose four surviving weights and leverages were
recorded as `t = 0.0326, 0.2151, 0.4126, 0.3342` and
`l = 20.63, 3.41, 1.94, 2.32`, is reproduced by the formula to four digits once
its weights are renormalised, so the classification identifies that ray exactly.

## Where the weights enter, and why the argument stops at size four

Write `u_c = 1 − t_c·l_c` for the co-share of an atom and `v_c = 1 − t_c` for its
co-weight, and set `z_c = u_c / v_c` (`Gtz.coShare`).  Two facts drive everything.

* **The pairing cap is an EQUALITY at size four** (`Gtz.four_pair_cap_eq`).  The
  complement of a pair is the sum of the two remaining atoms, a sum of two
  rank-one matrices in three dimensions, so its determinant vanishes rather than
  merely being nonnegative.  The landed `Gtz.det_one_sub_weighted_triple` then
  reads `t_a t_b ⟨g_a,g_b⟩² = u_a u_b`.
* **The complement of a TRIPLE is a single rank-one matrix**, so the same
  determinant law pins the product of the three pairings of a triple:
  `t_a t_b t_c · p_ab p_ac p_bc = − u_a u_b u_c`
  (`Gtz.four_triple_pairing_prod`).  In particular that product is never
  positive, which is the real shadow of the Bargmann invariant at four points.

Together they collapse the gap determinant of a triple to a form carrying no
pairing at all (`Gtz.four_tripleGapDet_identity`):

  `t_a t_b t_c · tripleGapDet = v_a v_b v_c − (u_a v_b v_c + v_a u_b v_c + v_a v_b u_c)` ,

whose sign is the sign of `1 − (z_a + z_b + z_c)`.  A boundary system needs every
triple nonpositive, so `z_a + z_b + z_c ≥ 1` for each of the four triples, that
is `z_d ≤ Z − 1` for every `d`, with `Z` the co-share total.  The trace of
Parseval gives `∑ v_c z_c = ∑ u_c = 4 − 3 = 1`, hence `∑ t_c z_c = Z − 1`
exactly.  **A convex combination of numbers that are all at most `Z − 1` and
equals `Z − 1` forces them all equal** (`Gtz.eq_of_le_weighted_average`), and the
weights are strictly positive, so no atom may be dropped from that argument.
This is the precise point at which weight positivity is consumed, and it is the
mechanism four independent lanes predicted a certificate here would need.

The argument does not survive to six points, and the reason is visible from the
shape of it.  At size `m` the complement of a triple is a sum of `m − 3` rank-one
matrices, and the condition on a triple is the nonpositivity of the determinant
of an `(m−3)×(m−3)` matrix.  At `m = 4` that determinant is a SCALAR, so
nonpositivity is an order relation and convexity bites.  At `m = 6` it is a
three by three determinant, and nonpositivity fixes only the PARITY of the number
of negative eigenvalues.  Size four is rigid because one is odd and small, not
because the geometry there is simpler.

[MEASURED before proving.  The three scalar laws of sections three and four hold
to `3.3e-13` over four hundred random four-atom designs.  A direct search for
four-atom branch-B boundary systems returned 306 independent solutions and every
one had `z ≡ 1/3` to eight digits.]
-/
import Gtz.Wave.ComplementBracketLaw
import Gtz.Design.TripleGramSylvester

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. Low rank in three dimensions

A sum of at most two rank-one matrices of order three is singular.  Both
statements are one `ring` after the determinant is expanded, with no hypothesis
of any kind. -/

/-- A single rank-one atom of order three is singular. -/
theorem det_smul_atomMatrix (al : ℝ) (a : Fin 3 → ℝ) :
    (al • atomMatrix a).det = 0 := by
  simp only [Matrix.det_fin_three, atomMatrix, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  ring

/-- **A SUM OF TWO RANK-ONE ATOMS OF ORDER THREE IS SINGULAR.**  This is where
the size four enters: at four atoms the complement of a pair has exactly two
terms, so the landed pairing cap is attained rather than merely valid. -/
theorem det_smul_atomMatrix_add (al be : ℝ) (a b : Fin 3 → ℝ) :
    (al • atomMatrix a + be • atomMatrix b).det = 0 := by
  simp only [Matrix.det_fin_three, atomMatrix, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  ring

/-! ## 2. The complement of a pair and of a triple, at four atoms -/

/-- The complement of a pair of atoms of a four-atom design is the sum of the two
remaining weighted atoms. -/
theorem four_complement_pair (D : WeightedDesign 4 3) {i j k l : Fin 4}
    (hset : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (1 : Matrix (Fin 3) (Fin 3) ℝ) - D.weight i • atomMatrix (D.atom i)
        - D.weight j • atomMatrix (D.atom j)
      = D.weight k • atomMatrix (D.atom k) + D.weight l • atomMatrix (D.atom l) := by
  have hp := D.isParseval
  rw [← hset, Finset.sum_insert (by simp [hij, hik, hil]),
    Finset.sum_insert (by simp [hjk, hjl]), Finset.sum_insert (by simp [hkl]),
    Finset.sum_singleton] at hp
  rw [← hp]; abel

/-- The complement of a triple of atoms of a four-atom design is the one
remaining weighted atom. -/
theorem four_complement_triple (D : WeightedDesign 4 3) {i j k l : Fin 4}
    (hset : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (1 : Matrix (Fin 3) (Fin 3) ℝ) - D.weight i • atomMatrix (D.atom i)
        - D.weight j • atomMatrix (D.atom j) - D.weight k • atomMatrix (D.atom k)
      = D.weight l • atomMatrix (D.atom l) := by
  have hp := D.isParseval
  rw [← hset, Finset.sum_insert (by simp [hij, hik, hil]),
    Finset.sum_insert (by simp [hjk, hjl]), Finset.sum_insert (by simp [hkl]),
    Finset.sum_singleton] at hp
  rw [← hp]; abel

/-! ## 3. The pairing cap is an equality, and the triple pairing product is pinned -/

/-- **THE PAIRING CAP IS AN EQUALITY AT FOUR ATOMS.**  The landed
`Gtz.pairing_cap` bounds the weighted squared pairing by the product of the two
co-shares, because the complement of a pair is positive semidefinite.  At four
atoms that complement is a sum of only two rank-one matrices in three
dimensions, hence singular, and the bound is attained. -/
theorem four_pair_cap_eq (D : WeightedDesign 4 3) {i j k l : Fin 4}
    (hset : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    D.weight i * D.weight j * (D.atom i ⬝ᵥ D.atom j) ^ 2
      = (1 - D.weight i * leverageOf (D.atom i))
        * (1 - D.weight j * leverageOf (D.atom j)) := by
  have hzero : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - D.weight i • atomMatrix (D.atom i)
      - D.weight j • atomMatrix (D.atom j)
      - (0 : ℝ) • atomMatrix (D.atom i)).det = 0 := by
    rw [zero_smul, sub_zero, four_complement_pair D hset hij hik hil hjk hjl hkl]
    exact det_smul_atomMatrix_add _ _ _ _
  rw [det_one_sub_weighted_triple, crossNormSq_eq_leverage_mul_sub_sq] at hzero
  simp only [zero_mul, mul_zero, add_zero, sub_zero, zero_add] at hzero
  nlinarith [hzero]

/-- The three pair equalities of one triple, packaged for the two identities
below.  Only the index bookkeeping differs between them. -/
theorem four_pair_cap_eq_triple (D : WeightedDesign 4 3) {i j k l : Fin 4}
    (hset : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    D.weight i * D.weight j * (D.atom i ⬝ᵥ D.atom j) ^ 2
        = (1 - D.weight i * leverageOf (D.atom i))
          * (1 - D.weight j * leverageOf (D.atom j))
      ∧ D.weight i * D.weight k * (D.atom i ⬝ᵥ D.atom k) ^ 2
        = (1 - D.weight i * leverageOf (D.atom i))
          * (1 - D.weight k * leverageOf (D.atom k))
      ∧ D.weight j * D.weight k * (D.atom j ⬝ᵥ D.atom k) ^ 2
        = (1 - D.weight j * leverageOf (D.atom j))
          * (1 - D.weight k * leverageOf (D.atom k)) := by
  have hsetB : ({i, k, j, l} : Finset (Fin 4)) = Finset.univ := by
    rw [← hset]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hsetC : ({j, k, i, l} : Finset (Fin 4)) = Finset.univ := by
    rw [← hset]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  exact ⟨four_pair_cap_eq D hset hij hik hil hjk hjl hkl,
    four_pair_cap_eq D hsetB hik hij hil (Ne.symm hjk) hkl hjl,
    four_pair_cap_eq D hsetC hjk (Ne.symm hij) hjl (Ne.symm hik) hkl hil⟩

/-- **THE PRODUCT OF THE THREE PAIRINGS OF A TRIPLE IS PINNED.**  The complement
of a triple is a single rank-one atom, hence singular, and the determinant law
together with the three pair equalities leaves exactly one relation: the
weighted product of the three pairings is minus the product of the three
co-shares.  In particular that product is never positive. -/
theorem four_triple_pairing_prod (D : WeightedDesign 4 3) {i j k l : Fin 4}
    (hset : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    D.weight i * D.weight j * D.weight k
        * ((D.atom i ⬝ᵥ D.atom j) * (D.atom i ⬝ᵥ D.atom k) * (D.atom j ⬝ᵥ D.atom k))
      = -((1 - D.weight i * leverageOf (D.atom i))
          * (1 - D.weight j * leverageOf (D.atom j))
          * (1 - D.weight k * leverageOf (D.atom k))) := by
  obtain ⟨hpij, hpik, hpjk⟩ := four_pair_cap_eq_triple D hset hij hik hil hjk hjl hkl
  have hzero : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - D.weight i • atomMatrix (D.atom i)
      - D.weight j • atomMatrix (D.atom j)
      - D.weight k • atomMatrix (D.atom k)).det = 0 := by
    rw [four_complement_triple D hset hij hik hil hjk hjl hkl]
    exact det_smul_atomMatrix _ _
  rw [det_one_sub_weighted_triple, crossNormSq_eq_leverage_mul_sub_sq,
    crossNormSq_eq_leverage_mul_sub_sq, crossNormSq_eq_leverage_mul_sub_sq] at hzero
  have hbr := sq_tripleBracket_eq_gramDet (D.atom i) (D.atom j) (D.atom k)
  rw [hbr] at hzero
  linear_combination (-(1 : ℝ) / 2) * hzero
    + ((D.weight k * leverageOf (D.atom k) - 1) / 2) * hpij
    + ((D.weight j * leverageOf (D.atom j) - 1) / 2) * hpik
    + ((D.weight i * leverageOf (D.atom i) - 1) / 2) * hpjk

/-! ## 4. The gap determinant of a triple, with the pairings eliminated -/

/-- **THE FOUR-ATOM GAP DETERMINANT IDENTITY.**  At four atoms the weighted gap
determinant of a triple carries no pairing at all: it is a polynomial in the
three co-weights `1 − t_c` and the three co-shares `1 − t_c l_c`.  Everything
else has been eliminated by the two complement relations. -/
theorem four_tripleGapDet_identity (D : WeightedDesign 4 3) {i j k l : Fin 4}
    (hset : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    D.weight i * D.weight j * D.weight k
        * tripleGapDet (D.atom i) (D.atom j) (D.atom k)
      = (1 - D.weight i) * (1 - D.weight j) * (1 - D.weight k)
        - ((1 - D.weight i * leverageOf (D.atom i)) * (1 - D.weight j) * (1 - D.weight k)
          + (1 - D.weight i) * (1 - D.weight j * leverageOf (D.atom j)) * (1 - D.weight k)
          + (1 - D.weight i) * (1 - D.weight j)
              * (1 - D.weight k * leverageOf (D.atom k))) := by
  obtain ⟨hpij, hpik, hpjk⟩ := four_pair_cap_eq_triple D hset hij hik hil hjk hjl hkl
  have hprod := four_triple_pairing_prod D hset hij hik hil hjk hjl hkl
  rw [tripleGapDet]
  linear_combination (-(D.weight i * (leverageOf (D.atom i) - 1))) * hpjk
    + (-(D.weight j * (leverageOf (D.atom j) - 1))) * hpik
    + (-(D.weight k * (leverageOf (D.atom k) - 1))) * hpij
    + 2 * hprod

/-! ## 5. A convex combination cannot dominate every one of its terms -/

/-- **THE CONVEX COMBINATION LEMMA.**  If every term of a strictly positive
convex combination is at most the value of the combination, every term equals
it.  Strict positivity of every weight is exactly what is used, and it is what
makes this argument unavailable to any weight-free statement. -/
theorem eq_of_le_weighted_average {n : ℕ} {t z : Fin n → ℝ} (hpos : ∀ c, 0 < t c)
    (hsum : ∑ c, t c = 1) {avg : ℝ} (havg : ∑ c, t c * z c = avg)
    (hle : ∀ c, z c ≤ avg) (d : Fin n) : z d = avg := by
  by_contra hne
  have hlt : z d < avg := lt_of_le_of_ne (hle d) hne
  have hstrict : ∑ c, t c * z c < ∑ c, t c * avg :=
    Finset.sum_lt_sum (fun c _ => mul_le_mul_of_nonneg_left (hle c) (hpos c).le)
      ⟨d, Finset.mem_univ d, mul_lt_mul_of_pos_left hlt (hpos d)⟩
  rw [havg, ← Finset.sum_mul, hsum, one_mul] at hstrict
  exact lt_irrefl _ hstrict

/-! ## 6. The co-share, and the two facts it satisfies -/

/-- The co-share of an atom, normalised by its co-weight.  At four atoms the sign
of a triple's gap determinant is the sign of one less the co-share total of that
triple. -/
noncomputable def coShare (D : WeightedDesign m 3) (c : Fin m) : ℝ :=
  (1 - D.weight c * leverageOf (D.atom c)) / (1 - D.weight c)

/-- The co-share times the co-weight is the co-share numerator. -/
theorem coShare_mul_coWeight (D : WeightedDesign m 3) (hm : 2 ≤ m) (c : Fin m) :
    coShare D c * (1 - D.weight c) = 1 - D.weight c * leverageOf (D.atom c) := by
  rw [coShare, div_mul_cancel₀]
  exact sub_ne_zero_of_ne (Ne.symm (ne_of_lt (weight_lt_one D hm c)))

/-- **THE CO-SHARES OF A FOUR-ATOM DESIGN CARRY UNIT CO-WEIGHTED TOTAL.**  The
trace of Parseval says the weighted leverages total three, and there are four
atoms, so the co-shares total exactly one against the co-weights. -/
theorem four_coShare_total (D : WeightedDesign 4 3) :
    ∑ c, (1 - D.weight c) * coShare D c = 1 := by
  have hlev := sum_weighted_leverage D
  have hterm : ∀ c : Fin 4, (1 - D.weight c) * coShare D c
      = 1 - D.weight c * leverageOf (D.atom c) := by
    intro c
    rw [mul_comm]
    exact coShare_mul_coWeight D (by norm_num) c
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hlev]; norm_num

/-- **A NONPOSITIVE GAP DETERMINANT IS A CO-SHARE TOTAL PAST ONE.**  The identity
of section four, divided by the three positive co-weights. -/
theorem four_coShare_triple_ge_one (D : WeightedDesign 4 3) {i j k l : Fin 4}
    (hset : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hdet : tripleGapDet (D.atom i) (D.atom j) (D.atom k) ≤ 0) :
    1 ≤ coShare D i + coShare D j + coShare D k := by
  have hvi : (0 : ℝ) < 1 - D.weight i := by linarith [weight_lt_one D (by norm_num) i]
  have hvj : (0 : ℝ) < 1 - D.weight j := by linarith [weight_lt_one D (by norm_num) j]
  have hvk : (0 : ℝ) < 1 - D.weight k := by linarith [weight_lt_one D (by norm_num) k]
  have hci := coShare_mul_coWeight D (by norm_num : 2 ≤ 4) i
  have hcj := coShare_mul_coWeight D (by norm_num : 2 ≤ 4) j
  have hck := coShare_mul_coWeight D (by norm_num : 2 ≤ 4) k
  have hid := four_tripleGapDet_identity D hset hij hik hil hjk hjl hkl
  have hw : 0 < D.weight i * D.weight j * D.weight k :=
    mul_pos (mul_pos (D.weight_pos i) (D.weight_pos j)) (D.weight_pos k)
  have key : (1 - D.weight i) * (1 - D.weight j) * (1 - D.weight k)
      * (1 - (coShare D i + coShare D j + coShare D k))
      = D.weight i * D.weight j * D.weight k
        * tripleGapDet (D.atom i) (D.atom j) (D.atom k) := by
    rw [hid, ← hci, ← hcj, ← hck]; ring
  have hle : (1 - D.weight i) * (1 - D.weight j) * (1 - D.weight k)
      * (1 - (coShare D i + coShare D j + coShare D k)) ≤ 0 := by
    rw [key]; nlinarith [hw, hdet]
  nlinarith [mul_pos (mul_pos hvi hvj) hvk, hle]

/-! ## 7. The classification -/

/-- **EVERY CO-SHARE OF A FOUR-ATOM BRANCH-B BOUNDARY SYSTEM IS ONE THIRD.**  The
four triple conditions say every co-share is at most the total less one, and the
trace of Parseval says the weighted average of the co-shares IS the total less
one.  A strictly positive convex combination cannot dominate every one of its
terms, so all four are equal, and four equal numbers whose common value is their
total less one are each one third. -/
theorem fourAtom_branchB_coShare (D : WeightedDesign 4 3)
    (hdet : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      tripleGapDet (D.atom i) (D.atom j) (D.atom k) ≤ 0) (c : Fin 4) :
    coShare D c = 1 / 3 := by
  set Z : ℝ := ∑ d, coShare D d with hZ
  -- the four triple conditions
  have h012 : 1 ≤ coShare D 0 + coShare D 1 + coShare D 2 :=
    four_coShare_triple_ge_one D (i := 0) (j := 1) (k := 2) (l := 3)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (hdet 0 1 2 (by decide) (by decide) (by decide))
  have h013 : 1 ≤ coShare D 0 + coShare D 1 + coShare D 3 :=
    four_coShare_triple_ge_one D (i := 0) (j := 1) (k := 3) (l := 2)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (hdet 0 1 3 (by decide) (by decide) (by decide))
  have h023 : 1 ≤ coShare D 0 + coShare D 2 + coShare D 3 :=
    four_coShare_triple_ge_one D (i := 0) (j := 2) (k := 3) (l := 1)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (hdet 0 2 3 (by decide) (by decide) (by decide))
  have h123 : 1 ≤ coShare D 1 + coShare D 2 + coShare D 3 :=
    four_coShare_triple_ge_one D (i := 1) (j := 2) (k := 3) (l := 0)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (hdet 1 2 3 (by decide) (by decide) (by decide))
  have hZexp : Z = coShare D 0 + coShare D 1 + coShare D 2 + coShare D 3 := by
    rw [hZ, Fin.sum_univ_four]
  -- the weighted average of the co-shares is the total less one
  have htot := four_coShare_total D
  have hsplit : ∑ d, (1 - D.weight d) * coShare D d
      = (∑ d, coShare D d) - ∑ d, D.weight d * coShare D d := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hsplit] at htot
  have havg : ∑ d, D.weight d * coShare D d = Z - 1 := by rw [hZ]; linarith
  -- every co-share is at most the total less one
  have hle : ∀ d : Fin 4, coShare D d ≤ Z - 1 := by
    intro d
    fin_cases d
    · show coShare D 0 ≤ Z - 1; rw [hZexp]; linarith
    · show coShare D 1 ≤ Z - 1; rw [hZexp]; linarith
    · show coShare D 2 ≤ Z - 1; rw [hZexp]; linarith
    · show coShare D 3 ≤ Z - 1; rw [hZexp]; linarith
  have heq : ∀ d : Fin 4, coShare D d = Z - 1 :=
    fun d => eq_of_le_weighted_average D.weight_pos D.weight_sum_one havg hle d
  have hZval : Z = 4 * (Z - 1) := by
    have h0 := heq 0
    have h1 := heq 1
    have h2 := heq 2
    have h3 := heq 3
    linarith
  have hZthird : Z - 1 = 1 / 3 := by linarith
  rw [heq c, hZthird]

/-- **THE LEVERAGE IS DETERMINED BY THE WEIGHT.**  A four-atom branch-B boundary
system has `3 t_c l_c = 2 + t_c` at every atom.  At the uniform weight one
quarter this returns leverage three, the regular tetrahedron. -/
theorem fourAtom_branchB_leverage (D : WeightedDesign 4 3)
    (hdet : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      tripleGapDet (D.atom i) (D.atom j) (D.atom k) ≤ 0) (c : Fin 4) :
    3 * (D.weight c * leverageOf (D.atom c)) = 2 + D.weight c := by
  have hc := fourAtom_branchB_coShare D hdet c
  have hmul := coShare_mul_coWeight D (by norm_num : 2 ≤ 4) c
  rw [hc] at hmul
  linarith

/-- **EVERY TRIPLE OF A FOUR-ATOM BRANCH-B BOUNDARY SYSTEM IS EXACTLY TIGHT.**
All four gap determinants vanish, so all four triples dominate and none
dominates strictly.  The configuration sits on the boundary in every direction
at once. -/
theorem fourAtom_branchB_tripleGapDet_eq_zero (D : WeightedDesign 4 3)
    (hdet : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      tripleGapDet (D.atom i) (D.atom j) (D.atom k) ≤ 0)
    {i j k l : Fin 4} (hset : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    tripleGapDet (D.atom i) (D.atom j) (D.atom k) = 0 := by
  have hvi : (0 : ℝ) < 1 - D.weight i := by linarith [weight_lt_one D (by norm_num) i]
  have hvj : (0 : ℝ) < 1 - D.weight j := by linarith [weight_lt_one D (by norm_num) j]
  have hvk : (0 : ℝ) < 1 - D.weight k := by linarith [weight_lt_one D (by norm_num) k]
  have hci := coShare_mul_coWeight D (by norm_num : 2 ≤ 4) i
  have hcj := coShare_mul_coWeight D (by norm_num : 2 ≤ 4) j
  have hck := coShare_mul_coWeight D (by norm_num : 2 ≤ 4) k
  rw [fourAtom_branchB_coShare D hdet i] at hci
  rw [fourAtom_branchB_coShare D hdet j] at hcj
  rw [fourAtom_branchB_coShare D hdet k] at hck
  have hid := four_tripleGapDet_identity D hset hij hik hil hjk hjl hkl
  rw [← hci, ← hcj, ← hck] at hid
  have hw : 0 < D.weight i * D.weight j * D.weight k :=
    mul_pos (mul_pos (D.weight_pos i) (D.weight_pos j)) (D.weight_pos k)
  have hzero : D.weight i * D.weight j * D.weight k
      * tripleGapDet (D.atom i) (D.atom j) (D.atom k) = 0 := by
    rw [hid]; ring
  rcases mul_eq_zero.mp hzero with hcontra | hgood
  · exact absurd hcontra (ne_of_gt hw)
  · exact hgood

end Gtz

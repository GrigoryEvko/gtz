import Gtz.Wave.OneAxisZeroAnchorCaps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# The determinant law of the outside triad: every recombination scales by the
# product of its coefficients

A `(6,3)` corner leaves exactly three outside atoms, and three rank-one atoms
in `ℝ³` obey an exact determinant law: ANY coefficient recombination of the
three atoms has determinant equal to the coefficient product times the
determinant of the plain sum (`Gtz.det_triad_recombination`),

  `det(c₁ q₁q₁ᵀ + c₂ q₂q₂ᵀ + c₃ q₃q₃ᵀ) = c₁c₂c₃ · det(q₁q₁ᵀ + q₂q₂ᵀ + q₃q₃ᵀ)`.

The whole one-parameter pencil between the weighted and unweighted outside
masses is therefore determinant-explicit
(`Gtz.outside_triad_char_identity`):

  `det(M_o − s·N_out) = (1 − s t_{d₁})(1 − s t_{d₂})(1 − s t_{d₃}) · det M_o`,

so the generalized eigenvalues of the pair `(N_out, M_o)` are EXACTLY the
three outside weights.  The campaign's outside payment `M_o ⪰ N_out/ms` is
the crude shadow of this law: at `s = 1/t_d` for any member `d` the pencil is
singular on the nose (`Gtz.outside_payment_det_sharp`).

## Parseval pins the outside determinant by inside data

The weighted outside mass is the identity minus the weighted inside mass, so
the det link (`Gtz.outside_triad_det_link`) becomes an exact pin
(`Gtz.corner_outside_det_pinned`):

  `t_{d₁} t_{d₂} t_{d₃} · det(S_{Cᶜ}) = det(1 − t_x G_x − t_y G_y − t_z G_z)`.

The right side is inside data only.  As the outside weights collapse, the
unweighted outside determinant blows up at exactly the inverse rate — the
quantitative content of the non-compact end where the `Z1` battery's
stragglers live.  Calibration: at `Gtz.oneAxisZeroWitness` both sides equal
`73568/8120601 · 64` in exact rationals.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The recombination law -/

/-- **THE TRIAD RECOMBINATION LAW.**  Any coefficient recombination of three
rank-one atoms of `ℝ³` has determinant equal to the coefficient product times
the determinant of the plain atom sum: the atoms factor through one `3×3`
matrix of rows, and the coefficients sit on a diagonal between it and its
transpose. -/
theorem det_triad_recombination (q₁ q₂ q₃ : Fin 3 → ℝ) (c : Fin 3 → ℝ) :
    (c 0 • atomMatrix q₁ + c 1 • atomMatrix q₂ + c 2 • atomMatrix q₃).det
      = c 0 * c 1 * c 2
        * (atomMatrix q₁ + atomMatrix q₂ + atomMatrix q₃).det := by
  set Q : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![q₁, q₂, q₃] with hQ
  have hrows : ∀ cv : Fin 3 → ℝ,
      Qᵀ * (Matrix.diagonal cv * Q)
        = cv 0 • atomMatrix q₁ + cv 1 • atomMatrix q₂ + cv 2 • atomMatrix q₃ := by
    intro cv
    ext i j
    have hentry : ∀ k : Fin 3, Qᵀ i k * (Matrix.diagonal cv * Q) k j
        = cv k * (Q k i * Q k j) := by
      intro k
      rw [Matrix.transpose_apply, Matrix.diagonal_mul]
      ring
    rw [Matrix.mul_apply, Finset.sum_congr rfl fun k _ => hentry k,
      Fin.sum_univ_three]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix,
      Matrix.vecMulVec_apply]
    have h0 : Q 0 = q₁ := rfl
    have h1 : Q 1 = q₂ := rfl
    have h2 : Q 2 = q₃ := rfl
    rw [h0, h1, h2]
  have hdet : ∀ cv : Fin 3 → ℝ,
      (cv 0 • atomMatrix q₁ + cv 1 • atomMatrix q₂ + cv 2 • atomMatrix q₃).det
        = cv 0 * cv 1 * cv 2 * (Qᵀ.det * Q.det) := by
    intro cv
    rw [← hrows cv, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
      Fin.prod_univ_three]
    ring
  have hone := hdet (fun _ => 1)
  simp only [one_smul, one_mul] at hone
  rw [hdet c, hone]

/-! ## 2. The three-member sum and product of the outside family -/

/-- A card-3 complement enumerated: the weighted outside mass, the unweighted
outside mass, and the weight product, all as three-term expressions. -/
theorem outside_triad_det_link (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hCc : (Cᶜ : Finset (Fin m)).card = 3) :
    (∑ d ∈ (Cᶜ : Finset (Fin m)), D.weight d • atomMatrix (D.atom d)).det
      = (∏ d ∈ (Cᶜ : Finset (Fin m)), D.weight d) * (subsetSum D Cᶜ).det := by
  classical
  obtain ⟨d₁, d₂, d₃, h12, h13, h23, hset⟩ := Finset.card_eq_three.mp hCc
  have hw : ∑ d ∈ (Cᶜ : Finset (Fin m)), D.weight d • atomMatrix (D.atom d)
      = D.weight d₁ • atomMatrix (D.atom d₁)
        + D.weight d₂ • atomMatrix (D.atom d₂)
        + D.weight d₃ • atomMatrix (D.atom d₃) := by
    rw [hset, sum_triple_eq h12 h13 h23]
    abel
  have hu : subsetSum D Cᶜ
      = atomMatrix (D.atom d₁) + atomMatrix (D.atom d₂)
        + atomMatrix (D.atom d₃) := by
    rw [subsetSum, hset, sum_triple_eq h12 h13 h23]
    abel
  have hp : ∏ d ∈ (Cᶜ : Finset (Fin m)), D.weight d
      = D.weight d₁ * D.weight d₂ * D.weight d₃ := by
    rw [hset,
      show ({d₁, d₂, d₃} : Finset (Fin m)) = insert d₁ (insert d₂ {d₃}) from rfl,
      Finset.prod_insert (by simp [h12, h13]),
      Finset.prod_insert (by simp [h23]), Finset.prod_singleton, mul_assoc]
  have hcore := det_triad_recombination (D.atom d₁) (D.atom d₂) (D.atom d₃)
    ![D.weight d₁, D.weight d₂, D.weight d₃]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hcore
  rw [hw, hu, hp, hcore, mul_assoc]

/-- **THE CHARACTERISTIC IDENTITY OF THE OUTSIDE PENCIL.**  The determinant of
the pencil between the unweighted and weighted outside masses factors through
the outside weights: the generalized eigenvalues of `(N_out, M_o)` are the
weights themselves. -/
theorem outside_triad_char_identity (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hCc : (Cᶜ : Finset (Fin m)).card = 3) (s : ℝ) :
    (subsetSum D Cᶜ
        - s • ∑ d ∈ (Cᶜ : Finset (Fin m)), D.weight d • atomMatrix (D.atom d)).det
      = (∏ d ∈ (Cᶜ : Finset (Fin m)), (1 - s * D.weight d))
          * (subsetSum D Cᶜ).det := by
  classical
  obtain ⟨d₁, d₂, d₃, h12, h13, h23, hset⟩ := Finset.card_eq_three.mp hCc
  have hpencil : subsetSum D Cᶜ
      - s • ∑ d ∈ (Cᶜ : Finset (Fin m)), D.weight d • atomMatrix (D.atom d)
      = (1 - s * D.weight d₁) • atomMatrix (D.atom d₁)
        + (1 - s * D.weight d₂) • atomMatrix (D.atom d₂)
        + (1 - s * D.weight d₃) • atomMatrix (D.atom d₃) := by
    rw [subsetSum, hset, sum_triple_eq h12 h13 h23, sum_triple_eq h12 h13 h23,
      smul_add, smul_add, smul_smul, smul_smul, smul_smul,
      sub_smul, sub_smul, sub_smul, one_smul, one_smul, one_smul]
    abel
  have hu : subsetSum D Cᶜ
      = atomMatrix (D.atom d₁) + atomMatrix (D.atom d₂)
        + atomMatrix (D.atom d₃) := by
    rw [subsetSum, hset, sum_triple_eq h12 h13 h23]
    abel
  have hp : ∏ d ∈ (Cᶜ : Finset (Fin m)), (1 - s * D.weight d)
      = (1 - s * D.weight d₁) * (1 - s * D.weight d₂)
        * (1 - s * D.weight d₃) := by
    rw [hset,
      show ({d₁, d₂, d₃} : Finset (Fin m)) = insert d₁ (insert d₂ {d₃}) from rfl,
      Finset.prod_insert (by simp [h12, h13]),
      Finset.prod_insert (by simp [h23]), Finset.prod_singleton, mul_assoc]
  have hcore := det_triad_recombination (D.atom d₁) (D.atom d₂) (D.atom d₃)
    ![1 - s * D.weight d₁, 1 - s * D.weight d₂, 1 - s * D.weight d₃]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hcore
  rw [hpencil, hu, hp, hcore]

/-! ## 3. The payment is determinant-sharp -/

/-- **THE PAYMENT IS DET-SHARP.**  Scaling the unweighted outside mass by ANY
member weight and subtracting the weighted mass gives a singular matrix: the
outside payment `M_o ⪰ N_out/ms` touches at every member weight. -/
theorem outside_payment_det_sharp (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hCc : (Cᶜ : Finset (Fin m)).card = 3) {d₀ : Fin m} (hd₀ : d₀ ∈ (Cᶜ : Finset (Fin m))) :
    (D.weight d₀ • subsetSum D Cᶜ
        - ∑ d ∈ (Cᶜ : Finset (Fin m)), D.weight d • atomMatrix (D.atom d)).det
      = 0 := by
  classical
  obtain ⟨d₁, d₂, d₃, h12, h13, h23, hset⟩ := Finset.card_eq_three.mp hCc
  have hpencil : D.weight d₀ • subsetSum D Cᶜ
      - ∑ d ∈ (Cᶜ : Finset (Fin m)), D.weight d • atomMatrix (D.atom d)
      = (D.weight d₀ - D.weight d₁) • atomMatrix (D.atom d₁)
        + (D.weight d₀ - D.weight d₂) • atomMatrix (D.atom d₂)
        + (D.weight d₀ - D.weight d₃) • atomMatrix (D.atom d₃) := by
    rw [subsetSum, hset, sum_triple_eq h12 h13 h23, sum_triple_eq h12 h13 h23,
      smul_add, smul_add, sub_smul, sub_smul, sub_smul]
    abel
  have hcore := det_triad_recombination (D.atom d₁) (D.atom d₂) (D.atom d₃)
    ![D.weight d₀ - D.weight d₁, D.weight d₀ - D.weight d₂,
      D.weight d₀ - D.weight d₃]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hcore
  rw [hpencil, hcore]
  have hd0 : d₀ = d₁ ∨ d₀ = d₂ ∨ d₀ = d₃ := by
    have := hset ▸ hd₀
    simpa using this
  rcases hd0 with rfl | rfl | rfl
  · simp
  · simp
  · simp

/-! ## 4. Parseval pins the outside determinant -/

/-- **THE OUTSIDE DETERMINANT IS PINNED BY INSIDE DATA.**  At any corner of a
`(6,3)` design, the product of the outside weights times the unweighted
outside determinant is the determinant of the identity minus the weighted
inside mass — an exact identity, no gap or tie hypothesis.  As the outside
weights collapse, `det S_{Cᶜ}` blows up at exactly the inverse rate. -/
theorem corner_outside_det_pinned (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    (hC : C.card = 3) :
    (∏ d ∈ (Cᶜ : Finset (Fin 6)), D.weight d) * (subsetSum D Cᶜ).det
      = ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - ∑ c ∈ C, D.weight c • atomMatrix (D.atom c)).det := by
  classical
  have hCc : (Cᶜ : Finset (Fin 6)).card = 3 :=
    card_compl_eq_three_of_card_eq_three C hC
  have hsplit := Finset.sum_add_sum_compl C
    (fun c => D.weight c • atomMatrix (D.atom c))
  rw [D.isParseval] at hsplit
  have hout : ∑ d ∈ (Cᶜ : Finset (Fin 6)), D.weight d • atomMatrix (D.atom d)
      = (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - ∑ c ∈ C, D.weight c • atomMatrix (D.atom c) := by
    rw [← hsplit]
    abel
  rw [← hout, outside_triad_det_link D C hCc]

end Gtz

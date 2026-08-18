import Gtz.Wave.CorankTwoPlanarRigidity
import Gtz.Wave.CorankTwoClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The planar corner reads isotropically, and the tie prices every pair

The planar rigidity (`Gtz.planar_insideWeights_eq_and_lam_gt_two`) pins every
inside weight of a primitive planar corank-two tie at `1/(1 + lam)` with
`lam > 2`.  This module cashes that rigidity into the three instruments the
closure consumes.

* **Isotropy.**  With equal inside weights the outside weighted plane matrix
  is a multiple of the plane identity: against every `w ⊥ u`,
  `(1+lam)·Σ_{d∉C} t_d (g_d·w)² = lam·|w|²` — an exact identity, not a bound.
* **The reading floor.**  At every plane direction some outside atom reads at
  least `lam/(lam-2) > 1` times the norm.  No direction is quiet: the planar
  corner cannot hide outside mass.
* **The thin-witness reading.**  When a pair of outside atoms is thin at a
  witness `w` — their readings sum below the norm — the omitted outside atom
  must read at least `(2 + (1+lam) t_k)/((1+lam) t_k)` times the norm there.
* **The alignment witness.**  The tie's refusal of a one-shared triple with a
  heavy inside atom hands a witness direction where the outside pair's plane
  cover is capped by the inside atom's plane reading — and Cauchy–Schwarz
  turns the cap into the pair-near-thinness inequality
  `(β² - 1)(Q(w) - |w|²) ≤ (ℓ_e - β²)|w|²`.

## Calibration — the pigeonhole at the fixture, both sides exact

The parent brief's pigeonhole `(lam-2)·det(Q_k - I) ≤ tr Q_k - 2` is a
NECESSARY condition for a planar corank-two tie (derived by summing the
alignment refusals over the heavy inside atoms against the inside plane
Parseval; verified on paper, landed here in witness form).  At the landed
non-tie fixture `Gtz.corankTwoPlanarDesign` it is VIOLATED, in exact
rationals: for the pair `{4,5}` the invariant form reads

  `(3-2) · det(Q - I) = 24  >  11 = tr Q - 2` ,

matching the fixture's strict triple `{0,4,5}`
(`Gtz.corankTwoPlanar_oneShared_strict`) — the instrument detects the non-tie
exactly where the strict dominator lives.  `Gtz.corankTwoPlanar_pigeonhole_violation`
records both sides in kernel through the fixture's atoms, using the frame-free
2×2 invariants `det(Q - I) = det Q - tr Q + 1`, `det Q = |q_i|²|q_j|² - (q_i·q_j)²`.

Nothing in this module can be stated at `(5,3)`: every statement quantifies
over three outside atoms.
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. Isotropy -/

/-- **The outside plane reading is isotropic.**  Equal inside weights force
`(1+lam)·Σ_{d∉C} t_d (g_d·w)² = lam·|w|²` at every `w ⊥ u`. -/
theorem outside_isotropy_of_planar (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} (hlam : 0 ≤ lam) {u w : Fin 3 → ℝ}
    (hw : w ⬝ᵥ u = 0) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (heq : ∀ e ∈ C, D.weight e = 1 / (1 + lam)) :
    (1 + lam) * ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ w) ^ 2
      = lam * (w ⬝ᵥ w) := by
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have htotal := dotProduct_self_eq_sum_weight_mul_sq D w
  rw [← Finset.sum_add_sum_compl C] at htotal
  have hin : ∑ e ∈ C, D.weight e * (D.atom e ⬝ᵥ w) ^ 2
      = (1 / (1 + lam)) * (w ⬝ᵥ w) := by
    have hplane := planeMass_of_rankOneGap D C hw hgap
    calc ∑ e ∈ C, D.weight e * (D.atom e ⬝ᵥ w) ^ 2
        = ∑ e ∈ C, (1 / (1 + lam)) * (D.atom e ⬝ᵥ w) ^ 2 :=
          Finset.sum_congr rfl fun e he => by rw [heq e he]
      _ = (1 / (1 + lam)) * ∑ e ∈ C, (D.atom e ⬝ᵥ w) ^ 2 := by
          rw [Finset.mul_sum]
      _ = (1 / (1 + lam)) * (w ⬝ᵥ w) := by rw [hplane]
  rw [hin] at htotal
  field_simp at htotal ⊢
  linarith

/-- The outside weight total under equal inside weights:
`(1+lam)·Σ_{d∉C} t_d = lam - 2` at `(6,3)`. -/
theorem outside_weight_total_of_planar (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    (heq : ∀ e ∈ C, D.weight e = 1 / (1 + lam)) :
    (1 + lam) * ∑ d ∈ Cᶜ, D.weight d = lam - 2 := by
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have hsum := D.weight_sum_one
  rw [← Finset.sum_add_sum_compl C] at hsum
  have hin : ∑ e ∈ C, D.weight e = 3 * (1 / (1 + lam)) := by
    rw [Finset.sum_congr rfl heq, Finset.sum_const, hcard]
    simp [mul_comm]
  rw [hin] at hsum
  field_simp at hsum ⊢
  linarith

/-! ## 2. The reading floor -/

/-- **No plane direction is quiet.**  At every `w ⊥ u` some outside atom
reads at least `lam/(lam-2)` times the norm — strictly above it. -/
theorem exists_outside_reading_floor (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} (hlam : 2 < lam)
    {u w : Fin 3 → ℝ} (hw : w ⬝ᵥ u = 0)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (heq : ∀ e ∈ C, D.weight e = 1 / (1 + lam)) :
    ∃ d ∈ Cᶜ, lam * (w ⬝ᵥ w) ≤ (lam - 2) * (D.atom d ⬝ᵥ w) ^ 2 := by
  by_contra hcon
  push_neg at hcon
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have hiso := outside_isotropy_of_planar D C (by linarith) hw hgap heq
  have htot := outside_weight_total_of_planar D C hcard (by linarith) heq
  have hne : (Cᶜ : Finset (Fin 6)).Nonempty :=
    Finset.card_pos.mp
      (by rw [card_compl_eq_three_of_card_eq_three C hcard]; norm_num)
  have hstrict : ∑ d ∈ Cᶜ, D.weight d * ((lam - 2) * (D.atom d ⬝ᵥ w) ^ 2)
      < ∑ d ∈ Cᶜ, D.weight d * (lam * (w ⬝ᵥ w)) := by
    refine Finset.sum_lt_sum_of_nonempty hne fun d hd => ?_
    exact mul_lt_mul_of_pos_left (hcon d hd) (D.weight_pos d)
  have hlhs : ∑ d ∈ Cᶜ, D.weight d * ((lam - 2) * (D.atom d ⬝ᵥ w) ^ 2)
      = (lam - 2) * ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ w) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  have hrhs : ∑ d ∈ Cᶜ, D.weight d * (lam * (w ⬝ᵥ w))
      = (∑ d ∈ Cᶜ, D.weight d) * (lam * (w ⬝ᵥ w)) := by
    rw [Finset.sum_mul]
  rw [hlhs, hrhs] at hstrict
  have h1 := mul_lt_mul_of_pos_left hstrict hone
  have e1 : (1 + lam) * ((lam - 2)
        * ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ w) ^ 2)
      = (lam - 2)
        * ((1 + lam) * ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ w) ^ 2) := by
    ring
  have e2 : (1 + lam) * ((∑ d ∈ Cᶜ, D.weight d) * (lam * (w ⬝ᵥ w)))
      = ((1 + lam) * ∑ d ∈ Cᶜ, D.weight d) * (lam * (w ⬝ᵥ w)) := by
    ring
  rw [e1, e2, hiso, htot] at h1
  exact absurd h1 (lt_irrefl _)

/-! ## 3. The thin-witness reading -/

/-- **A thin pair concentrates the witness on the omitted atom.**  When the
readings of two outside atoms sum below the norm at `w`, the third outside
atom carries the isotropy there:
`(2 + (1+lam) t_k)·|w|² ≤ (1+lam)·t_k·(g_k·w)²`. -/
theorem thin_witness_omitted_reading (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} (hlam : 2 < lam)
    {u w : Fin 3 → ℝ} (hw : w ⬝ᵥ u = 0)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (heq : ∀ e ∈ C, D.weight e = 1 / (1 + lam))
    {i j dk : Fin 6} (hi : i ∈ Cᶜ) (hj : j ∈ Cᶜ) (hk : dk ∈ Cᶜ)
    (hij : i ≠ j) (hik : i ≠ dk) (hjk : j ≠ dk)
    (hthin : (D.atom i ⬝ᵥ w) ^ 2 + (D.atom j ⬝ᵥ w) ^ 2 ≤ w ⬝ᵥ w) :
    (2 + (1 + lam) * D.weight dk) * (w ⬝ᵥ w)
      ≤ (1 + lam) * (D.weight dk * (D.atom dk ⬝ᵥ w) ^ 2) := by
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have hCc : Cᶜ = ({i, j, dk} : Finset (Fin 6)) := by
    have hsub : ({i, j, dk} : Finset (Fin 6)) ⊆ Cᶜ := by
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact hk
    have hcardijk : ({i, j, dk} : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hij, hik]),
        Finset.card_insert_of_notMem (by simp [hjk]),
        Finset.card_singleton]
    exact (Finset.eq_of_subset_of_card_le hsub
      (by rw [card_compl_eq_three_of_card_eq_three C hcard, hcardijk])).symm
  have hiso := outside_isotropy_of_planar D C (by linarith) hw hgap heq
  rw [hCc, Finset.sum_insert (by simp [hij, hik]),
    Finset.sum_insert (by simp [hjk]), Finset.sum_singleton] at hiso
  have htot := outside_weight_total_of_planar D C hcard (by linarith) heq
  rw [hCc, Finset.sum_insert (by simp [hij, hik]),
    Finset.sum_insert (by simp [hjk]), Finset.sum_singleton] at htot
  have hwsq : 0 ≤ w ⬝ᵥ w := dotProduct_self_nonneg w
  have hisq : (D.atom i ⬝ᵥ w) ^ 2 ≤ w ⬝ᵥ w := by
    nlinarith [sq_nonneg (D.atom j ⬝ᵥ w)]
  have hjsq : (D.atom j ⬝ᵥ w) ^ 2 ≤ w ⬝ᵥ w := by
    nlinarith [sq_nonneg (D.atom i ⬝ᵥ w)]
  have hibound : D.weight i * (D.atom i ⬝ᵥ w) ^ 2
      ≤ D.weight i * (w ⬝ᵥ w) :=
    mul_le_mul_of_nonneg_left hisq (D.weight_pos i).le
  have hjbound : D.weight j * (D.atom j ⬝ᵥ w) ^ 2
      ≤ D.weight j * (w ⬝ᵥ w) :=
    mul_le_mul_of_nonneg_left hjsq (D.weight_pos j).le
  have hPA := mul_le_mul_of_nonneg_left hibound hone.le
  have hPB := mul_le_mul_of_nonneg_left hjbound hone.le
  have htotw : ((1 + lam) * (D.weight i + (D.weight j + D.weight dk)))
        * (w ⬝ᵥ w)
      = (lam - 2) * (w ⬝ᵥ w) := by
    rw [htot]
  linarith [hiso, htotw, hPA, hPB]

/-! ## 4. The alignment witness -/

/-- **The tie's refusal of a one-shared triple with a heavy inside atom hands
an alignment witness**: a plane direction where the pair's cover above the
norm is capped by the inside atom's plane reading. -/
theorem alignment_witness_of_isTie_planar (D : WeightedDesign 6 3)
    (htie : IsTie D) (C : Finset (Fin 6)) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (houtside : ∀ d ∈ Cᶜ, D.atom d ⬝ᵥ u = 0)
    {e i j : Fin 6} (he : e ∈ C) (hi : i ∈ Cᶜ) (hj : j ∈ Cᶜ) (hij : i ≠ j)
    (hheavy : 1 < (D.atom e ⬝ᵥ u) ^ 2) :
    ∃ w : Fin 3 → ℝ, w ⬝ᵥ u = 0 ∧ w ≠ 0
      ∧ ((D.atom e ⬝ᵥ u) ^ 2 - 1)
            * ((D.atom i ⬝ᵥ w) ^ 2 + (D.atom j ⬝ᵥ w) ^ 2 - w ⬝ᵥ w)
          ≤ (D.atom e ⬝ᵥ w) ^ 2 := by
  classical
  have hei : e ≠ i := fun h => (Finset.mem_compl.mp hi) (h ▸ he)
  have hej : e ≠ j := fun h => (Finset.mem_compl.mp hj) (h ▸ he)
  have henotin : e ∉ ({i, j} : Finset (Fin 6)) := by simp [hei, hej]
  have hinotin : i ∉ ({j} : Finset (Fin 6)) := by simp [hij]
  have hcardT : (insert e ({i, j} : Finset (Fin 6))).card = 3 := by
    rw [Finset.card_insert_of_notMem henotin,
      Finset.card_insert_of_notMem hinotin, Finset.card_singleton]
  have hsplit := uMass_le_or_planeWitness_of_isTie D htie
    (insert e ({i, j} : Finset (Fin 6))) hcardT hunit
  have huMass : ∑ c ∈ insert e ({i, j} : Finset (Fin 6)),
      (D.atom c ⬝ᵥ u) ^ 2 = (D.atom e ⬝ᵥ u) ^ 2 := by
    rw [Finset.sum_insert henotin, Finset.sum_insert hinotin,
      Finset.sum_singleton, houtside i hi, houtside j hj]
    ring
  rcases hsplit with hle | ⟨w, hw, hwne, hbeat⟩
  · rw [huMass] at hle
    linarith
  · refine ⟨w, hw, hwne, ?_⟩
    rw [huMass] at hbeat
    have hcross : ∑ c ∈ insert e ({i, j} : Finset (Fin 6)),
        (D.atom c ⬝ᵥ u) * (D.atom c ⬝ᵥ w)
          = (D.atom e ⬝ᵥ u) * (D.atom e ⬝ᵥ w) := by
      rw [Finset.sum_insert henotin, Finset.sum_insert hinotin,
        Finset.sum_singleton, houtside i hi, houtside j hj]
      ring
    have hplane : ∑ c ∈ insert e ({i, j} : Finset (Fin 6)),
        (D.atom c ⬝ᵥ w) ^ 2
          = (D.atom e ⬝ᵥ w) ^ 2 + (D.atom i ⬝ᵥ w) ^ 2
            + (D.atom j ⬝ᵥ w) ^ 2 := by
      rw [Finset.sum_insert henotin, Finset.sum_insert hinotin,
        Finset.sum_singleton]
      ring
    rw [hcross, hplane] at hbeat
    nlinarith [hbeat, hheavy, sq_nonneg (D.atom e ⬝ᵥ w)]

/-- **The plane Cauchy–Schwarz cap.**  A reading against a plane direction is
bounded by the atom's plane norm: `(g·w)² ≤ (|g|² - (g·u)²)·|w|²`. -/
theorem planeReading_sq_le (g : Fin 3 → ℝ) {u w : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hw : w ⬝ᵥ u = 0) :
    (g ⬝ᵥ w) ^ 2 ≤ (g ⬝ᵥ g - (g ⬝ᵥ u) ^ 2) * (w ⬝ᵥ w) := by
  have huw : u ⬝ᵥ w = 0 := by rwa [dotProduct_comm] at hw
  have hpw : (g - (g ⬝ᵥ u) • u) ⬝ᵥ w = g ⬝ᵥ w := by
    rw [sub_dotProduct, smul_dotProduct, huw, smul_eq_mul, mul_zero, sub_zero]
  have hpp : (g - (g ⬝ᵥ u) • u) ⬝ᵥ (g - (g ⬝ᵥ u) • u)
      = g ⬝ᵥ g - (g ⬝ᵥ u) ^ 2 := by
    rw [sub_dotProduct, smul_dotProduct, dotProduct_sub, dotProduct_sub,
      dotProduct_smul, dotProduct_smul, hunit, dotProduct_comm u g]
    simp only [smul_eq_mul]
    ring
  have hcs := dotProduct_sq_le_mul (g - (g ⬝ᵥ u) • u) w
  rw [hpw, hpp] at hcs
  exact hcs

/-- **The pair-near-thinness cap.**  Combining the alignment witness with
Cauchy–Schwarz: every outside pair has a plane direction where its cover
above the norm is capped by the heavy atom's plane mass over its surplus. -/
theorem pair_witness_cap (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (houtside : ∀ d ∈ Cᶜ, D.atom d ⬝ᵥ u = 0)
    {e i j : Fin 6} (he : e ∈ C) (hi : i ∈ Cᶜ) (hj : j ∈ Cᶜ) (hij : i ≠ j)
    (hheavy : 1 < (D.atom e ⬝ᵥ u) ^ 2) :
    ∃ w : Fin 3 → ℝ, w ⬝ᵥ u = 0 ∧ w ≠ 0
      ∧ ((D.atom e ⬝ᵥ u) ^ 2 - 1)
            * ((D.atom i ⬝ᵥ w) ^ 2 + (D.atom j ⬝ᵥ w) ^ 2 - w ⬝ᵥ w)
          ≤ (D.atom e ⬝ᵥ D.atom e - (D.atom e ⬝ᵥ u) ^ 2) * (w ⬝ᵥ w) := by
  obtain ⟨w, hw, hwne, hcap⟩ := alignment_witness_of_isTie_planar D htie C
    hunit houtside he hi hj hij hheavy
  exact ⟨w, hw, hwne, hcap.trans (planeReading_sq_le (D.atom e) hunit hw)⟩

/-! ## 5. Calibration: the pigeonhole at the fixture, both sides exact -/

/-- **THE PIGEONHOLE IS VIOLATED AT THE FIXTURE, IN KERNEL.**  For the outside
pair `{4, 5}` of `Gtz.corankTwoPlanarDesign` the tie-necessary inequality
`(lam-2)·det(Q - I) ≤ tr Q - 2` reads `24 ≤ 11` and fails — the instrument
certifies the non-tie exactly where the strict triple `{0,4,5}` lives.  The
2×2 invariants are frame-free: `det(Q - I) = det Q - tr Q + 1` with
`det Q = |q_i|²|q_j|² - (q_i·q_j)²` and `tr Q = |q_i|² + |q_j|²`. -/
theorem corankTwoPlanar_pigeonhole_violation :
    ((3 : ℝ) - 2)
        * ((corankTwoPlanarDesign.atom 4 ⬝ᵥ corankTwoPlanarDesign.atom 4)
              * (corankTwoPlanarDesign.atom 5 ⬝ᵥ corankTwoPlanarDesign.atom 5)
            - (corankTwoPlanarDesign.atom 4 ⬝ᵥ corankTwoPlanarDesign.atom 5) ^ 2
            - ((corankTwoPlanarDesign.atom 4 ⬝ᵥ corankTwoPlanarDesign.atom 4)
              + (corankTwoPlanarDesign.atom 5 ⬝ᵥ corankTwoPlanarDesign.atom 5))
            + 1)
      = 24
    ∧ (corankTwoPlanarDesign.atom 4 ⬝ᵥ corankTwoPlanarDesign.atom 4)
        + (corankTwoPlanarDesign.atom 5 ⬝ᵥ corankTwoPlanarDesign.atom 5) - 2
      = 11
    ∧ ¬ (((3 : ℝ) - 2)
        * ((corankTwoPlanarDesign.atom 4 ⬝ᵥ corankTwoPlanarDesign.atom 4)
              * (corankTwoPlanarDesign.atom 5 ⬝ᵥ corankTwoPlanarDesign.atom 5)
            - (corankTwoPlanarDesign.atom 4 ⬝ᵥ corankTwoPlanarDesign.atom 5) ^ 2
            - ((corankTwoPlanarDesign.atom 4 ⬝ᵥ corankTwoPlanarDesign.atom 4)
              + (corankTwoPlanarDesign.atom 5 ⬝ᵥ corankTwoPlanarDesign.atom 5))
            + 1)
      ≤ (corankTwoPlanarDesign.atom 4 ⬝ᵥ corankTwoPlanarDesign.atom 4)
          + (corankTwoPlanarDesign.atom 5 ⬝ᵥ corankTwoPlanarDesign.atom 5)
          - 2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [corankTwoPlanarDesign_atom, corankTwoPlanarAtom, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

end Gtz

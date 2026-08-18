import Gtz.Wave.CorankTwoIsotropy
import Gtz.LinAlg.PlaneTwoForm
import Gtz.LinAlg.PlaneSpread
import Gtz.LinAlg.PlanarCaseInequalities

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The planar corank-two corner is empty

A primitive `(6,3)` tie whose gap at a dominator `C` is `lam • u uᵀ` with
every outside atom orthogonal to `u` does not exist
(`Gtz.corankTwoPlanar_absurd`).

## The proof

The planar rigidity pins the inside weights at `1/(1+lam)` and forces
`lam > 2`; the outside then satisfies an exact isotropy.  Write `q₁ q₂ q₃`
for the outside atoms, `T_d` for their scaled weights, `Δ` for the plane
determinant of the outside gap `R = Σ q qᵀ − I`, and
`L_d = Φ_R(u ⨯₃ q_d)` for the turned self-readings.  Three exact ledgers
close the system:

* the trace ledger `Σ T_d ℓ_d = 2 lam`;
* the isotropy read at every outside atom pair;
* the determinant ledger `Σ (lam − T_d) L_d = 2 lam Δ`.

The pair omitting `q_d` has gap determinant `Δ − L_d`, so the tie's twenty
refusals leave exactly one dichotomy per outside pair: `L_d ≥ Δ` (a thin
pair, priced by the Gram identity of the two-form kit), or the pair form is
positive definite and the tie's alignment witnesses aggregate — through the
heavy inside atoms and the inside plane Parseval — into the pigeonhole
`(lam−2)·(Δ − L_d) ≤ tr`.  Conjugating the isotropy by the outside gap
(the vectors `x_d = adj R · q_d`, tamed by the Cayley–Hamilton identity of
the planar Gram) turns the pigeonhole into one polynomial inequality per
fat pair.  `Gtz/LinAlg/PlanarCaseInequalities.lean` refutes every sign
pattern of the dichotomy, so no planar corner survives.

The corner needs three outside atoms, so nothing here can be stated at
`(5,3)`: there is no diamond hazard, by construction.
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The polarized isotropy -/

/-- **The polarized outside isotropy.**  Squares polarize: the weighted
outside readings of two plane directions multiply to the plane dot. -/
theorem outside_isotropy_polar (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} (hlam : 0 ≤ lam) {u v w : Fin 3 → ℝ}
    (hv : v ⬝ᵥ u = 0) (hw : w ⬝ᵥ u = 0)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (heq : ∀ e ∈ C, D.weight e = 1 / (1 + lam)) :
    (1 + lam) * ∑ d ∈ Cᶜ, D.weight d * ((D.atom d ⬝ᵥ v) * (D.atom d ⬝ᵥ w))
      = lam * (v ⬝ᵥ w) := by
  have hvw : (v + w) ⬝ᵥ u = 0 := by rw [add_dotProduct, hv, hw]; ring
  have hvw' : (v - w) ⬝ᵥ u = 0 := by rw [sub_dotProduct, hv, hw]; ring
  have hplus := outside_isotropy_of_planar D C hlam hvw hgap heq
  have hminus := outside_isotropy_of_planar D C hlam hvw' hgap heq
  have hsum : ∀ d : Fin m,
      (D.atom d ⬝ᵥ (v + w)) ^ 2 - (D.atom d ⬝ᵥ (v - w)) ^ 2
        = 4 * ((D.atom d ⬝ᵥ v) * (D.atom d ⬝ᵥ w)) := by
    intro d
    rw [dotProduct_add, dotProduct_sub]
    ring
  have hnorm : (v + w) ⬝ᵥ (v + w) - (v - w) ⬝ᵥ (v - w) = 4 * (v ⬝ᵥ w) := by
    simp only [dotProduct_add, dotProduct_sub, add_dotProduct, sub_dotProduct]
    rw [dotProduct_comm w v]
    ring
  have hdiff : ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ (v + w)) ^ 2
      - ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ (v - w)) ^ 2
      = 4 * ∑ d ∈ Cᶜ, D.weight d * ((D.atom d ⬝ᵥ v) * (D.atom d ⬝ᵥ w)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← mul_sub, hsum d]
    ring
  nlinarith [hplus, hminus, hdiff, hnorm]

/-! ## 2. The fat-pair pigeonhole -/

/-- **The fat-pair pigeonhole.**  At a primitive planar corank-two `(6,3)`
tie, an outside pair whose gap form is positive definite on the plane obeys
`(lam−2) · det(Q−I) ≤ tr Q − 2`: the tie's alignment witnesses at the heavy
inside atoms, priced by the Gram identity, aggregate against the inside
plane Parseval. -/
theorem planar_fatPair_pigeonhole (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (houtside : ∀ d ∈ Cᶜ, D.atom d ⬝ᵥ u = 0)
    {i j : Fin 6} (hi : i ∈ Cᶜ) (hj : j ∈ Cᶜ) (hij : i ≠ j)
    (hfat : ∀ w : Fin 3 → ℝ, w ⬝ᵥ u = 0 → w ≠ 0 →
      0 < (D.atom i ⬝ᵥ w) ^ 2 + (D.atom j ⬝ᵥ w) ^ 2 - w ⬝ᵥ w)
    (hdet : 0 ≤ (u ⬝ᵥ D.atom i ⨯₃ D.atom j) ^ 2
        - (D.atom i ⬝ᵥ D.atom i + D.atom j ⬝ᵥ D.atom j) + 1) :
    (lam - 2) * ((u ⬝ᵥ D.atom i ⨯₃ D.atom j) ^ 2
        - (D.atom i ⬝ᵥ D.atom i + D.atom j ⬝ᵥ D.atom j) + 1)
      ≤ D.atom i ⬝ᵥ D.atom i + D.atom j ⬝ᵥ D.atom j - 2 := by
  classical
  have hqiu : D.atom i ⬝ᵥ u = 0 := houtside i hi
  have hqju : D.atom j ⬝ᵥ u = 0 := houtside j hj
  -- the per-atom priced floor, valid at every inside atom
  have hfloor : ∀ e ∈ C,
      ((D.atom e ⬝ᵥ u) ^ 2 - 1)
          * ((u ⬝ᵥ D.atom i ⨯₃ D.atom j) ^ 2
              - (D.atom i ⬝ᵥ D.atom i + D.atom j ⬝ᵥ D.atom j) + 1)
        ≤ (D.atom i ⬝ᵥ (u ⨯₃ D.atom e)) ^ 2
          + (D.atom j ⬝ᵥ (u ⨯₃ D.atom e)) ^ 2
          - (D.atom e ⬝ᵥ D.atom e - (D.atom e ⬝ᵥ u) ^ 2) := by
    intro e he
    by_cases hheavy : 1 < (D.atom e ⬝ᵥ u) ^ 2
    · -- a heavy atom is priced by its alignment witness
      obtain ⟨w, hw, hwne, hcap⟩ := alignment_witness_of_isTie_planar D htie C
        hunit houtside he hi hj hij hheavy
      have hkit := threeForm_turn_floor (u := u) (x := D.atom i)
        (y := D.atom j) (z := 0) (q := D.atom e) (w := w)
        (c := (D.atom e ⬝ᵥ u) ^ 2 - 1) hunit hqiu hqju
        (by simp) hw ?_ ?_ ?_
      · norm_num only [map_zero, LinearMap.zero_apply, dotProduct_zero,
          zero_dotProduct] at hkit
        linarith [hkit]
      · -- the witness inequality, with the zero third atom
        simpa using hcap
      · -- the pair form is positive at the witness
        have := hfat w hw hwne
        simpa using this
      · -- the pair determinant invariant, with the zero third atom
        simpa using hdet
    · -- a light atom contributes a nonpositive left side
      push_neg at hheavy
      have hval : 0 ≤ (D.atom i ⬝ᵥ (u ⨯₃ D.atom e)) ^ 2
          + (D.atom j ⬝ᵥ (u ⨯₃ D.atom e)) ^ 2
          - (D.atom e ⬝ᵥ D.atom e - (D.atom e ⬝ᵥ u) ^ 2) := by
        rcases eq_or_ne (u ⨯₃ D.atom e) 0 with hz | hz
        · have hnorm := turn_normSq_general (u := u) (D.atom e) hunit
          rw [hz] at hnorm
          simp only [zero_dotProduct] at hnorm
          rw [hz]
          simp [← hnorm]
        · have hpos := hfat (u ⨯₃ D.atom e) (turn_dot_u u (D.atom e)) hz
          have hnorm := turn_normSq_general (u := u) (D.atom e) hunit
          nlinarith [hpos, hnorm]
      have hL : ((D.atom e ⬝ᵥ u) ^ 2 - 1)
          * ((u ⬝ᵥ D.atom i ⨯₃ D.atom j) ^ 2
              - (D.atom i ⬝ᵥ D.atom i + D.atom j ⬝ᵥ D.atom j) + 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hdet
      linarith
  -- sum the floors over the dominator
  have hsummed := Finset.sum_le_sum hfloor
  -- the inside plane Parseval prices the right side exactly
  have hread_i : ∑ e ∈ C, (D.atom i ⬝ᵥ (u ⨯₃ D.atom e)) ^ 2
      = D.atom i ⬝ᵥ D.atom i := by
    have hsq : ∀ e : Fin 6, (D.atom i ⬝ᵥ (u ⨯₃ D.atom e)) ^ 2
        = (D.atom e ⬝ᵥ (u ⨯₃ D.atom i)) ^ 2 := by
      intro e
      have h1 : u ⬝ᵥ D.atom e ⨯₃ D.atom i = D.atom i ⬝ᵥ u ⨯₃ D.atom e :=
        turn_read u (D.atom e) (D.atom i)
      have h2 : u ⬝ᵥ D.atom i ⨯₃ D.atom e = D.atom e ⬝ᵥ u ⨯₃ D.atom i :=
        turn_read u (D.atom i) (D.atom e)
      have h3 : u ⬝ᵥ D.atom e ⨯₃ D.atom i = -(u ⬝ᵥ D.atom i ⨯₃ D.atom e) := by
        rw [show D.atom e ⨯₃ D.atom i = -(D.atom i ⨯₃ D.atom e) from
          (cross_anticomm (D.atom i) (D.atom e)).symm, dotProduct_neg]
      have h4 : D.atom i ⬝ᵥ (u ⨯₃ D.atom e)
          = -(D.atom e ⬝ᵥ (u ⨯₃ D.atom i)) := by linarith [h1, h2, h3]
      rw [h4]
      ring
    calc ∑ e ∈ C, (D.atom i ⬝ᵥ (u ⨯₃ D.atom e)) ^ 2
        = ∑ e ∈ C, (D.atom e ⬝ᵥ (u ⨯₃ D.atom i)) ^ 2 :=
          Finset.sum_congr rfl fun e _ => hsq e
      _ = (u ⨯₃ D.atom i) ⬝ᵥ (u ⨯₃ D.atom i) :=
          planeMass_of_rankOneGap D C (turn_dot_u u (D.atom i)) hgap
      _ = D.atom i ⬝ᵥ D.atom i := turn_normSq hunit hqiu
  have hread_j : ∑ e ∈ C, (D.atom j ⬝ᵥ (u ⨯₃ D.atom e)) ^ 2
      = D.atom j ⬝ᵥ D.atom j := by
    have hsq : ∀ e : Fin 6, (D.atom j ⬝ᵥ (u ⨯₃ D.atom e)) ^ 2
        = (D.atom e ⬝ᵥ (u ⨯₃ D.atom j)) ^ 2 := by
      intro e
      have h1 : u ⬝ᵥ D.atom e ⨯₃ D.atom j = D.atom j ⬝ᵥ u ⨯₃ D.atom e :=
        turn_read u (D.atom e) (D.atom j)
      have h2 : u ⬝ᵥ D.atom j ⨯₃ D.atom e = D.atom e ⬝ᵥ u ⨯₃ D.atom j :=
        turn_read u (D.atom j) (D.atom e)
      have h3 : u ⬝ᵥ D.atom e ⨯₃ D.atom j = -(u ⬝ᵥ D.atom j ⨯₃ D.atom e) := by
        rw [show D.atom e ⨯₃ D.atom j = -(D.atom j ⨯₃ D.atom e) from
          (cross_anticomm (D.atom j) (D.atom e)).symm, dotProduct_neg]
      have h4 : D.atom j ⬝ᵥ (u ⨯₃ D.atom e)
          = -(D.atom e ⬝ᵥ (u ⨯₃ D.atom j)) := by linarith [h1, h2, h3]
      rw [h4]
      ring
    calc ∑ e ∈ C, (D.atom j ⬝ᵥ (u ⨯₃ D.atom e)) ^ 2
        = ∑ e ∈ C, (D.atom e ⬝ᵥ (u ⨯₃ D.atom j)) ^ 2 :=
          Finset.sum_congr rfl fun e _ => hsq e
      _ = (u ⨯₃ D.atom j) ⬝ᵥ (u ⨯₃ D.atom j) :=
          planeMass_of_rankOneGap D C (turn_dot_u u (D.atom j)) hgap
      _ = D.atom j ⬝ᵥ D.atom j := turn_normSq hunit hqju
  have hlev : ∑ e ∈ C, (D.atom e ⬝ᵥ D.atom e - (D.atom e ⬝ᵥ u) ^ 2) = 2 := by
    have hlevsum := lam_eq_sum_leverage_sub_of_rankOneGap D C hunit hgap
    have hmass := uMass_of_rankOneGap D C hunit hgap
    have hconv : ∑ e ∈ C, leverageOf (D.atom e)
        = ∑ e ∈ C, D.atom e ⬝ᵥ D.atom e :=
      Finset.sum_congr rfl fun e _ => leverageOf_eq_dotProduct_self (D.atom e)
    have h1 : ∑ e ∈ C, D.atom e ⬝ᵥ D.atom e = lam + 3 := by
      rw [← hconv]
      push_cast at hlevsum
      linarith
    rw [Finset.sum_sub_distrib, h1, hmass]
    ring
  have hmass := uMass_of_rankOneGap D C hunit hgap
  have hcardC : (C.card : ℝ) = 3 := by rw [hcard]; norm_num
  have hLHS : ∑ e ∈ C, ((D.atom e ⬝ᵥ u) ^ 2 - 1)
        * ((u ⬝ᵥ D.atom i ⨯₃ D.atom j) ^ 2
            - (D.atom i ⬝ᵥ D.atom i + D.atom j ⬝ᵥ D.atom j) + 1)
      = (lam - 2) * ((u ⬝ᵥ D.atom i ⨯₃ D.atom j) ^ 2
          - (D.atom i ⬝ᵥ D.atom i + D.atom j ⬝ᵥ D.atom j) + 1) := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hmass,
      Finset.sum_const, hcard]
    push_cast
    ring
  have hRHS : ∑ e ∈ C, ((D.atom i ⬝ᵥ (u ⨯₃ D.atom e)) ^ 2
        + (D.atom j ⬝ᵥ (u ⨯₃ D.atom e)) ^ 2
        - (D.atom e ⬝ᵥ D.atom e - (D.atom e ⬝ᵥ u) ^ 2))
      = D.atom i ⬝ᵥ D.atom i + D.atom j ⬝ᵥ D.atom j - 2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hread_i, hread_j,
      hlev]
  rw [hLHS, hRHS] at hsummed
  exact hsummed



/-- A positive definite outside pair of a planar corank-two tie obeys the
pigeonhole, stated through the cross reading. -/
theorem planar_pairPD_pigeonhole (D : WeightedDesign 6 3) (htie : IsTie D)
    (hprimitive : IsPrimitiveDesign D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (houtside : ∀ d ∈ Cᶜ, D.atom d ⬝ᵥ u = 0)
    {ki kj : Fin 6} (hki : ki ∈ Cᶜ) (hkj : kj ∈ Cᶜ) (hkij : ki ≠ kj)
    (hPD : ∀ w : Fin 3 → ℝ, w ⬝ᵥ u = 0 → w ≠ 0 →
      0 < (D.atom ki ⬝ᵥ w) ^ 2 + (D.atom kj ⬝ᵥ w) ^ 2 - w ⬝ᵥ w) :
    (lam - 2) * ((u ⬝ᵥ D.atom ki ⨯₃ D.atom kj) ^ 2
        - (D.atom ki ⬝ᵥ D.atom ki + D.atom kj ⬝ᵥ D.atom kj) + 1)
      ≤ D.atom ki ⬝ᵥ D.atom ki + D.atom kj ⬝ᵥ D.atom kj - 2 := by
  have hkine : D.atom ki ≠ 0 := by
    intro h
    exact hprimitive kj ki 0 (Ne.symm hkij) (by rw [h, zero_smul])
  have hJne : u ⨯₃ D.atom ki ≠ 0 := by
    intro h
    have hn := turn_normSq hunit (houtside ki hki)
    rw [h] at hn
    simp only [zero_dotProduct] at hn
    exact absurd hn.symm (ne_of_gt (dotProduct_self_pos hkine))
  have hdp := threeForm_det_pos (x := D.atom ki) (y := D.atom kj)
    (z := (0 : Fin 3 → ℝ)) (v := u ⨯₃ D.atom ki) hunit
    (houtside ki hki) (houtside kj hkj) (by simp) (turn_dot_u u (D.atom ki))
    hJne (fun w hw hwne => by simpa using hPD w hw hwne)
  have hdp' : (0:ℝ) ≤ (u ⬝ᵥ D.atom ki ⨯₃ D.atom kj) ^ 2
      - (D.atom ki ⬝ᵥ D.atom ki + D.atom kj ⬝ᵥ D.atom kj) + 1 := by
    have h0 := hdp
    simp only [map_zero, LinearMap.zero_apply, dotProduct_zero,
      zero_dotProduct] at h0
    nlinarith [h0]
  exact planar_fatPair_pigeonhole D htie C hcard hlam hunit hgap houtside
    hki hkj hkij hPD hdp'

/-! ## 3. The closure -/

/-- **THE PLANAR CORANK-TWO CORNER IS EMPTY.**  A primitive `(6,3)` tie
whose gap at a dominator is `lam • u uᵀ` with every outside atom orthogonal
to `u` does not exist. -/
theorem corankTwoPlanar_absurd (D : WeightedDesign 6 3)
    (htie : IsTie D) (hprimitive : IsPrimitiveDesign D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (houtside : ∀ d ∈ Cᶜ, D.atom d ⬝ᵥ u = 0) : False := by
  classical
  obtain ⟨hweights, hlam2⟩ := planar_insideWeights_eq_and_lam_gt_two D htie
    hprimitive C hcard hlam hunit hgap houtside
  have hlam1 : (0:ℝ) < 1 + lam := by linarith
  -- name the three outside atoms
  have hccard := card_compl_eq_three_of_card_eq_three C hcard
  obtain ⟨d1, d2, d3, hd12, hd13, hd23, hCc⟩ := Finset.card_eq_three.mp hccard
  have hd1 : d1 ∈ Cᶜ := by rw [hCc]; simp
  have hd2 : d2 ∈ Cᶜ := by rw [hCc]; simp
  have hd3 : d3 ∈ Cᶜ := by rw [hCc]; simp
  set q1 := D.atom d1 with hq1
  set q2 := D.atom d2 with hq2
  set q3 := D.atom d3 with hq3
  have hq1u : q1 ⬝ᵥ u = 0 := houtside d1 hd1
  have hq2u : q2 ⬝ᵥ u = 0 := houtside d2 hd2
  have hq3u : q3 ⬝ᵥ u = 0 := houtside d3 hd3
  have hc21 : q2 ⬝ᵥ q1 = q1 ⬝ᵥ q2 := dotProduct_comm q2 q1
  have hc31 : q3 ⬝ᵥ q1 = q1 ⬝ᵥ q3 := dotProduct_comm q3 q1
  have hc32 : q3 ⬝ᵥ q2 = q2 ⬝ᵥ q3 := dotProduct_comm q3 q2
  have hsum3 : ∀ f : Fin 6 → ℝ, ∑ d ∈ Cᶜ, f d = f d1 + f d2 + f d3 := by
    intro f
    rw [hCc, Finset.sum_insert (by simp [hd12, hd13]),
      Finset.sum_insert (by simp [hd23]), Finset.sum_singleton]
    ring
  -- outside atoms are nonzero and pairwise nonparallel
  have hqne : ∀ a b : Fin 6, a ≠ b → D.atom a ≠ 0 := by
    intro a b hab h
    exact hprimitive b a 0 (Ne.symm hab) (by rw [h, zero_smul])
  have hq1ne : q1 ≠ 0 := hqne d1 d2 hd12
  have hq2ne : q2 ≠ 0 := hqne d2 d1 hd12.symm
  have hq3ne : q3 ≠ 0 := hqne d3 d1 hd13.symm
  have hl1 : (0:ℝ) < q1 ⬝ᵥ q1 := dotProduct_self_pos hq1ne
  have hl2 : (0:ℝ) < q2 ⬝ᵥ q2 := dotProduct_self_pos hq2ne
  have hl3 : (0:ℝ) < q3 ⬝ᵥ q3 := dotProduct_self_pos hq3ne
  have hcrossne : ∀ a b : Fin 6, a ≠ b → D.atom a ⨯₃ D.atom b ≠ 0 := by
    intro a b hab h
    have hla : (0:ℝ) < D.atom a ⬝ᵥ D.atom a :=
      dotProduct_self_pos (hqne a b hab)
    have hcc := cross_cross_eq_smul_sub_smul' (D.atom a) (D.atom a) (D.atom b)
    rw [h] at hcc
    simp only [map_zero] at hcc
    have hsolve : D.atom b
        = ((D.atom a ⬝ᵥ D.atom b) / (D.atom a ⬝ᵥ D.atom a)) • D.atom a := by
      have h1 : (D.atom a ⬝ᵥ D.atom a) • D.atom b
          = (D.atom a ⬝ᵥ D.atom b) • D.atom a := by
        have h0 := hcc.symm
        rw [sub_eq_zero] at h0
        exact h0.symm
      have h2 : D.atom b
          = ((D.atom a ⬝ᵥ D.atom a)⁻¹ * (D.atom a ⬝ᵥ D.atom b)) • D.atom a := by
        have h3 := congrArg
          (fun t => ((D.atom a ⬝ᵥ D.atom a)⁻¹ : ℝ) • t) h1
        simp only [smul_smul] at h3
        rwa [inv_mul_cancel₀ (ne_of_gt hla), one_smul] at h3
      rw [div_eq_inv_mul]
      exact h2
    exact hprimitive a b _ hab hsolve
  -- pair determinants through the Gram, and the u-readings of the crosses
  have hpy : ∀ a b : Fin 3 → ℝ, a ⬝ᵥ u = 0 → b ⬝ᵥ u = 0 →
      (a ⬝ᵥ (u ⨯₃ b)) ^ 2 = (a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) ^ 2 := by
    intro a b ha hb
    have h := plane_pythagoras hunit ha hb
    linarith [h]
  have hU12 : (u ⬝ᵥ q1 ⨯₃ q2) ^ 2
      = (q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 := by
    rw [turn_read u q1 q2]
    have := hpy q2 q1 hq2u hq1u
    rw [dotProduct_comm q2 q1] at this
    linarith [this]
  have hU13 : (u ⬝ᵥ q1 ⨯₃ q3) ^ 2
      = (q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 := by
    rw [turn_read u q1 q3]
    have := hpy q3 q1 hq3u hq1u
    rw [dotProduct_comm q3 q1] at this
    linarith [this]
  have hU23 : (u ⬝ᵥ q2 ⨯₃ q3) ^ 2
      = (q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2 := by
    rw [turn_read u q2 q3]
    have := hpy q3 q2 hq3u hq2u
    rw [dotProduct_comm q3 q2] at this
    linarith [this]
  -- the scaled weights
  have hT1 : (0:ℝ) < (1 + lam) * D.weight d1 := mul_pos hlam1 (D.weight_pos d1)
  have hT2 : (0:ℝ) < (1 + lam) * D.weight d2 := mul_pos hlam1 (D.weight_pos d2)
  have hT3 : (0:ℝ) < (1 + lam) * D.weight d3 := mul_pos hlam1 (D.weight_pos d3)
  have hTtot : (1 + lam) * D.weight d1 + (1 + lam) * D.weight d2
      + (1 + lam) * D.weight d3 = lam - 2 := by
    have h := outside_weight_total_of_planar D C hcard (by linarith) hweights
    rw [hsum3 D.weight] at h
    linarith [h]
  -- the polarized isotropy at named atoms
  have hiso : ∀ v w : Fin 3 → ℝ, v ⬝ᵥ u = 0 → w ⬝ᵥ u = 0 →
      ((1 + lam) * D.weight d1) * ((q1 ⬝ᵥ v) * (q1 ⬝ᵥ w))
        + ((1 + lam) * D.weight d2) * ((q2 ⬝ᵥ v) * (q2 ⬝ᵥ w))
        + ((1 + lam) * D.weight d3) * ((q3 ⬝ᵥ v) * (q3 ⬝ᵥ w))
      = lam * (v ⬝ᵥ w) := by
    intro v w hv hw
    have h := outside_isotropy_polar D C (by linarith) hv hw hgap hweights
    rw [hsum3 (fun d => D.weight d * ((D.atom d ⬝ᵥ v) * (D.atom d ⬝ᵥ w)))]
      at h
    rw [← hq1, ← hq2, ← hq3] at h
    linarith [h]
  -- the outside gap form is positive definite on the plane
  have hRpd : ∀ w : Fin 3 → ℝ, w ⬝ᵥ u = 0 → w ≠ 0 →
      0 < (q1 ⬝ᵥ w) ^ 2 + (q2 ⬝ᵥ w) ^ 2 + (q3 ⬝ᵥ w) ^ 2 - w ⬝ᵥ w := by
    intro w hw hwne
    have hisow := hiso w w hw hw
    have hwpos := dotProduct_self_pos hwne
    nlinarith [hisow, hwpos,
      mul_le_mul_of_nonneg_right
        (by linarith : (1 + lam) * D.weight d1 ≤ lam - 2)
        (sq_nonneg (q1 ⬝ᵥ w)),
      mul_le_mul_of_nonneg_right
        (by linarith : (1 + lam) * D.weight d2 ≤ lam - 2)
        (sq_nonneg (q2 ⬝ᵥ w)),
      mul_le_mul_of_nonneg_right
        (by linarith : (1 + lam) * D.weight d3 ≤ lam - 2)
        (sq_nonneg (q3 ⬝ᵥ w)),
      sq_nonneg (q1 ⬝ᵥ w), sq_nonneg (q2 ⬝ᵥ w), sq_nonneg (q3 ⬝ᵥ w)]
  -- the outside gap determinant is positive
  have hJ1ne : u ⨯₃ q1 ≠ 0 := by
    intro h
    have := turn_normSq hunit hq1u
    rw [h] at this
    simp only [zero_dotProduct] at this
    exact absurd this.symm (ne_of_gt hl1)
  have hDD0 := threeForm_det_pos (x := q1) (y := q2) (z := q3)
    (v := u ⨯₃ q1) hunit hq1u hq2u hq3u (turn_dot_u u q1) hJ1ne hRpd
  have hDD : (0:ℝ) <
      ((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2)
        + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2)
        + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2)
        - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1 := by
    rw [← hU12, ← hU13, ← hU23]
    linarith [hDD0]
  -- the turned self-readings are positive
  have hpy21 : (q2 ⬝ᵥ (u ⨯₃ q1)) ^ 2
      = (q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 := by
    have := hpy q2 q1 hq2u hq1u
    rw [dotProduct_comm q2 q1] at this
    linarith [this]
  have hpy31 : (q3 ⬝ᵥ (u ⨯₃ q1)) ^ 2
      = (q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 := by
    have := hpy q3 q1 hq3u hq1u
    rw [dotProduct_comm q3 q1] at this
    linarith [this]
  have hpy12 : (q1 ⬝ᵥ (u ⨯₃ q2)) ^ 2
      = (q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 :=
    hpy q1 q2 hq1u hq2u
  have hpy32 : (q3 ⬝ᵥ (u ⨯₃ q2)) ^ 2
      = (q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2 := by
    have := hpy q3 q2 hq3u hq2u
    rw [dotProduct_comm q3 q2] at this
    linarith [this]
  have hpy13 : (q1 ⬝ᵥ (u ⨯₃ q3)) ^ 2
      = (q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 :=
    hpy q1 q3 hq1u hq3u
  have hpy23 : (q2 ⬝ᵥ (u ⨯₃ q3)) ^ 2
      = (q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2 :=
    hpy q2 q3 hq2u hq3u
  have hself : ∀ a : Fin 3 → ℝ, (a ⬝ᵥ (u ⨯₃ a)) = 0 := by
    intro a
    rw [dotProduct_comm]
    exact turn_dot_self u a
  have hLL1 : (0:ℝ) < ((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1)
      - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2 := by
    have h := hRpd (u ⨯₃ q1) (turn_dot_u u q1) hJ1ne
    rw [hself q1] at h
    rw [turn_normSq hunit hq1u] at h
    nlinarith [h, hpy21, hpy31]
  have hJ2ne : u ⨯₃ q2 ≠ 0 := by
    intro h
    have := turn_normSq hunit hq2u
    rw [h] at this
    simp only [zero_dotProduct] at this
    exact absurd this.symm (ne_of_gt hl2)
  have hJ3ne : u ⨯₃ q3 ≠ 0 := by
    intro h
    have := turn_normSq hunit hq3u
    rw [h] at this
    simp only [zero_dotProduct] at this
    exact absurd this.symm (ne_of_gt hl3)
  have hLL2 : (0:ℝ) < ((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2)
      - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2 := by
    have h := hRpd (u ⨯₃ q2) (turn_dot_u u q2) hJ2ne
    rw [hself q2] at h
    rw [turn_normSq hunit hq2u] at h
    nlinarith [h, hpy12, hpy32]
  have hLL3 : (0:ℝ) < ((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3)
      - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2 := by
    have h := hRpd (u ⨯₃ q3) (turn_dot_u u q3) hJ3ne
    rw [hself q3] at h
    rw [turn_normSq hunit hq3u] at h
    nlinarith [h, hpy13, hpy23]
  -- planarity: the Gram determinant vanishes
  have htriple : q1 ⬝ᵥ q2 ⨯₃ q3 = 0 :=
    triple_product_eq_zero_of_orth hunit hq2u hq3u hq1u
  have hCB : (q1 ⬝ᵥ q2 ⨯₃ q3) ^ 2
      = (q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3)
        + 2 * (q1 ⬝ᵥ q2) * (q1 ⬝ᵥ q3) * (q2 ⬝ᵥ q3)
        - (q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q2) * (q1 ⬝ᵥ q3) ^ 2
        - (q3 ⬝ᵥ q3) * (q1 ⬝ᵥ q2) ^ 2 := by
    simp only [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    ring
  have hdetG : (q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3)
        + 2 * (q1 ⬝ᵥ q2) * (q1 ⬝ᵥ q3) * (q2 ⬝ᵥ q3)
        - (q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q2) * (q1 ⬝ᵥ q3) ^ 2
        - (q3 ⬝ᵥ q3) * (q1 ⬝ᵥ q2) ^ 2 = 0 := by
    rw [← hCB, htriple]
    ring
  have hdet0 : (0:ℝ) ≤ (u ⬝ᵥ q1 ⨯₃ q2) ^ 2 + (u ⬝ᵥ q1 ⨯₃ q3) ^ 2
      + (u ⬝ᵥ q2 ⨯₃ q3) ^ 2 - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1 :=
    hDD0.le
  have hdich1 : (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) ≤ (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2)
      ∨ (lam - 2) * ((((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) - (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2))
        ≤ (q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 2 := by
    by_cases hPD : ∀ w : Fin 3 → ℝ, w ⬝ᵥ u = 0 → w ≠ 0 →
        0 < (q2 ⬝ᵥ w) ^ 2 + (q3 ⬝ᵥ w) ^ 2 - w ⬝ᵥ w
    · right
      have h := planar_pairPD_pigeonhole D htie hprimitive C hcard hlam hunit
        hgap houtside hd2 hd3 hd23 hPD
      have hconv : (u ⬝ᵥ q2 ⨯₃ q3) ^ 2
          - (q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1
          = (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) - (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2) := by
        rw [hU23]
        ring
      rw [hconv] at h
      linarith [h]
    · left
      push_neg at hPD
      obtain ⟨w, hw, hwne, hple⟩ := hPD
      have hkit := threeForm_turn_floor (u := u) (x := q1) (y := q2) (z := q3)
        (q := q1) (w := w) (c := 1) hunit hq1u hq2u hq3u hw
        (by nlinarith [hple]) (hRpd w hw hwne) hdet0
      have hK : (u ⬝ᵥ q1 ⨯₃ q2) ^ 2 + (u ⬝ᵥ q1 ⨯₃ q3) ^ 2
          + (u ⬝ᵥ q2 ⨯₃ q3) ^ 2 - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1
          = (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) := by
        rw [hU12, hU13, hU23]
        ring
      have hL : (q1 ⬝ᵥ (u ⨯₃ q1)) ^ 2 + (q2 ⬝ᵥ (u ⨯₃ q1)) ^ 2
          + (q3 ⬝ᵥ (u ⨯₃ q1)) ^ 2 - (q1 ⬝ᵥ q1 - (q1 ⬝ᵥ u) ^ 2)
          = (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2) := by
        rw [hself q1, hpy21, hpy31, hq1u]
        ring
      rw [hK, hL] at hkit
      linarith [hkit]
  have hdich2 : (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) ≤ (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2)
      ∨ (lam - 2) * ((((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) - (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2))
        ≤ (q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 2 := by
    by_cases hPD : ∀ w : Fin 3 → ℝ, w ⬝ᵥ u = 0 → w ≠ 0 →
        0 < (q1 ⬝ᵥ w) ^ 2 + (q3 ⬝ᵥ w) ^ 2 - w ⬝ᵥ w
    · right
      have h := planar_pairPD_pigeonhole D htie hprimitive C hcard hlam hunit
        hgap houtside hd1 hd3 hd13 hPD
      have hconv : (u ⬝ᵥ q1 ⨯₃ q3) ^ 2
          - (q1 ⬝ᵥ q1 + q3 ⬝ᵥ q3) + 1
          = (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) - (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) := by
        rw [hU13]
        ring
      rw [hconv] at h
      linarith [h]
    · left
      push_neg at hPD
      obtain ⟨w, hw, hwne, hple⟩ := hPD
      have hkit := threeForm_turn_floor (u := u) (x := q1) (y := q2) (z := q3)
        (q := q2) (w := w) (c := 1) hunit hq1u hq2u hq3u hw
        (by nlinarith [hple]) (hRpd w hw hwne) hdet0
      have hK : (u ⬝ᵥ q1 ⨯₃ q2) ^ 2 + (u ⬝ᵥ q1 ⨯₃ q3) ^ 2
          + (u ⬝ᵥ q2 ⨯₃ q3) ^ 2 - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1
          = (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) := by
        rw [hU12, hU13, hU23]
        ring
      have hL : (q1 ⬝ᵥ (u ⨯₃ q2)) ^ 2 + (q2 ⬝ᵥ (u ⨯₃ q2)) ^ 2
          + (q3 ⬝ᵥ (u ⨯₃ q2)) ^ 2 - (q2 ⬝ᵥ q2 - (q2 ⬝ᵥ u) ^ 2)
          = (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) := by
        rw [hself q2, hpy12, hpy32, hq2u]
        ring
      rw [hK, hL] at hkit
      linarith [hkit]
  have hdich3 : (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) ≤ (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2)
      ∨ (lam - 2) * ((((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) - (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2))
        ≤ (q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 2 := by
    by_cases hPD : ∀ w : Fin 3 → ℝ, w ⬝ᵥ u = 0 → w ≠ 0 →
        0 < (q1 ⬝ᵥ w) ^ 2 + (q2 ⬝ᵥ w) ^ 2 - w ⬝ᵥ w
    · right
      have h := planar_pairPD_pigeonhole D htie hprimitive C hcard hlam hunit
        hgap houtside hd1 hd2 hd12 hPD
      have hconv : (u ⬝ᵥ q1 ⨯₃ q2) ^ 2
          - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2) + 1
          = (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) - (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) := by
        rw [hU12]
        ring
      rw [hconv] at h
      linarith [h]
    · left
      push_neg at hPD
      obtain ⟨w, hw, hwne, hple⟩ := hPD
      have hkit := threeForm_turn_floor (u := u) (x := q1) (y := q2) (z := q3)
        (q := q3) (w := w) (c := 1) hunit hq1u hq2u hq3u hw
        (by nlinarith [hple]) (hRpd w hw hwne) hdet0
      have hK : (u ⬝ᵥ q1 ⨯₃ q2) ^ 2 + (u ⬝ᵥ q1 ⨯₃ q3) ^ 2
          + (u ⬝ᵥ q2 ⨯₃ q3) ^ 2 - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1
          = (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) := by
        rw [hU12, hU13, hU23]
        ring
      have hL : (q1 ⬝ᵥ (u ⨯₃ q3)) ^ 2 + (q2 ⬝ᵥ (u ⨯₃ q3)) ^ 2
          + (q3 ⬝ᵥ (u ⨯₃ q3)) ^ 2 - (q3 ⬝ᵥ q3 - (q3 ⬝ᵥ u) ^ 2)
          = (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) := by
        rw [hself q3, hpy13, hpy23, hq3u]
        ring
      rw [hK, hL] at hkit
      linarith [hkit]

  set x1 : Fin 3 → ℝ := ((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) • q1
      - ((q1 ⬝ᵥ q2) • q2 + (q1 ⬝ᵥ q3) • q3) with hx1def
  have hx1u : x1 ⬝ᵥ u = 0 := by
    rw [hx1def]
    simp only [sub_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul,
      hq1u, hq2u, hq3u]
    ring
  have hP11 : q1 ⬝ᵥ x1 = (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2) := by
    rw [hx1def]
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
    
    ring
  have hP21 : q2 ⬝ᵥ x1 = (q1 ⬝ᵥ q2) * ((q3 ⬝ᵥ q3) - 1) - (q1 ⬝ᵥ q3) * (q2 ⬝ᵥ q3) := by
    rw [hx1def]
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
    simp only [hc21, hc31, hc32]
    ring
  have hP31 : q3 ⬝ᵥ x1 = (q1 ⬝ᵥ q3) * ((q2 ⬝ᵥ q2) - 1) - (q1 ⬝ᵥ q2) * (q2 ⬝ᵥ q3) := by
    rw [hx1def]
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
    simp only [hc21, hc31, hc32]
    ring
  have hx1sq : x1 ⬝ᵥ x1
      = (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3)) - 2) * (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2) - (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (q1 ⬝ᵥ q1) := by
    rw [hx1def]
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, sub_dotProduct,
      add_dotProduct, smul_dotProduct, smul_eq_mul]
    simp only [hc21, hc31, hc32]
    linear_combination hdetG
  have hQ1raw : (q1 ⬝ᵥ x1) ^ 2 + (q2 ⬝ᵥ x1) ^ 2 + (q3 ⬝ᵥ x1) ^ 2
      = (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2) + (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3)) - 2) * (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2)
        - (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (q1 ⬝ᵥ q1) := by
    rw [hP11, hP21, hP31]
    linear_combination (2 - (q2 ⬝ᵥ q2) - (q3 ⬝ᵥ q3)) * hdetG
  have hiso1x := hiso x1 x1 hx1u hx1u
  rw [hx1sq] at hiso1x
  have hEL1raw : (lam - ((1 + lam) * D.weight d1)) * (q1 ⬝ᵥ x1) ^ 2
        + (lam - ((1 + lam) * D.weight d2)) * (q2 ⬝ᵥ x1) ^ 2 + (lam - ((1 + lam) * D.weight d3)) * (q3 ⬝ᵥ x1) ^ 2
      = lam * (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2) := by
    linear_combination lam * hQ1raw - hiso1x
      + lam * ((q1 ⬝ᵥ x1) + (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2)) * hP11
      - lam * ((q1 ⬝ᵥ x1) + (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2)) * hP11
  set x2 : Fin 3 → ℝ := ((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) • q2
      - ((q1 ⬝ᵥ q2) • q1 + (q2 ⬝ᵥ q3) • q3) with hx2def
  have hx2u : x2 ⬝ᵥ u = 0 := by
    rw [hx2def]
    simp only [sub_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul,
      hq1u, hq2u, hq3u]
    ring
  have hP22 : q2 ⬝ᵥ x2 = (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) := by
    rw [hx2def]
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
    simp only [hc21, hc31, hc32]
    ring
  have hP12 : q1 ⬝ᵥ x2 = (q1 ⬝ᵥ q2) * ((q3 ⬝ᵥ q3) - 1) - (q2 ⬝ᵥ q3) * (q1 ⬝ᵥ q3) := by
    rw [hx2def]
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
    
    ring
  have hP32 : q3 ⬝ᵥ x2 = (q2 ⬝ᵥ q3) * ((q1 ⬝ᵥ q1) - 1) - (q1 ⬝ᵥ q2) * (q1 ⬝ᵥ q3) := by
    rw [hx2def]
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
    simp only [hc21, hc31, hc32]
    ring
  have hx2sq : x2 ⬝ᵥ x2
      = (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3)) - 2) * (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) - (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (q2 ⬝ᵥ q2) := by
    rw [hx2def]
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, sub_dotProduct,
      add_dotProduct, smul_dotProduct, smul_eq_mul]
    simp only [hc21, hc31, hc32]
    linear_combination hdetG
  have hQ2raw : (q2 ⬝ᵥ x2) ^ 2 + (q1 ⬝ᵥ x2) ^ 2 + (q3 ⬝ᵥ x2) ^ 2
      = (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) + (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3)) - 2) * (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2)
        - (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (q2 ⬝ᵥ q2) := by
    rw [hP22, hP12, hP32]
    linear_combination (2 - (q1 ⬝ᵥ q1) - (q3 ⬝ᵥ q3)) * hdetG
  have hiso2x := hiso x2 x2 hx2u hx2u
  rw [hx2sq] at hiso2x
  have hEL2raw : (lam - ((1 + lam) * D.weight d1)) * (q1 ⬝ᵥ x2) ^ 2
        + (lam - ((1 + lam) * D.weight d2)) * (q2 ⬝ᵥ x2) ^ 2 + (lam - ((1 + lam) * D.weight d3)) * (q3 ⬝ᵥ x2) ^ 2
      = lam * (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) := by
    linear_combination lam * hQ2raw - hiso2x
      + lam * ((q2 ⬝ᵥ x2) + (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2)) * hP22
      - lam * ((q2 ⬝ᵥ x2) + (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2)) * hP22
  set x3 : Fin 3 → ℝ := ((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) • q3
      - ((q1 ⬝ᵥ q3) • q1 + (q2 ⬝ᵥ q3) • q2) with hx3def
  have hx3u : x3 ⬝ᵥ u = 0 := by
    rw [hx3def]
    simp only [sub_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul,
      hq1u, hq2u, hq3u]
    ring
  have hP33 : q3 ⬝ᵥ x3 = (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) := by
    rw [hx3def]
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
    simp only [hc21, hc31, hc32]
    ring
  have hP13 : q1 ⬝ᵥ x3 = (q1 ⬝ᵥ q3) * ((q2 ⬝ᵥ q2) - 1) - (q2 ⬝ᵥ q3) * (q1 ⬝ᵥ q2) := by
    rw [hx3def]
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
    
    ring
  have hP23 : q2 ⬝ᵥ x3 = (q2 ⬝ᵥ q3) * ((q1 ⬝ᵥ q1) - 1) - (q1 ⬝ᵥ q3) * (q1 ⬝ᵥ q2) := by
    rw [hx3def]
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
    simp only [hc21, hc31, hc32]
    ring
  have hx3sq : x3 ⬝ᵥ x3
      = (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3)) - 2) * (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) - (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (q3 ⬝ᵥ q3) := by
    rw [hx3def]
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, sub_dotProduct,
      add_dotProduct, smul_dotProduct, smul_eq_mul]
    simp only [hc21, hc31, hc32]
    linear_combination hdetG
  have hQ3raw : (q3 ⬝ᵥ x3) ^ 2 + (q1 ⬝ᵥ x3) ^ 2 + (q2 ⬝ᵥ x3) ^ 2
      = (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) + (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3)) - 2) * (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2)
        - (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (q3 ⬝ᵥ q3) := by
    rw [hP33, hP13, hP23]
    linear_combination (2 - (q1 ⬝ᵥ q1) - (q2 ⬝ᵥ q2)) * hdetG
  have hiso3x := hiso x3 x3 hx3u hx3u
  rw [hx3sq] at hiso3x
  have hEL3raw : (lam - ((1 + lam) * D.weight d1)) * (q1 ⬝ᵥ x3) ^ 2
        + (lam - ((1 + lam) * D.weight d2)) * (q2 ⬝ᵥ x3) ^ 2 + (lam - ((1 + lam) * D.weight d3)) * (q3 ⬝ᵥ x3) ^ 2
      = lam * (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) := by
    linear_combination lam * hQ3raw - hiso3x
      + lam * ((q3 ⬝ᵥ x3) + (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2)) * hP33
      - lam * ((q3 ⬝ᵥ x3) + (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2)) * hP33
  -- the trace ledger
  have hTl : ((1 + lam) * D.weight d1) * (q1 ⬝ᵥ q1) + ((1 + lam) * D.weight d2) * (q2 ⬝ᵥ q2) + ((1 + lam) * D.weight d3) * (q3 ⬝ᵥ q3)
      = 2 * lam := by
    have ha := hiso q1 q1 hq1u hq1u
    have hb := hiso (u ⨯₃ q1) (u ⨯₃ q1) (turn_dot_u u q1) (turn_dot_u u q1)
    rw [turn_normSq hunit hq1u] at hb
    have py1 := plane_pythagoras (x := q1) (v := q1) hunit hq1u hq1u
    have py2 := plane_pythagoras (x := q2) (v := q1) hunit hq2u hq1u
    have py3 := plane_pythagoras (x := q3) (v := q1) hunit hq3u hq1u
    have hkey : (((1 + lam) * D.weight d1) * (q1 ⬝ᵥ q1) + ((1 + lam) * D.weight d2) * (q2 ⬝ᵥ q2)
          + ((1 + lam) * D.weight d3) * (q3 ⬝ᵥ q3)) * (q1 ⬝ᵥ q1) = (2 * lam) * (q1 ⬝ᵥ q1) := by
      linear_combination ha + hb - ((1 + lam) * D.weight d1) * py1 - ((1 + lam) * D.weight d2) * py2 - ((1 + lam) * D.weight d3) * py3
    exact mul_right_cancel₀ (ne_of_gt hl1) hkey
  -- canonical isotropy instances at the atom pairs
  have hIso11 := hiso q1 q1 hq1u hq1u
  have hIso22 := hiso q2 q2 hq2u hq2u
  have hIso33 := hiso q3 q3 hq3u hq3u
  simp only [hc21, hc31, hc32] at hIso11 hIso22 hIso33
  -- the determinant ledger
  have hTLL : ((1 + lam) * D.weight d1) * (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2) + ((1 + lam) * D.weight d2) * (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) + ((1 + lam) * D.weight d3) * (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2)
      = lam * (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3)) - 2) := by
    linear_combination (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3)) - 1) * hTl - hIso11 - hIso22 - hIso33
  have hledger : (lam - ((1 + lam) * D.weight d1)) * (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2) + (lam - ((1 + lam) * D.weight d2)) * (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2)
      + (lam - ((1 + lam) * D.weight d3)) * (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) = 2 * lam * (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) := by
    linear_combination (-1 : ℝ) * hTLL
  -- the dispatch hypotheses in their final shapes
  have hEL1 : (lam - ((1 + lam) * D.weight d1)) * (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2) ^ 2 + (lam - ((1 + lam) * D.weight d2)) * (q2 ⬝ᵥ x1) ^ 2
      + (lam - ((1 + lam) * D.weight d3)) * (q3 ⬝ᵥ x1) ^ 2 = lam * (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2) := by
    linear_combination hEL1raw
      - (lam - ((1 + lam) * D.weight d1)) * ((q1 ⬝ᵥ x1) + (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2)) * hP11
  have hEL2 : (lam - ((1 + lam) * D.weight d1)) * (q2 ⬝ᵥ x1) ^ 2 + (lam - ((1 + lam) * D.weight d2)) * (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) ^ 2
      + (lam - ((1 + lam) * D.weight d3)) * (q3 ⬝ᵥ x2) ^ 2 = lam * (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) := by
    linear_combination hEL2raw
      - (lam - ((1 + lam) * D.weight d2)) * ((q2 ⬝ᵥ x2) + (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2)) * hP22
      - (lam - ((1 + lam) * D.weight d1)) * ((q1 ⬝ᵥ x2) + (q2 ⬝ᵥ x1)) * hP12
      + (lam - ((1 + lam) * D.weight d1)) * ((q1 ⬝ᵥ x2) + (q2 ⬝ᵥ x1)) * hP21
  have hEL3 : (lam - ((1 + lam) * D.weight d1)) * (q3 ⬝ᵥ x1) ^ 2 + (lam - ((1 + lam) * D.weight d2)) * (q3 ⬝ᵥ x2) ^ 2
      + (lam - ((1 + lam) * D.weight d3)) * (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) ^ 2 = lam * (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) := by
    linear_combination hEL3raw
      - (lam - ((1 + lam) * D.weight d3)) * ((q3 ⬝ᵥ x3) + (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2)) * hP33
      - (lam - ((1 + lam) * D.weight d1)) * ((q1 ⬝ᵥ x3) + (q3 ⬝ᵥ x1)) * hP13
      + (lam - ((1 + lam) * D.weight d1)) * ((q1 ⬝ᵥ x3) + (q3 ⬝ᵥ x1)) * hP31
      - (lam - ((1 + lam) * D.weight d2)) * ((q2 ⬝ᵥ x3) + (q3 ⬝ᵥ x2)) * hP23
      + (lam - ((1 + lam) * D.weight d2)) * ((q2 ⬝ᵥ x3) + (q3 ⬝ᵥ x2)) * hP32
  have hQ1 : (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2) ^ 2 + (q2 ⬝ᵥ x1) ^ 2 + (q3 ⬝ᵥ x1) ^ 2
      = (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2) + (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3)) - 2) * (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2) - (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (q1 ⬝ᵥ q1) := by
    linear_combination hQ1raw - ((q1 ⬝ᵥ x1) + (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2)) * hP11
  have hQ2 : (q2 ⬝ᵥ x1) ^ 2 + (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) ^ 2 + (q3 ⬝ᵥ x2) ^ 2
      = (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) + (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3)) - 2) * (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) - (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (q2 ⬝ᵥ q2) := by
    linear_combination hQ2raw - ((q2 ⬝ᵥ x2) + (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2)) * hP22
      - ((q1 ⬝ᵥ x2) + (q2 ⬝ᵥ x1)) * hP12
      + ((q1 ⬝ᵥ x2) + (q2 ⬝ᵥ x1)) * hP21
  have hQ3 : (q3 ⬝ᵥ x1) ^ 2 + (q3 ⬝ᵥ x2) ^ 2 + (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) ^ 2
      = (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) + (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3)) - 2) * (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) - (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) * (q3 ⬝ᵥ q3) := by
    linear_combination hQ3raw - ((q3 ⬝ᵥ x3) + (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2)) * hP33
      - ((q1 ⬝ᵥ x3) + (q3 ⬝ᵥ x1)) * hP13
      + ((q1 ⬝ᵥ x3) + (q3 ⬝ᵥ x1)) * hP31
      - ((q2 ⬝ᵥ x3) + (q3 ⬝ᵥ x2)) * hP23
      + ((q2 ⬝ᵥ x3) + (q3 ⬝ᵥ x2)) * hP32
  have hTrEq : (((q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3) - 1) * (q1 ⬝ᵥ q1) - (q1 ⬝ᵥ q2) ^ 2 - (q1 ⬝ᵥ q3) ^ 2) + (((q1 ⬝ᵥ q1) + (q3 ⬝ᵥ q3) - 1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) + (((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) - 1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2 - (q2 ⬝ᵥ q3) ^ 2) = 2 * (((q2 ⬝ᵥ q2) * (q3 ⬝ᵥ q3) - (q2 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q3 ⬝ᵥ q3) - (q1 ⬝ᵥ q3) ^ 2) + ((q1 ⬝ᵥ q1) * (q2 ⬝ᵥ q2) - (q1 ⬝ᵥ q2) ^ 2) - (q1 ⬝ᵥ q1 + q2 ⬝ᵥ q2 + q3 ⬝ᵥ q3) + 1) + ((q1 ⬝ᵥ q1) + (q2 ⬝ᵥ q2) + (q3 ⬝ᵥ q3)) - 2 := by ring
  exact planar_scalar_dispatch hlam2 hT1 hT2 hT3 hTtot hDD hLL1 hLL2 hLL3
    hledger hTrEq hEL1 hEL2 hEL3 hQ1 hQ2 hQ3 hdich1 hdich2 hdich3


end Gtz

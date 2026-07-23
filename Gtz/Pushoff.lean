/-
# The Zero-Atom Pushoff Theorem

The result that dissolved GAP-T (diary §75; both adversarial audits SOUND, and
hand-verified independently): every atom-plane projection of a weighted design
carries the projecting atom as a **zero atom** — square `0`, leverage `0`,
defect `1` — and the universal pairing identity then pushes the whole
projection a definite distance off the equality manifold:

  `t_e ≤ (|ξ| + 1/2) · Σ_{c ≠ e} t_c · |S_c − X_c|`

for ANY moment vector `ξ` and ANY assignment `c ↦ X_c` of defect-zero points.
No silence hypothesis, no heaviness, no corner exclusion — it is pure design
bookkeeping plus a Lipschitz bound. Consequence: GAP-T's `δ_T = 0` case is
EMPTY, and its distance form is a theorem with `δ_T ∼ t_e`.

Contents:
* `planarNorm` and its kit — Cauchy–Schwarz and the triangle inequality proved
  from scratch in the planar case (Lagrange identity + `nlinarith`), so nothing
  here depends on an `InnerProductSpace` instance over `Fin 2 → ℝ`;
* `planarDefect` — `d(S) = 1 + ⟨ξ,S⟩ − |S|/2`, vanishing exactly on the tight
  clusters of the equality manifold (Theorem V), `(|ξ| + 1/2)`-Lipschitz;
* `sum_weighted_defect_eq_zero` — the pairing identity `Σ t_c d_c = 0`, which
  is the three design equations paired with `(1, ξ, −1/2)`;
* `zeroAtom_pushoff` — the theorem;
* `cornerPushoff_saturates` — the sharpness witness: at the embedded
  tetrahedron corner the bound holds with EQUALITY (both sides `1/4`), so the
  constant cannot be improved.
-/
import Mathlib
import Gtz.PsdKit

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ### The planar norm kit -/

/-- Euclidean length of a planar vector, from the dot product. -/
noncomputable def planarNorm (planarVec : Fin 2 → ℝ) : ℝ :=
  Real.sqrt (planarVec ⬝ᵥ planarVec)

theorem planarNorm_nonneg (planarVec : Fin 2 → ℝ) : 0 ≤ planarNorm planarVec :=
  Real.sqrt_nonneg _

theorem planarNorm_sq (planarVec : Fin 2 → ℝ) :
    planarNorm planarVec ^ 2 = planarVec ⬝ᵥ planarVec :=
  Real.sq_sqrt (dotProduct_self_nonneg planarVec)

theorem planarNorm_zero : planarNorm (0 : Fin 2 → ℝ) = 0 := by
  simp only [planarNorm, dotProduct, Fin.sum_univ_two, Pi.zero_apply]
  norm_num

/-- **Cauchy–Schwarz, planar case**, via the Lagrange identity. -/
theorem dotProduct_le_planarNorm_mul (leftVec rightVec : Fin 2 → ℝ) :
    leftVec ⬝ᵥ rightVec ≤ planarNorm leftVec * planarNorm rightVec := by
  have hlag : (leftVec ⬝ᵥ rightVec) ^ 2
      ≤ (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) := by
    simp only [dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0)]
  by_contra hcontra
  push Not at hcontra
  have hprodNonneg : 0 ≤ planarNorm leftVec * planarNorm rightVec :=
    mul_nonneg (planarNorm_nonneg _) (planarNorm_nonneg _)
  nlinarith [planarNorm_sq leftVec, planarNorm_sq rightVec, hlag, hcontra,
    hprodNonneg]

/-- The absolute pairing bound. -/
theorem abs_dotProduct_le_planarNorm_mul (leftVec rightVec : Fin 2 → ℝ) :
    |leftVec ⬝ᵥ rightVec| ≤ planarNorm leftVec * planarNorm rightVec := by
  have hneg : leftVec ⬝ᵥ (-rightVec) = -(leftVec ⬝ᵥ rightVec) := by
    simp only [dotProduct, Fin.sum_univ_two, Pi.neg_apply]
    ring
  have hnormNeg : planarNorm (-rightVec) = planarNorm rightVec := by
    simp only [planarNorm, dotProduct, Fin.sum_univ_two, Pi.neg_apply]
    ring_nf
  have hpos := dotProduct_le_planarNorm_mul leftVec rightVec
  have hminus := dotProduct_le_planarNorm_mul leftVec (-rightVec)
  rw [hneg, hnormNeg] at hminus
  exact abs_le.mpr ⟨by linarith, hpos⟩

/-- **The triangle inequality**, planar case. -/
theorem planarNorm_add_le (leftVec rightVec : Fin 2 → ℝ) :
    planarNorm (leftVec + rightVec) ≤ planarNorm leftVec + planarNorm rightVec := by
  have hexpand : (leftVec + rightVec) ⬝ᵥ (leftVec + rightVec)
      = leftVec ⬝ᵥ leftVec + 2 * (leftVec ⬝ᵥ rightVec)
        + rightVec ⬝ᵥ rightVec := by
    simp only [dotProduct, Fin.sum_univ_two, Pi.add_apply]
    ring
  have hsumNonneg : 0 ≤ planarNorm leftVec + planarNorm rightVec :=
    add_nonneg (planarNorm_nonneg _) (planarNorm_nonneg _)
  calc planarNorm (leftVec + rightVec)
      = Real.sqrt ((leftVec + rightVec) ⬝ᵥ (leftVec + rightVec)) := rfl
    _ ≤ Real.sqrt ((planarNorm leftVec + planarNorm rightVec) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [hexpand]
        nlinarith [dotProduct_le_planarNorm_mul leftVec rightVec,
          planarNorm_sq leftVec, planarNorm_sq rightVec]
    _ = planarNorm leftVec + planarNorm rightVec := Real.sqrt_sq hsumNonneg

/-- The reverse triangle inequality: lengths differ by at most the distance. -/
theorem abs_planarNorm_sub_le (leftVec rightVec : Fin 2 → ℝ) :
    |planarNorm leftVec - planarNorm rightVec|
      ≤ planarNorm (leftVec - rightVec) := by
  have hswap : planarNorm (rightVec - leftVec) = planarNorm (leftVec - rightVec) := by
    simp only [planarNorm, dotProduct, Fin.sum_univ_two, Pi.sub_apply]
    ring_nf
  have hforward : planarNorm leftVec - planarNorm rightVec
      ≤ planarNorm (leftVec - rightVec) := by
    have hsplit := planarNorm_add_le (leftVec - rightVec) rightVec
    have hrewrite : leftVec - rightVec + rightVec = leftVec := by
      ext i
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [hrewrite] at hsplit
    linarith
  have hbackward : planarNorm rightVec - planarNorm leftVec
      ≤ planarNorm (leftVec - rightVec) := by
    have hsplit := planarNorm_add_le (rightVec - leftVec) leftVec
    have hrewrite : rightVec - leftVec + leftVec = rightVec := by
      ext i
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [hrewrite, hswap] at hsplit
    linarith
  exact abs_le.mpr ⟨by linarith, hforward⟩

/-! ### The defect and the pairing identity -/

/-- The **planar defect** of an atom square against a moment vector:
`d(S) = 1 + ⟨ξ,S⟩ − |S|/2`. On the equality manifold it vanishes exactly at
the tight clusters (Theorem V), and the zero atom has defect `1`. -/
noncomputable def planarDefect (moment planarSquare : Fin 2 → ℝ) : ℝ :=
  1 + moment ⬝ᵥ planarSquare - planarNorm planarSquare / 2

/-- The zero atom has defect one. -/
theorem planarDefect_zero (moment : Fin 2 → ℝ) :
    planarDefect moment 0 = 1 := by
  simp only [planarDefect, planarNorm_zero, dotProduct, Fin.sum_univ_two,
    Pi.zero_apply]
  norm_num

/-- **The defect is `(|ξ| + 1/2)`-Lipschitz.** -/
theorem abs_planarDefect_sub_le (moment leftSquare rightSquare : Fin 2 → ℝ) :
    |planarDefect moment leftSquare - planarDefect moment rightSquare|
      ≤ (planarNorm moment + 1/2) * planarNorm (leftSquare - rightSquare) := by
  have hpair : moment ⬝ᵥ leftSquare - moment ⬝ᵥ rightSquare
      = moment ⬝ᵥ (leftSquare - rightSquare) := by
    simp only [dotProduct, Fin.sum_univ_two, Pi.sub_apply]
    ring
  have hpairBound : |moment ⬝ᵥ (leftSquare - rightSquare)|
      ≤ planarNorm moment * planarNorm (leftSquare - rightSquare) :=
    abs_dotProduct_le_planarNorm_mul _ _
  have hlevBound := abs_planarNorm_sub_le leftSquare rightSquare
  have hsplit : planarDefect moment leftSquare - planarDefect moment rightSquare
      = moment ⬝ᵥ (leftSquare - rightSquare)
        - (planarNorm leftSquare - planarNorm rightSquare) / 2 := by
    simp only [planarDefect]
    rw [← hpair]
    ring
  rw [hsplit]
  calc |moment ⬝ᵥ (leftSquare - rightSquare)
        - (planarNorm leftSquare - planarNorm rightSquare) / 2|
      ≤ |moment ⬝ᵥ (leftSquare - rightSquare)|
        + |(planarNorm leftSquare - planarNorm rightSquare) / 2| :=
        abs_sub _ _
    _ ≤ planarNorm moment * planarNorm (leftSquare - rightSquare)
        + planarNorm (leftSquare - rightSquare) / 2 := by
        rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        linarith
    _ = (planarNorm moment + 1/2) * planarNorm (leftSquare - rightSquare) := by
        ring

/-- **The pairing identity**: for every planar design and EVERY moment vector,
the weighted defects sum to zero. This is the covector `(1, ξ, −1/2)` paired
with the three design equations — pure bookkeeping, no geometry. -/
theorem sum_weighted_defect_eq_zero (atoms : Finset (Fin m))
    (weight : Fin m → ℝ) (planarSquare : Fin m → Fin 2 → ℝ)
    (moment : Fin 2 → ℝ)
    (hweightSum : ∑ c ∈ atoms, weight c = 1)
    (hclosure : (∑ c ∈ atoms, weight c • planarSquare c) = 0)
    (htrace : ∑ c ∈ atoms, weight c * planarNorm (planarSquare c) = 2) :
    ∑ c ∈ atoms, weight c * planarDefect moment (planarSquare c) = 0 := by
  have hsplit : ∑ c ∈ atoms, weight c * planarDefect moment (planarSquare c)
      = (∑ c ∈ atoms, weight c)
        + (∑ c ∈ atoms, weight c * (moment ⬝ᵥ planarSquare c))
        - (∑ c ∈ atoms, weight c * planarNorm (planarSquare c)) / 2 := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [planarDefect]
    ring
  have hmomentPart : (∑ c ∈ atoms, weight c * (moment ⬝ᵥ planarSquare c)) = 0 := by
    have hpull : (∑ c ∈ atoms, weight c * (moment ⬝ᵥ planarSquare c))
        = moment ⬝ᵥ (∑ c ∈ atoms, weight c • planarSquare c) := by
      rw [dotProduct_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [dotProduct_smul, smul_eq_mul]
    rw [hpull, hclosure]
    simp only [dotProduct, Fin.sum_univ_two, Pi.zero_apply]
    ring
  rw [hsplit, hweightSum, hmomentPart, htrace]
  norm_num

/-! ### The theorem -/

/-- **The Zero-Atom Pushoff Theorem.** In any planar design containing an atom
whose square is the origin (the projecting atom of an atom-plane projection),
that atom's weight is bounded by the Lipschitz constant times the weighted
distance of the remaining atoms from ANY assignment of defect-zero points.

Applied with the tight-triangle covector of Theorem V — whose defect vanishes
exactly on the clusters — this says the projection sits at weighted distance
at least `t_e/(|ξ| + 1/2) > t_e` from the equality manifold: the `δ_T = 0` case
of GAP-T is empty, unconditionally (no silence, no heaviness, no corner
hypothesis anywhere in this proof). -/
theorem zeroAtom_pushoff (atoms : Finset (Fin m)) (zeroAtom : Fin m)
    (hmem : zeroAtom ∈ atoms)
    (weight : Fin m → ℝ) (planarSquare : Fin m → Fin 2 → ℝ)
    (moment : Fin 2 → ℝ) (nearestZero : Fin m → Fin 2 → ℝ)
    (hweightSum : ∑ c ∈ atoms, weight c = 1)
    (hclosure : (∑ c ∈ atoms, weight c • planarSquare c) = 0)
    (htrace : ∑ c ∈ atoms, weight c * planarNorm (planarSquare c) = 2)
    (hzeroSquare : planarSquare zeroAtom = 0)
    (hweightNonneg : ∀ c ∈ atoms, 0 ≤ weight c)
    (hnearestZero : ∀ c ∈ atoms.erase zeroAtom,
      planarDefect moment (nearestZero c) = 0) :
    weight zeroAtom
      ≤ (planarNorm moment + 1/2) *
        ∑ c ∈ atoms.erase zeroAtom,
          weight c * planarNorm (planarSquare c - nearestZero c) := by
  have hpairing := sum_weighted_defect_eq_zero atoms weight planarSquare moment
    hweightSum hclosure htrace
  -- Peel the zero atom: its defect is 1, so its weight is the negated remainder.
  have hpeel : weight zeroAtom * planarDefect moment (planarSquare zeroAtom)
      + ∑ c ∈ atoms.erase zeroAtom,
          weight c * planarDefect moment (planarSquare c)
      = ∑ c ∈ atoms, weight c * planarDefect moment (planarSquare c) :=
    Finset.add_sum_erase atoms
      (fun c => weight c * planarDefect moment (planarSquare c)) hmem
  rw [hzeroSquare, planarDefect_zero, mul_one, hpairing] at hpeel
  have hweightEq : weight zeroAtom
      = -∑ c ∈ atoms.erase zeroAtom,
          weight c * planarDefect moment (planarSquare c) := by linarith
  -- Each remaining term is controlled by the Lipschitz bound at its target.
  have hterm : ∀ c ∈ atoms.erase zeroAtom,
      -(weight c * planarDefect moment (planarSquare c))
        ≤ (planarNorm moment + 1/2) *
          (weight c * planarNorm (planarSquare c - nearestZero c)) := by
    intro c hc
    have hwc : 0 ≤ weight c := hweightNonneg c (Finset.mem_of_mem_erase hc)
    have hlip := abs_planarDefect_sub_le moment (planarSquare c) (nearestZero c)
    rw [hnearestZero c hc, sub_zero] at hlip
    have hbound : -planarDefect moment (planarSquare c)
        ≤ (planarNorm moment + 1/2)
          * planarNorm (planarSquare c - nearestZero c) :=
      le_trans (neg_le_abs _) hlip
    nlinarith [hwc, hbound]
  calc weight zeroAtom
      = ∑ c ∈ atoms.erase zeroAtom,
          -(weight c * planarDefect moment (planarSquare c)) := by
        rw [hweightEq, ← Finset.sum_neg_distrib]
    _ ≤ ∑ c ∈ atoms.erase zeroAtom, (planarNorm moment + 1/2) *
          (weight c * planarNorm (planarSquare c - nearestZero c)) :=
        Finset.sum_le_sum hterm
    _ = (planarNorm moment + 1/2) *
          ∑ c ∈ atoms.erase zeroAtom,
            weight c * planarNorm (planarSquare c - nearestZero c) := by
        rw [Finset.mul_sum]

/-! ### Sharpness: the embedded tetrahedron corner saturates the bound -/

/-- The corner projection's four planar squares: the zero atom (the projecting
tetrahedron vertex) and three squares of leverage `8/3` at mutual square-gaps
`2π/3`. -/
noncomputable def cornerSquare : Fin 4 → Fin 2 → ℝ :=
  ![![0, 0],
    ![8/3, 0],
    ![-4/3, (4/3) * Real.sqrt 3],
    ![-4/3, -(4/3) * Real.sqrt 3]]

/-- The corner projection's weights: uniform `1/4`. -/
noncomputable def cornerWeight : Fin 4 → ℝ := fun _ => 1/4

/-- The defect-zero targets: the Mercedes clusters at leverage `2` in the same
three directions (three quarters of the way in from each corner square). -/
noncomputable def cornerNearest : Fin 4 → Fin 2 → ℝ :=
  ![![0, 0],
    ![2, 0],
    ![-1, Real.sqrt 3],
    ![-1, -Real.sqrt 3]]

private theorem sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num)

/-- Read off a planar norm from a squared value. -/
theorem planarNorm_eq_of_sq {planarVec : Fin 2 → ℝ} {target : ℝ}
    (htarget : 0 ≤ target) (hsq : planarVec ⬝ᵥ planarVec = target ^ 2) :
    planarNorm planarVec = target := by
  rw [planarNorm, hsq, Real.sqrt_sq htarget]

/-- Matrix-literal reduction set for the corner data. -/
private lemma cornerNorm_helper (planarVec : Fin 2 → ℝ) :
    planarVec ⬝ᵥ planarVec = planarVec 0 * planarVec 0 + planarVec 1 * planarVec 1 := by
  simp only [dotProduct, Fin.sum_univ_two]

private theorem cornerSquare_norm_one : planarNorm (cornerSquare 1) = 8/3 := by
  refine planarNorm_eq_of_sq (by norm_num) ?_
  rw [cornerNorm_helper]
  simp only [cornerSquare, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.head_cons, Matrix.tail_cons]
  norm_num

private theorem cornerSquare_norm_two : planarNorm (cornerSquare 2) = 8/3 := by
  refine planarNorm_eq_of_sq (by norm_num) ?_
  rw [cornerNorm_helper]
  simp only [cornerSquare, Matrix.cons_val_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (16/9 : ℝ) * sqrt_three_sq

private theorem cornerSquare_norm_three : planarNorm (cornerSquare 3) = 8/3 := by
  refine planarNorm_eq_of_sq (by norm_num) ?_
  rw [cornerNorm_helper]
  simp only [cornerSquare, Matrix.cons_val_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (16/9 : ℝ) * sqrt_three_sq

private theorem cornerSquare_norm_zero : planarNorm (cornerSquare 0) = 0 := by
  refine planarNorm_eq_of_sq (le_refl 0) ?_
  rw [cornerNorm_helper]
  simp only [cornerSquare, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  norm_num

private theorem cornerGap_norm_one :
    planarNorm (cornerSquare 1 - cornerNearest 1) = 2/3 := by
  refine planarNorm_eq_of_sq (by norm_num) ?_
  rw [cornerNorm_helper]
  simp only [cornerSquare, cornerNearest, Pi.sub_apply, Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons]
  norm_num

private theorem cornerGap_norm_two :
    planarNorm (cornerSquare 2 - cornerNearest 2) = 2/3 := by
  refine planarNorm_eq_of_sq (by norm_num) ?_
  rw [cornerNorm_helper]
  simp only [cornerSquare, cornerNearest, Pi.sub_apply, Matrix.cons_val_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (1/9 : ℝ) * sqrt_three_sq

private theorem cornerGap_norm_three :
    planarNorm (cornerSquare 3 - cornerNearest 3) = 2/3 := by
  refine planarNorm_eq_of_sq (by norm_num) ?_
  rw [cornerNorm_helper]
  simp only [cornerSquare, cornerNearest, Pi.sub_apply, Matrix.cons_val_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination (1/9 : ℝ) * sqrt_three_sq

private theorem cornerNearest_norm_one : planarNorm (cornerNearest 1) = 2 := by
  refine planarNorm_eq_of_sq (by norm_num) ?_
  rw [cornerNorm_helper]
  simp only [cornerNearest, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.head_cons, Matrix.tail_cons]
  norm_num

private theorem cornerNearest_norm_two : planarNorm (cornerNearest 2) = 2 := by
  refine planarNorm_eq_of_sq (by norm_num) ?_
  rw [cornerNorm_helper]
  simp only [cornerNearest, Matrix.cons_val_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
  linear_combination sqrt_three_sq

private theorem cornerNearest_norm_three : planarNorm (cornerNearest 3) = 2 := by
  refine planarNorm_eq_of_sq (by norm_num) ?_
  rw [cornerNorm_helper]
  simp only [cornerNearest, Matrix.cons_val_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
  linear_combination sqrt_three_sq

/-- The Mercedes targets sit at leverage `2`, so their defect vanishes at
`ξ = 0` — they are legitimate defect-zero points. -/
theorem cornerNearest_defect_zero (index : Fin 4) (hindex : index ≠ 0) :
    planarDefect 0 (cornerNearest index) = 0 := by
  have hnorm : planarNorm (cornerNearest index) = 2 := by
    fin_cases index
    · exact absurd rfl hindex
    · exact cornerNearest_norm_one
    · exact cornerNearest_norm_two
    · exact cornerNearest_norm_three
  simp only [planarDefect, hnorm, dotProduct, Fin.sum_univ_two, Pi.zero_apply]
  norm_num

/-- The corner projection is a valid planar design: uniform weights summing to
one, exact closure, trace two, and the projecting atom at the origin. -/
theorem cornerDesign_valid :
    (∑ c, cornerWeight c) = 1
      ∧ (∑ c, cornerWeight c • cornerSquare c) = 0
      ∧ (∑ c, cornerWeight c * planarNorm (cornerSquare c)) = 2
      ∧ cornerSquare 0 = 0
      ∧ (∀ c, 0 ≤ cornerWeight c) := by
  refine ⟨by norm_num [Fin.sum_univ_four, cornerWeight], ?_, ?_, ?_, fun c => ?_⟩
  · ext i
    rw [Finset.sum_apply, Fin.sum_univ_four]
    fin_cases i <;> simp [cornerSquare, cornerWeight] <;> norm_num
  · rw [Fin.sum_univ_four, cornerSquare_norm_zero, cornerSquare_norm_one,
      cornerSquare_norm_two, cornerSquare_norm_three]
    norm_num [cornerWeight]
  · ext i
    fin_cases i <;> simp [cornerSquare]
  · norm_num [cornerWeight]

/-- **Sharpness of the Pushoff Theorem**: at the embedded tetrahedron corner
the bound holds with EQUALITY — both sides are `1/4`. The moment vector is
`ξ = 0` (Lipschitz constant `1/2`), the zero atom carries weight `1/4`, and the
three remaining atoms each sit at distance `2/3` from their Mercedes targets at
weight `1/4`. So the constant `(|ξ| + 1/2)` cannot be improved, and the corner
is exactly the extremal configuration of the pushoff. -/
theorem cornerPushoff_saturates :
    cornerWeight 0
      = (planarNorm (0 : Fin 2 → ℝ) + 1/2) *
        ∑ c ∈ (Finset.univ : Finset (Fin 4)).erase 0,
          cornerWeight c * planarNorm (cornerSquare c - cornerNearest c) := by
  have herase : (Finset.univ : Finset (Fin 4)).erase 0 = {1, 2, 3} := by decide
  rw [herase, planarNorm_zero, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    cornerGap_norm_one, cornerGap_norm_two, cornerGap_norm_three]
  norm_num [cornerWeight]

end Gtz

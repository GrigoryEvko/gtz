import Gtz.Wave.OppositeHornScalarSystem
import Gtz.Wave.KOneAnchor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The failure direction of a complement that does not dominate

Every tie refuses EVERY triple, the complement `Cᶜ` included.  So at a tie the
complement carries a FAILURE DIRECTION: a unit probe it reads at most one.  This
module prices that direction, and the price is paid by the inside atoms.

The mechanism is Parseval read at the probe.  The weighted readings of all six
atoms total the probe's own square, and the outside part of that total is capped
by the largest outside weight times the complement's own reading.  So a
complement that fails hands the inside triple almost the whole Parseval mass:

* `Gtz.failureDirection_inside_share` — `1 − tcap ≤ Σ_{e ∈ C} t_e (g_e·v)²`,
  for ANY subset of ANY design, with no corner and no tie.
* `Gtz.failureDirection_inside_mass` — dividing by the largest inside weight,
  `1 − tcap ≤ tin · Σ_{e ∈ C} (g_e·v)²`: the inside atoms are long along `v`,
  or heavy, or both.
* `Gtz.exists_inside_reads_failureDirection` — hence SOME inside atom reads the
  failure direction, `(1 − tcap) ≤ tin · |C| · (g_e·v)²`.  This is the atom a
  repair must swap in.
* `Gtz.corner_failureDirection_axis_bound` — at a corank-two corner the inside
  unweighted reading is exactly `1 + λ(u·v)²`, so a failing complement forces

    `1 − tcap ≤ tin · (1 + λ·(u·v)²)` ,

  a necessary condition on the corner scalars and the axis reading alone.  A
  corner with light inside weights can only fail its complement by leaning the
  failure direction onto the gap axis.

All four are FIELD-BLIND, and deliberately so: they hold verbatim at the complex
corner tie, which is itself a complement failure.  The field enters one step
later, in whether the named atom's triple actually dominates — and that step,
not these, is where the two-point form must be spent.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The unweighted reading of a subset -/

/-- A subset sum reads a probe by the total of its squared atom readings. -/
theorem subsetSum_quadForm (D : WeightedDesign m 3) (C : Finset (Fin m))
    (v : Fin 3 → ℝ) :
    v ⬝ᵥ (subsetSum D C *ᵥ v) = ∑ c ∈ C, (D.atom c ⬝ᵥ v) ^ 2 := by
  classical
  rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show atomMatrix (D.atom c) *ᵥ v = (D.atom c ⬝ᵥ v) • D.atom c from
      vecMulVec_mulVec_eq _ _ _, dotProduct_smul, smul_eq_mul,
    dotProduct_comm v (D.atom c)]
  ring

/-! ## 2. The share the inside atoms must carry -/

/-- **THE FAILURE DIRECTION IS CARRIED BY THE INSIDE ATOMS.**  If the complement
of `C` reads the unit probe `v` at most one — which every tie forces, since a
tie refuses the complement too — then the weighted readings of `C` total at
least `1 − tcap`, with `tcap` any bound on the complement's weights.

Parseval read at `v`, split along `C`, with the complement's weighted total
capped by `tcap` times its own reading.  No corner, no tie, any subset. -/
theorem failureDirection_inside_share (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {v : Fin 3 → ℝ} (hv : v ⬝ᵥ v = 1)
    {tcap : ℝ} (htcap0 : 0 ≤ tcap)
    (hcap : ∀ d ∈ (Cᶜ : Finset (Fin m)), D.weight d ≤ tcap)
    (hfail : ∑ d ∈ (Cᶜ : Finset (Fin m)), (D.atom d ⬝ᵥ v) ^ 2 ≤ 1) :
    1 - tcap ≤ ∑ e ∈ C, D.weight e * (D.atom e ⬝ᵥ v) ^ 2 := by
  classical
  have hpars := parseval_probe_form D v
  rw [hv] at hpars
  have hsplit : (∑ e ∈ C, D.weight e * (D.atom e ⬝ᵥ v) ^ 2)
      + ∑ d ∈ (Cᶜ : Finset (Fin m)), D.weight d * (D.atom d ⬝ᵥ v) ^ 2
      = ∑ c, D.weight c * (D.atom c ⬝ᵥ v) ^ 2 :=
    Finset.sum_add_sum_compl C _
  -- the complement's weighted total is capped by tcap times its own reading
  have hout : ∑ d ∈ (Cᶜ : Finset (Fin m)), D.weight d * (D.atom d ⬝ᵥ v) ^ 2
      ≤ ∑ d ∈ (Cᶜ : Finset (Fin m)), tcap * (D.atom d ⬝ᵥ v) ^ 2 :=
    Finset.sum_le_sum fun d hd =>
      mul_le_mul_of_nonneg_right (hcap d hd) (sq_nonneg _)
  have hpull : ∑ d ∈ (Cᶜ : Finset (Fin m)), tcap * (D.atom d ⬝ᵥ v) ^ 2
      = tcap * ∑ d ∈ (Cᶜ : Finset (Fin m)), (D.atom d ⬝ᵥ v) ^ 2 :=
    (Finset.mul_sum _ _ _).symm
  have hchain : ∑ d ∈ (Cᶜ : Finset (Fin m)), D.weight d * (D.atom d ⬝ᵥ v) ^ 2
      ≤ tcap := by
    refine le_trans hout ?_
    rw [hpull]
    nlinarith [hfail, htcap0]
  linarith [hsplit, hpars, hchain]

/-- **THE INSIDE MASS BOUND.**  Dividing the share by the largest inside weight:
the inside atoms of a failing complement are long along the failure direction,
or heavy, or both. -/
theorem failureDirection_inside_mass (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {v : Fin 3 → ℝ} (hv : v ⬝ᵥ v = 1)
    {tcap tin : ℝ} (htcap0 : 0 ≤ tcap)
    (hcap : ∀ d ∈ (Cᶜ : Finset (Fin m)), D.weight d ≤ tcap)
    (hin : ∀ e ∈ C, D.weight e ≤ tin)
    (hfail : ∑ d ∈ (Cᶜ : Finset (Fin m)), (D.atom d ⬝ᵥ v) ^ 2 ≤ 1) :
    1 - tcap ≤ tin * ∑ e ∈ C, (D.atom e ⬝ᵥ v) ^ 2 := by
  classical
  refine le_trans (failureDirection_inside_share D C hv htcap0 hcap hfail) ?_
  calc ∑ e ∈ C, D.weight e * (D.atom e ⬝ᵥ v) ^ 2
      ≤ ∑ e ∈ C, tin * (D.atom e ⬝ᵥ v) ^ 2 :=
        Finset.sum_le_sum fun e he =>
          mul_le_mul_of_nonneg_right (hin e he) (sq_nonneg _)
    _ = tin * ∑ e ∈ C, (D.atom e ⬝ᵥ v) ^ 2 := (Finset.mul_sum _ _ _).symm

/-- **SOME INSIDE ATOM READS THE FAILURE DIRECTION.**  The atom a repair must
swap in: at least one member of `C` carries `(1 − tcap)/(tin·|C|)` of the
squared reading. -/
theorem exists_inside_reads_failureDirection (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {v : Fin 3 → ℝ} (hv : v ⬝ᵥ v = 1)
    {tcap tin : ℝ} (htcap0 : 0 ≤ tcap)
    (hcap : ∀ d ∈ (Cᶜ : Finset (Fin m)), D.weight d ≤ tcap)
    (hin : ∀ e ∈ C, D.weight e ≤ tin)
    (hfail : ∑ d ∈ (Cᶜ : Finset (Fin m)), (D.atom d ⬝ᵥ v) ^ 2 ≤ 1)
    (hne : C.Nonempty) :
    ∃ e ∈ C, 1 - tcap ≤ tin * (C.card : ℝ) * (D.atom e ⬝ᵥ v) ^ 2 := by
  classical
  obtain ⟨e, heC, hemax⟩ :=
    C.exists_max_image (fun c => (D.atom c ⬝ᵥ v) ^ 2) hne
  refine ⟨e, heC, ?_⟩
  have hmass := failureDirection_inside_mass D C hv htcap0 hcap hin hfail
  have hbound : ∑ c ∈ C, (D.atom c ⬝ᵥ v) ^ 2
      ≤ (C.card : ℝ) * (D.atom e ⬝ᵥ v) ^ 2 := by
    calc ∑ c ∈ C, (D.atom c ⬝ᵥ v) ^ 2
        ≤ ∑ _c ∈ C, (D.atom e ⬝ᵥ v) ^ 2 :=
          Finset.sum_le_sum fun c hc => hemax c hc
      _ = (C.card : ℝ) * (D.atom e ⬝ᵥ v) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have htin : 0 ≤ tin := le_trans (D.weight_pos e).le (hin e heC)
  nlinarith [hmass, hbound, htin, sq_nonneg (D.atom e ⬝ᵥ v)]

/-! ## 3. The corner form -/

/-- **THE CORNER READS ITS OWN AXIS.**  At a corank-two corner the unweighted
inside reading of a unit probe is `1 + λ(u·v)²`. -/
theorem corner_inside_quadForm (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {v : Fin 3 → ℝ} (hv : v ⬝ᵥ v = 1) :
    ∑ e ∈ C, (D.atom e ⬝ᵥ v) ^ 2 = 1 + lam * (u ⬝ᵥ v) ^ 2 := by
  have hsum : subsetSum D C = 1 + lam • atomMatrix u := by
    rw [← hgap]; abel
  rw [← subsetSum_quadForm, hsum, Matrix.add_mulVec, dotProduct_add,
    Matrix.one_mulVec, hv, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    show atomMatrix u *ᵥ v = (u ⬝ᵥ v) • u from vecMulVec_mulVec_eq _ _ _,
    dotProduct_smul, smul_eq_mul, dotProduct_comm v u]
  ring

/-- **THE AXIS BOUND OF A FAILING COMPLEMENT.**  At a corank-two corner, a
complement that fails to dominate forces

  `1 − tcap ≤ tin·(1 + λ·(u·v)²)` .

Light inside weights can only fail the complement by leaning the failure
direction onto the gap axis: with `tin` small the reading `(u·v)²` must carry
the whole deficit, at the rate `1/(tin·λ)`. -/
theorem corner_failureDirection_axis_bound (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {v : Fin 3 → ℝ} (hv : v ⬝ᵥ v = 1)
    {tcap tin : ℝ} (htcap0 : 0 ≤ tcap)
    (hcap : ∀ d ∈ (Cᶜ : Finset (Fin m)), D.weight d ≤ tcap)
    (hin : ∀ e ∈ C, D.weight e ≤ tin)
    (hfail : ∑ d ∈ (Cᶜ : Finset (Fin m)), (D.atom d ⬝ᵥ v) ^ 2 ≤ 1) :
    1 - tcap ≤ tin * (1 + lam * (u ⬝ᵥ v) ^ 2) := by
  have h := failureDirection_inside_mass D C hv htcap0 hcap hin hfail
  rwa [corner_inside_quadForm D C hgap hv] at h

/-- The failure direction of a complement gap that is not positive definite,
packaged: a unit probe the complement reads at most one. -/
theorem exists_failureDirection_of_not_posDef (D : WeightedDesign m 3)
    (C : Finset (Fin m))
    (hnot : ¬ (subsetSum D (Cᶜ : Finset (Fin m)) - 1).PosDef) :
    ∃ v : Fin 3 → ℝ, v ⬝ᵥ v = 1 ∧
      ∑ d ∈ (Cᶜ : Finset (Fin m)), (D.atom d ⬝ᵥ v) ^ 2 ≤ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  refine hnot (Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩)
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_sub, Matrix.transpose_one]
    congr 1
    exact transpose_eq_of_isHermitian (subsetSum_isHermitian D _)
  · rw [star_trivial]
    -- normalise x and apply the hypothesis at the unit probe
    have hxx : 0 < x ⬝ᵥ x := dotProduct_self_pos hx
    set n : ℝ := Real.sqrt (x ⬝ᵥ x) with hn
    have hnpos : 0 < n := Real.sqrt_pos.mpr hxx
    set v : Fin 3 → ℝ := (1 / n) • x with hvdef
    have hvv : v ⬝ᵥ v = 1 := by
      rw [hvdef, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hn]
      field_simp
      rw [Real.sq_sqrt hxx.le]
    have hgt := hcon v hvv
    have hread : ∀ d, (D.atom d ⬝ᵥ v) ^ 2 = (1 / n) ^ 2 * (D.atom d ⬝ᵥ x) ^ 2 := by
      intro d
      rw [hvdef, dotProduct_smul, smul_eq_mul]
      ring
    have hform : x ⬝ᵥ ((subsetSum D (Cᶜ : Finset (Fin m)) - 1) *ᵥ x)
        = (∑ d ∈ (Cᶜ : Finset (Fin m)), (D.atom d ⬝ᵥ x) ^ 2) - x ⬝ᵥ x := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, subsetSum_quadForm]
    have hscale : (∑ d ∈ (Cᶜ : Finset (Fin m)), (D.atom d ⬝ᵥ v) ^ 2)
        = (1 / n) ^ 2 * ∑ d ∈ (Cᶜ : Finset (Fin m)), (D.atom d ⬝ᵥ x) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => hread d
    rw [hscale] at hgt
    have hnx : n ^ 2 = x ⬝ᵥ x := by rw [hn, Real.sq_sqrt hxx.le]
    have hinv : (0:ℝ) < (1 / n) ^ 2 := by positivity
    have hkey : (1 / n) ^ 2 * (x ⬝ᵥ x) = 1 := by
      rw [← hnx]
      field_simp
    have hlt : x ⬝ᵥ x < ∑ d ∈ (Cᶜ : Finset (Fin m)), (D.atom d ⬝ᵥ x) ^ 2 := by
      have hstep : (1 / n) ^ 2 * (x ⬝ᵥ x)
          < (1 / n) ^ 2 * ∑ d ∈ (Cᶜ : Finset (Fin m)), (D.atom d ⬝ᵥ x) ^ 2 := by
        rw [hkey]; exact hgt
      exact lt_of_mul_lt_mul_left hstep hinv.le
    rw [hform]
    linarith [hlt]

end Gtz

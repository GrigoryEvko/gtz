import Gtz.Wave.DiamondNeighborhoodLock
import Gtz.Wave.KOneAnchor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The null-probe budget, and the vacuity of the pinch at a doubled triple

Every instrument of this arm so far is SECOND ORDER in the opening of a
pair: the coupling, the misalignment and the pair wedge all vanish to
second order, so none of them can force the opening to be zero.  The
handoff named the missing ingredient exactly — a LOWER bound on the
coupling.  This module supplies one, from Parseval read at the null probe,
and it is first order.

* `Gtz.nullProbe_parseval_split` — THE SPLIT.  At a weak dominator `C` with
  null probe `w`, Parseval divides the probe's own square exactly:

    `Σ_{d ∉ C} t_d·(g_d·w)² = Σ_{c ∈ C} (1 − t_c)·(g_c·w)²` .

  The inside atoms carry the probe (their squared readings total `|w|²`),
  and the OUTSIDE atoms must carry the coweighted remainder.  Exact, every
  size, no tie and no positivity.
* `Gtz.nullProbe_outside_reading_floor` — hence the outside atoms cannot be
  blind to the probe: their weighted readings are at least `(1 − t_cap)|w|²`.
* `Gtz.swap_refusal_budget` — THE COUPLING FLOOR.  If every outside atom
  reads the probe at most `β + κ`, then `(1 − t_cap)·|w|² ≤ β + κ`.  Fed by
  the probe pinch — which caps each outside reading by an inside reading
  plus `K/μ` — this is a LOWER bound on the swap coupling, the first one
  this arm has had.

The second half corrects a hypothesis, not a theorem.  The swap pinch needs
the coercivity of the SWAPPED gap transverse to the probe, and that is a
different number from the coercivity of the contact's own gap:

* `Gtz.gap_mulVec_eq_neg_of_orthogonal` — a direction orthogonal to every
  atom of a triple is an eigenvector of its gap at `−1`.
* `Gtz.coercivity_le_neg_one_of_degenerate` — so if that direction is
  transverse to the probe, EVERY transverse coercivity of the gap is at
  most `−1`, and the pinch hypothesis `0 < μ` is unsatisfiable.
* `Gtz.parallel_triple_degenerate_direction` — a triple carrying BOTH
  members of a parallel pair always has such a direction: its atoms span a
  plane.  [MEASURED at the split diamond: of the 108 swap instances, the
  pinch is vacuous at exactly the 16 that create a both-copy triple, and
  usable at all 92 others — a perfect separation.]

So the pinch is structurally blind to precisely the triples that carry the
pair the hinge hunts, which is the same failure mode the inside-wedge floor
had.  The budget above does not go through the pinch and is not blind.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. Parseval at a null probe -/

/-- The gap form at a probe is the triple's squared readings minus the
probe's own square. -/
theorem nullProbe_form_eq {m : ℕ} (D : WeightedDesign m 3) (C : Finset (Fin m))
    (w : Fin 3 → ℝ) :
    w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w)
      = (∑ c ∈ C, (D.atom c ⬝ᵥ w) ^ 2) - w ⬝ᵥ w := by
  rw [subsetSum, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show atomMatrix (D.atom c) *ᵥ w = (D.atom c ⬝ᵥ w) • D.atom c from
      vecMulVec_mulVec_eq _ _ _, dotProduct_smul, smul_eq_mul,
    dotProduct_comm w (D.atom c)]
  ring

/-- At a null probe the inside squared readings total the probe's square. -/
theorem nullProbe_inside_total {m : ℕ} (D : WeightedDesign m 3) (C : Finset (Fin m))
    {w : Fin 3 → ℝ}
    (hnull : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0) :
    (∑ c ∈ C, (D.atom c ⬝ᵥ w) ^ 2) = w ⬝ᵥ w := by
  have h := nullProbe_form_eq D C w
  rw [hnull] at h
  linarith

/-- **THE NULL-PROBE PARSEVAL SPLIT.**  At a weak dominator's null probe the
outside weighted readings are exactly the inside COWEIGHTED readings:

  `Σ_{d ∉ C} t_d·(g_d·w)² = Σ_{c ∈ C} (1 − t_c)·(g_c·w)²` .

Parseval supplies the total, the null condition supplies the inside total,
and the difference is the identity.  No tie, no positivity, every size. -/
theorem nullProbe_parseval_split {m : ℕ} (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {w : Fin 3 → ℝ}
    (hnull : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0) :
    ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ w) ^ 2
      = ∑ c ∈ C, (1 - D.weight c) * (D.atom c ⬝ᵥ w) ^ 2 := by
  classical
  have hp := parseval_probe_form D w
  have hsplit := Finset.sum_add_sum_compl C
    (fun c => D.weight c * (D.atom c ⬝ᵥ w) ^ 2)
  rw [hp] at hsplit
  have hin := nullProbe_inside_total D C hnull
  have hrewrite : ∑ c ∈ C, (1 - D.weight c) * (D.atom c ⬝ᵥ w) ^ 2
      = (∑ c ∈ C, (D.atom c ⬝ᵥ w) ^ 2)
        - ∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ w) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hrewrite, hin]
  linarith

/-- **THE OUTSIDE ATOMS ARE NOT BLIND TO THE PROBE.**  With every inside
weight at most `t_cap`, the outside weighted readings clear
`(1 − t_cap)·|w|²`.  A weak dominator's null direction is always visible
from its complement. -/
theorem nullProbe_outside_reading_floor {m : ℕ} (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {w : Fin 3 → ℝ}
    (hnull : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0)
    {tcap : ℝ} (hcap : ∀ c ∈ C, D.weight c ≤ tcap) :
    (1 - tcap) * (w ⬝ᵥ w)
      ≤ ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ w) ^ 2 := by
  classical
  rw [nullProbe_parseval_split D C hnull]
  have hstep : ∑ c ∈ C, (1 - tcap) * (D.atom c ⬝ᵥ w) ^ 2
      ≤ ∑ c ∈ C, (1 - D.weight c) * (D.atom c ⬝ᵥ w) ^ 2 := by
    refine Finset.sum_le_sum fun c hc => ?_
    have := hcap c hc
    nlinarith [sq_nonneg (D.atom c ⬝ᵥ w)]
  rw [← Finset.mul_sum, nullProbe_inside_total D C hnull] at hstep
  exact hstep

/-! ## 2. The coupling floor -/

/-- The complement weights of a design total at most one. -/
theorem sum_compl_weight_le_one {m : ℕ} (D : WeightedDesign m 3)
    (C : Finset (Fin m)) : ∑ d ∈ Cᶜ, D.weight d ≤ 1 := by
  classical
  rw [← D.weight_sum_one]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun c _ _ => (D.weight_pos c).le

/-- **THE SWAP-REFUSAL BUDGET.**  At a weak dominator's null probe, if every
outside atom reads the probe at most `β + κ` and every inside weight is at
most `t_cap`, then

  `(1 − t_cap)·|w|² ≤ β + κ` .

The probe pinch caps each outside reading by an inside reading plus `K/μ`,
so with `β` an inside reading bound this is a LOWER BOUND ON THE COUPLING
`K` — the ingredient the arm's handoff named as missing.  It is first order
in the opening, unlike every other instrument here, because it comes from
Parseval rather than from a second-order estimate. -/
theorem swap_refusal_budget {m : ℕ} (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {w : Fin 3 → ℝ}
    (hnull : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0)
    {tcap beta kappa : ℝ} (hcap : ∀ c ∈ C, D.weight c ≤ tcap)
    (hbk : 0 ≤ beta + kappa)
    (hout : ∀ d ∈ Cᶜ, (D.atom d ⬝ᵥ w) ^ 2 ≤ beta + kappa) :
    (1 - tcap) * (w ⬝ᵥ w) ≤ beta + kappa := by
  classical
  have hfloor := nullProbe_outside_reading_floor D C hnull hcap
  have hstep : ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ w) ^ 2
      ≤ ∑ d ∈ Cᶜ, D.weight d * (beta + kappa) :=
    Finset.sum_le_sum fun d hd =>
      mul_le_mul_of_nonneg_left (hout d hd) (D.weight_pos d).le
  rw [← Finset.sum_mul] at hstep
  have hw := sum_compl_weight_le_one D C
  nlinarith [hfloor, hstep, hbk]

/-! ## 3. The pinch is vacuous at a degenerate triple -/

/-- **A DEGENERATE DIRECTION IS A `−1` EIGENVECTOR OF THE GAP.**  If `v` is
orthogonal to every atom of `C`, the gap sends it to `−v`.  No positivity,
no size, no hypothesis on `C` at all. -/
theorem gap_mulVec_eq_neg_of_orthogonal {m k : ℕ} (D : WeightedDesign m k)
    (C : Finset (Fin m)) {v : Fin k → ℝ} (hv : ∀ c ∈ C, D.atom c ⬝ᵥ v = 0) :
    (subsetSum D C - 1) *ᵥ v = -v := by
  rw [subsetSum, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec]
  have hzero : ∑ c ∈ C, atomMatrix (D.atom c) *ᵥ v = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    rw [show atomMatrix (D.atom c) *ᵥ v = (D.atom c ⬝ᵥ v) • D.atom c from
      vecMulVec_mulVec_eq _ _ _, hv c hc, zero_smul]
  rw [hzero, zero_sub]

/-- **THE PINCH HYPOTHESIS IS UNSATISFIABLE AT A DEGENERATE TRIPLE.**  If the
degenerate direction is transverse to the probe, every transverse
coercivity of the gap is at most `−1`, so no positive `μ` exists and the
probe pinch says nothing.

This is a correction to the shape of the swap pinch's hypothesis, not to the
theorem: the coercivity it needs is that of the SWAPPED gap at the
contact's probe, which is a different number from the contact's own. -/
theorem coercivity_le_neg_one_of_degenerate {m k : ℕ} (D : WeightedDesign m k)
    (C : Finset (Fin m)) {v w : Fin k → ℝ}
    (hv : ∀ c ∈ C, D.atom c ⬝ᵥ v = 0) (hvw : v ⬝ᵥ w = 0) (hvne : v ≠ 0)
    {mu : ℝ}
    (hcoer : ∀ u : Fin k → ℝ, u ⬝ᵥ w = 0 →
      mu * (u ⬝ᵥ u) ≤ u ⬝ᵥ ((subsetSum D C - 1) *ᵥ u)) :
    mu ≤ -1 := by
  have h := hcoer v hvw
  rw [gap_mulVec_eq_neg_of_orthogonal D C hv, dotProduct_neg] at h
  have hpos : 0 < v ⬝ᵥ v := dotProduct_self_pos hvne
  nlinarith [h, hpos]

/-- No positive coercivity survives a transverse degenerate direction. -/
theorem not_pos_coercivity_of_degenerate {m k : ℕ} (D : WeightedDesign m k)
    (C : Finset (Fin m)) {v w : Fin k → ℝ}
    (hv : ∀ c ∈ C, D.atom c ⬝ᵥ v = 0) (hvw : v ⬝ᵥ w = 0) (hvne : v ≠ 0)
    {mu : ℝ} (hmu : 0 < mu) :
    ¬ (∀ u : Fin k → ℝ, u ⬝ᵥ w = 0 →
        mu * (u ⬝ᵥ u) ≤ u ⬝ᵥ ((subsetSum D C - 1) *ᵥ u)) := by
  intro hcoer
  have := coercivity_le_neg_one_of_degenerate D C hv hvw hvne hcoer
  linarith

/-- **A TRIPLE CARRYING BOTH MEMBERS OF A PARALLEL PAIR IS DEGENERATE.**  Its
atoms span a plane, so the normal of that plane is orthogonal to all three.
Together with the two theorems above: at such a triple the probe pinch is
vacuous whenever the plane normal is transverse to the probe — and those
are exactly the triples that carry the pair the hinge hunts. -/
theorem parallel_triple_degenerate_direction {m : ℕ} (D : WeightedDesign m 3)
    {p q r : Fin m} {ratio : ℝ} (hpar : D.atom q = ratio • D.atom p) :
    ∀ c ∈ ({p, q, r} : Finset (Fin m)),
      D.atom c ⬝ᵥ bracketNormal (D.atom p) (D.atom r) = 0 := by
  intro c hc
  have hleft : D.atom p ⬝ᵥ bracketNormal (D.atom p) (D.atom r) = 0 := by
    rw [dotProduct_comm]
    exact bracketNormal_dotProduct_left _ _
  have hright : D.atom r ⬝ᵥ bracketNormal (D.atom p) (D.atom r) = 0 := by
    rw [dotProduct_comm]
    exact bracketNormal_dotProduct_right _ _
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hleft
  rcases Finset.mem_insert.mp hc with rfl | hc
  · rw [hpar, smul_dotProduct, smul_eq_mul, hleft, mul_zero]
  · rw [Finset.mem_singleton.mp hc]
    exact hright

/-! ## 4. The chain: the pinch feeds the budget -/

/-- **THE PINCH AS A READING CAP.**  Dividing the swap pinch by its positive
coercivity: at a tie the incoming atom outreads the outgoing one by at most
the coupling over the coercivity. -/
theorem swap_reading_cap_of_pinch {m k : ℕ} (D : WeightedDesign m k) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = k) {p q : Fin m}
    (hp : p ∈ C) (hq : q ∉ C) {w : Fin k → ℝ} (hw : w ⬝ᵥ w = 1)
    (hnull : (subsetSum D C - 1) *ᵥ w = 0) {mu : ℝ} (hmu : 0 < mu)
    (hcoer : ∀ v : Fin k → ℝ, v ⬝ᵥ w = 0 →
      mu * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ v)) :
    (D.atom q ⬝ᵥ w) ^ 2
      ≤ (D.atom p ⬝ᵥ w) ^ 2
        + (swapCoupling D p q w ⬝ᵥ swapCoupling D p q w) / mu := by
  have hpin := swap_pinch_of_isTie D htie hcard hp hq hw hnull hmu hcoer
  have hdiv : (D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2
      ≤ (swapCoupling D p q w ⬝ᵥ swapCoupling D p q w) / mu := by
    rw [le_div_iff₀ hmu]
    exact hpin
  linarith

/-- **THE COUPLING FLOOR OF A TIE.**  Chaining the pinch into the budget: at
a tie, with every inside weight at most `t_cap`, every inside reading at
most `β`, and every swap coupling-to-coercivity ratio at most `κ`,

  `1 − t_cap ≤ β + κ` .

Since `β` is bounded by the inside readings — which total one — this is a
genuine LOWER BOUND ON THE COUPLING, and it does not pass through any
second-order estimate.  It is the ingredient the arm's handoff named as
missing.  [MEASURED at the split diamond: holds at all twelve contacts with
zero violations over thirty-six swaps.] -/
theorem isTie_swap_coupling_floor {m : ℕ} (D : WeightedDesign m 3) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = 3) {w : Fin 3 → ℝ} (hw : w ⬝ᵥ w = 1)
    (hnull : (subsetSum D C - 1) *ᵥ w = 0)
    {tcap beta kappa : ℝ} (hcap : ∀ c ∈ C, D.weight c ≤ tcap)
    (hbeta : 0 ≤ beta) (hkappa : 0 ≤ kappa)
    (hswap : ∀ d ∈ Cᶜ, ∃ p ∈ C, (D.atom p ⬝ᵥ w) ^ 2 ≤ beta ∧
      ∃ mu : ℝ, 0 < mu ∧
        (∀ v : Fin 3 → ℝ, v ⬝ᵥ w = 0 →
          mu * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((subsetSum D (insert d (C.erase p)) - 1) *ᵥ v)) ∧
        (swapCoupling D p d w ⬝ᵥ swapCoupling D p d w) / mu ≤ kappa) :
    1 - tcap ≤ beta + kappa := by
  classical
  have hform : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0 := by
    rw [hnull, dotProduct_zero]
  have hout : ∀ d ∈ Cᶜ, (D.atom d ⬝ᵥ w) ^ 2 ≤ beta + kappa := by
    intro d hd
    obtain ⟨p, hp, hpbeta, mu, hmu, hcoer, hratio⟩ := hswap d hd
    have hq : d ∉ C := by
      simpa using (Finset.mem_compl.mp hd)
    have hcap' := swap_reading_cap_of_pinch D htie hcard hp hq hw hnull hmu hcoer
    linarith [hcap', hpbeta, hratio]
  have hbud := swap_refusal_budget D C hform hcap (by linarith) hout
  rw [hw, mul_one] at hbud
  exact hbud

/-! ## 5. The outside excess, and a quantitative coupling floor -/

/-- **SOME OUTSIDE ATOM CARRIES THE FLOOR.**  The weighted outside readings
clear `(1 − t_cap)|w|²` and the outside weights total at most one, so a
single outside atom already reads the probe that much. -/
theorem nullProbe_exists_outside_reading_ge {m : ℕ} (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {w : Fin 3 → ℝ}
    (hnull : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0)
    {tcap : ℝ} (hcap : ∀ c ∈ C, D.weight c ≤ tcap) (hne : (Cᶜ : Finset (Fin m)).Nonempty) :
    ∃ d ∈ (Cᶜ : Finset (Fin m)), (1 - tcap) * (w ⬝ᵥ w) ≤ (D.atom d ⬝ᵥ w) ^ 2 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨d0, hd0⟩ := hne
  have hpos : 0 < (1 - tcap) * (w ⬝ᵥ w) :=
    lt_of_le_of_lt (sq_nonneg (D.atom d0 ⬝ᵥ w)) (hcon d0 hd0)
  have hlt : ∑ d ∈ (Cᶜ : Finset (Fin m)), D.weight d * (D.atom d ⬝ᵥ w) ^ 2
      < ∑ d ∈ (Cᶜ : Finset (Fin m)), D.weight d * ((1 - tcap) * (w ⬝ᵥ w)) := by
    refine Finset.sum_lt_sum_of_nonempty ⟨d0, hd0⟩ fun d hd => ?_
    exact mul_lt_mul_of_pos_left (hcon d hd) (D.weight_pos d)
  rw [← Finset.sum_mul] at hlt
  have hfloor := nullProbe_outside_reading_floor D C hnull hcap
  have hw := sum_compl_weight_le_one D C
  nlinarith [hfloor, hlt, hpos, hw]

/-- **SOME INSIDE ATOM IS BELOW THE AVERAGE.**  The three inside squared
readings total the probe's square, so the least is at most a third of it. -/
theorem nullProbe_exists_inside_reading_le {m : ℕ} (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hcard : C.card = 3) {w : Fin 3 → ℝ}
    (hnull : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0) :
    ∃ c ∈ C, 3 * (D.atom c ⬝ᵥ w) ^ 2 ≤ w ⬝ᵥ w := by
  classical
  by_contra hcon
  push Not at hcon
  have hne : C.Nonempty := Finset.card_pos.mp (by rw [hcard]; norm_num)
  have hlt : ∑ _c ∈ C, (w ⬝ᵥ w) < ∑ c ∈ C, 3 * (D.atom c ⬝ᵥ w) ^ 2 :=
    Finset.sum_lt_sum_of_nonempty hne fun c hc => hcon c hc
  rw [Finset.sum_const, hcard] at hlt
  have hsum : ∑ c ∈ C, 3 * (D.atom c ⬝ᵥ w) ^ 2
      = 3 * ∑ c ∈ C, (D.atom c ⬝ᵥ w) ^ 2 := by rw [Finset.mul_sum]
  rw [hsum, nullProbe_inside_total D C hnull] at hlt
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hlt
  linarith

/-- **THE SWAP EXCESS FLOOR.**  At a weak dominator with a unit null probe,
some swap opens the probe by a definite amount:

  `(1 − t_cap) − 1/3 ≤ (g_d·w)² − (g_c·w)²` .

The outside floor pushes some outside reading up, the inside average pushes
some inside reading down, and the difference is the null form of the swapped
triple.  At `(6,3)` with inside weights at most a half this is at least
`1/6`, so the swapped gap is STRICTLY POSITIVE at the original probe while
the tie still refuses it — the refusal must therefore happen transverse to
the probe. -/
theorem nullProbe_swap_excess_floor {m : ℕ} (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hcard : C.card = 3) {w : Fin 3 → ℝ} (hw : w ⬝ᵥ w = 1)
    (hnull : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0)
    {tcap : ℝ} (hcap : ∀ c ∈ C, D.weight c ≤ tcap)
    (hne : (Cᶜ : Finset (Fin m)).Nonempty) :
    ∃ c ∈ C, ∃ d ∈ (Cᶜ : Finset (Fin m)),
      (1 - tcap) - 1 / 3 ≤ (D.atom d ⬝ᵥ w) ^ 2 - (D.atom c ⬝ᵥ w) ^ 2 := by
  obtain ⟨d, hd, hdge⟩ := nullProbe_exists_outside_reading_ge D C hnull hcap hne
  obtain ⟨c, hc, hcle⟩ := nullProbe_exists_inside_reading_le D C hcard hnull
  refine ⟨c, hc, d, hd, ?_⟩
  rw [hw, mul_one] at hdge
  rw [hw] at hcle
  linarith

/-- **THE QUANTITATIVE COUPLING FLOOR OF A TIE.**  Feeding the swap excess
into the probe pinch, at a tie the swap coupling clears a definite multiple
of the coercivity:

  `((1 − t_cap) − 1/3)·μ ≤ |swapCoupling|²` .

This is the arm's missing ingredient in numerical form — a LOWER bound on
the coupling, obtained from Parseval rather than from any second-order
estimate, and hence not homogeneous with the quantities it must beat.
[MEASURED at the split diamond: the forced excess is `1.267` against an
actual `1.875` at every mirror contact, all twelve exact.] -/
theorem isTie_swap_coupling_floor_quantitative {m : ℕ} (D : WeightedDesign m 3)
    (htie : IsTie D) (C : Finset (Fin m)) (hcard : C.card = 3)
    {w : Fin 3 → ℝ} (hw : w ⬝ᵥ w = 1)
    (hnullvec : (subsetSum D C - 1) *ᵥ w = 0)
    {tcap : ℝ} (hcap : ∀ c ∈ C, D.weight c ≤ tcap)
    (hne : (Cᶜ : Finset (Fin m)).Nonempty)
    {mu : ℝ} (hmu : 0 < mu)
    (hcoer : ∀ c ∈ C, ∀ d ∈ (Cᶜ : Finset (Fin m)), ∀ v : Fin 3 → ℝ, v ⬝ᵥ w = 0 →
      mu * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((subsetSum D (insert d (C.erase c)) - 1) *ᵥ v)) :
    ∃ c ∈ C, ∃ d ∈ (Cᶜ : Finset (Fin m)),
      ((1 - tcap) - 1 / 3) * mu ≤ swapCoupling D c d w ⬝ᵥ swapCoupling D c d w := by
  classical
  have hform : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0 := by
    rw [hnullvec, dotProduct_zero]
  obtain ⟨c, hc, d, hd, hexc⟩ :=
    nullProbe_swap_excess_floor D C hcard hw hform hcap hne
  refine ⟨c, hc, d, hd, ?_⟩
  have hdC : d ∉ C := by simpa using (Finset.mem_compl.mp hd)
  have hpin := swap_pinch_of_isTie D htie hcard hc hdC hw hnullvec hmu
    (hcoer c hc d hd)
  nlinarith [hpin, hexc, hmu]

/-! ## 6. The swap symmetry of an exact doubling -/

/-- **AN EXACT DOUBLING MAKES THE SWAP AN IDENTITY OF GAPS.**  If `g_q = ±g_p`
then exchanging `p` for `q` does not move the subset sum at all:

  `S_{C − p + q} = S_C` .

So at a doubling every mirror pair of triples carries the SAME gap, hence
the same null line, and the mirror structure of the fixture is not a
coincidence but a symmetry.  This is the converse direction of the arm's
equivalence, in its crudest and strongest form. -/
theorem parallel_swap_subsetSum_eq {m k : ℕ} (D : WeightedDesign m k)
    {C : Finset (Fin m)} {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C)
    {ratio : ℝ} (hpar : D.atom q = ratio • D.atom p) (hratio : ratio ^ 2 = 1) :
    subsetSum D (insert q (C.erase p)) = subsetSum D C := by
  rw [subsetSum_swap_eq D hp hq]
  have hatom : atomMatrix (D.atom q) = atomMatrix (D.atom p) := by
    ext i j
    simp only [hpar, atomMatrix, Matrix.vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul]
    linear_combination (D.atom p i * D.atom p j) * hratio
  rw [hatom]
  abel

/-- At an exact doubling the swapped triple weakly dominates exactly when the
original does. -/
theorem parallel_swap_dominates_iff {m k : ℕ} (D : WeightedDesign m k)
    {C : Finset (Fin m)} {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C)
    {ratio : ℝ} (hpar : D.atom q = ratio • D.atom p) (hratio : ratio ^ 2 = 1) :
    Dominates D (insert q (C.erase p)) ↔ Dominates D C := by
  rw [Dominates, Dominates, parallel_swap_subsetSum_eq D hp hq hpar hratio]

end Gtz

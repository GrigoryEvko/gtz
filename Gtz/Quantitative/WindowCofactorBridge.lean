/-
# The window cofactor bridge: the trace-one equation as a determinant sum,
  and the Cauchy–Binet layer sum as an aggregate of window sums

The `(6,3)` residual — at a tie, every CIRCUIT window `Q` (`|Q| = rank+1`, `S_Q ≻ 1`)
has `tr((S_Q − 1)⁻¹) = 1` — has been attacked from inside the window (the tie's
window-local content is all one-signed) and from the window's own geometry (the
Lorentzian signature reading is realizable with the trace off one).  Both walls end at
the same sentence: *any proof must consume the tie through atoms the window does not
contain*.  Meanwhile a third lane mechanized the general-weight LAYER SUM, a global
identity over all `rank`-subsets.  Nobody had composed them, because the window world
speaks in TRACES OF INVERSES and the layer world speaks in DETERMINANTS.

This file is the composition.  It is a change of vocabulary followed by a counting
argument, and it ends in a dichotomy that says exactly how much the global identity
can buy.

## The bridge

`det_erase_eq_det_mul_pivot_gap` (shipped, `Gtz.Design.CapSlack`) reads one erasure as
a determinant ratio, `det(S_{Q∖d} − 1) = det(S_Q − 1)·(1 − q_d)`.  Summing it over the
window and feeding the insider pivot sum gives, at any window size,

    Σ_{d ∈ Q} det(S_{Q∖d} − 1) = det(S_Q − 1)·(|Q| − rank − tr((S_Q − 1)⁻¹))

(`sum_det_erase_eq_det_mul_windowGap`), and at `|Q| = rank+1` the bracket is exactly
`1 − tr((S_Q − 1)⁻¹)`.  Since the gate makes `det(S_Q − 1) > 0`:

    **tr((S_Q − 1)⁻¹) = 1  ⟺  Σ_{d ∈ Q} det(S_{Q∖d} − 1) = 0**

(`traceInverse_eq_one_iff_sum_det_erase_eq_zero`).  The target is a VANISHING SUM OF
GAP DETERMINANTS — the same species the layer sum aggregates.  This is the exchange
rate the two lanes were missing; everything below is arithmetic on top of it.

## The composition

Each `rank`-subset sits inside exactly `size − rank` windows of size `rank+1`, so the
double count (`Gtz.sum_powersetCard_sum_powersetCard`, already in the tree) gives

    Σ_{|Q| = rank+1} Σ_{d ∈ Q} det(S_{Q∖d} − 1) = (size − rank) · Σ_{|C| = rank} det(S_C − 1)

(`sum_window_erasureTotal_eq_layer_nsmul`).  The right side is the layer sum.  So the
layer sum IS the aggregate of the very numbers the target sets to zero, and at `(6,3)`
it reads `Σ_{|Q|=4} Σ_{d∈Q} det(S_{Q∖d} − 1) = 3·Σ_{|C|=3} det(S_C − 1)`, which at a
uniform weight is `3·(−56) = −168` (`window_erasureTotal_uniform_sixThree`).

## What the composition buys, exactly

At a tie every insider pivot of a gated window is `≥ 1` (`one_le_pivot_of_isTie_window`,
re-derived here from `Gtz.posDef_sub_vecMulVec_iff` because the sibling lane's copy is
not in the tree), so every gated window's erasure total is `≤ 0`.  The aggregate is
therefore ONE LINEAR EQUATION over same-signed unknowns, and that has a sharp
dichotomy.

**The residual's exact price.**  At a tie with every `(rank+1)`-window gated,

    (∀ Q) tr((S_Q − 1)⁻¹) = 1   ⟺   Σ_{|C| = rank} det(S_C − 1) = 0

(`forall_gated_traceInverse_eq_one_iff_layer_eq_zero`) — not merely implied by a
vanishing layer sum, EQUAL to it.  So the residual stripped of its circuit hypothesis is
a single polynomial equation in the unweighted second moment, at `(6,3)` the
hypersurface `det N − 4 e_2(N) + 10 tr N − 20 = 0`, whose `≤` half
`layer_nonpos_of_isTie_of_forall_gated` already proves.

**General position collapses the circuit hypothesis.**  If every `rank`-subset is
independent then every window is a circuit
(`isCircuitWindow_of_isGeneralPosition`), the residual's own statement collapses onto
the unconditional one, and the whole question on that stratum becomes that one equation
(`forall_circuitWindow_traceInverse_eq_one_iff_layer_eq_zero`).  That is a falsification
test and a route at once: a general-position all-gated tie with nonzero layer value
refutes the residual outright
(`exists_circuitWindow_traceInverse_ne_one_of_layer_ne_zero`), and conversely proving
`layer = 0` on that stratum — a statement about `N` alone, with no window in it — closes
the residual there.  The uniform `(6,3)` cell has layer `−56`, so a uniform tie with all
fifteen windows gated cannot be in general position if the residual holds
(`not_isGeneralPosition_of_isTie_uniform_sixThree`).

**Off general position it cannot close.**  One equation with a nonzero right-hand side
does not pin any one of its same-signed unknowns: `budget_does_not_pin_coordinate`
exhibits, for every negative budget and every named coordinate, an alternative
assignment satisfying every constraint the composition supplies with that coordinate
strictly negative.  Both known `(6,3)` tie families have nonzero layer sums — `−56`
(uniform) and `−64` (split tetrahedron) — so the composition is provably silent exactly
where the residual lives.

**Where the deficit sits.**  `forall_traceInverse_eq_one_off_exempt_iff_exempt_carries_deficit`
says, for any exempt class of windows, that the non-exempt ones all have trace one
exactly when the exempt ones carry the entire layer deficit; only the non-exempt windows
need be gated, so the exempt class may absorb non-gated windows too.  Exempting the
non-circuits turns the residual into a scalar bookkeeping claim.  At the split
tetrahedron (verified in exact rationals outside Lean) the fifteen windows split as four
circuits with erasure total `0` and trace exactly `1`, ten gated non-circuits with total
`−16` and trace `19/3`, and one non-gated window with total `−32`; the deficit
`10·(−16) + (−32) = −192 = 3·(−64)` is carried entirely off the circuits, which is the
residual holding and the localization law's content in the same table.

## Scope — read before quoting the reach

The residual is NOT proved here.  Two hypotheses limit what is:

* **"Every `(rank+1)`-window is gated" is restrictive and its realizability at a tie is
  not established.**  The split tetrahedron FAILS it — its window `{2,3,4,5}` carries
  both doubled directions, has a rank-two moment and a `−1` eigenvalue in the gap — so
  `forall_gated_traceInverse_eq_one_iff_layer_eq_zero`,
  `layer_nonpos_of_isTie_of_forall_gated` and the general-position collapse do not speak
  about that design.  `forall_traceInverse_eq_one_off_exempt_iff_exempt_carries_deficit`
  is the one that does, because its exempt class absorbs the non-gated windows.  Whether
  general position forces every window gated at a tie is open and worth one probe: an
  affirmative answer would make the collapse unconditional on gating.

* **General position is strictly stronger than parallel-freeness.**  The campaign's
  hinge says the counterexamples that matter are parallel-free; general position also
  excludes coplanar triples, so the collapse covers a substratum of the hinge, not the
  hinge.

The sharp checkable prediction the collapse leaves behind is: NO general-position
`(6,3)` tie with all fifteen windows gated has `det N − 4 e_2(N) + 10 tr N − 20 ≠ 0`.
Finding one refutes the residual; proving there is none closes it on that stratum.

## The third wall, stated

The obstruction is not that the layer sum is weak; it is that the layer sum is a
CHANGE OF VARIABLES rather than a constraint.  Its proof uses no design hypothesis —
it holds for arbitrary vectors — so it cannot separate a tie from a non-tie, and every
inequality it yields is a nonnegative combination of the window-local inequalities the
first wall already surveyed and found same-signed.  Composing it with the tie produces
exactly one scalar equation against `C(size, rank+1)` nonpositive unknowns, and
`budget_does_not_pin_coordinate` is the proof that such a system pins a coordinate iff
its budget is zero (`all_eq_zero_of_nonpos_of_sum_eq_zero` is the converse half).  The
mechanism differs from both earlier walls: the first says the tie's local consequences
all point one way, the second says the window's geometry is realizable off the locus,
this one says the only global invariant on offer is rank-one against a
fifteen-dimensional cone.

## What is reusable

`window_erasureTotal_budget` is the positive residue: at a tie with every window gated,

    Σ_{|Q| = rank+1} det(S_Q − 1)·(tr((S_Q − 1)⁻¹) − 1) = −(size − rank)·Σ_{|C|=rank} det(S_C − 1)

with every summand NONNEGATIVE.  It is a global budget on the trace excesses — it says
how much total excess the design may spend and, through
`layer_nonpos_of_isTie_of_forall_gated`, forces the layer sum of such a tie to be
nonpositive, a necessary condition on the unweighted moment that no window sees.

`exists_not_dominates_det_mul_card_le_layer_of_isTie` is the count-and-position residue:
a dominating subset of a tie has a singular gap and so contributes nothing to the layer
sum, hence the whole layer value is carried by non-dominators, and pigeonhole turns that
into an explicit DEPTH — some `rank`-subset of a tie with negative layer sum has gap
determinant at most the layer average, and is therefore not a dominator.  Any bound on
the moment becomes a quantitative statement about how badly some subset must fail.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.SchurRankOne
import Gtz.Design.TraceIdentity
import Gtz.Design.CapSlack
import Gtz.Quantitative.MixtureAggregates
import Gtz.Quantitative.ChartHadamard
import Gtz.Certificates.ResidueDissolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The insider pivot sum -/

/-- **The insider pivots total `rank + tr((S_Q − 1)⁻¹)`.**  Every pivot is a trace
against the same inverse, so the sum is the trace against the window's own subset sum,
and `S_Q = (S_Q − 1) + 1` splits it.  No cardinality hypothesis: the identity holds at
any gated window. -/
theorem sum_pivot_insider_eq_rank_add_traceInverse (D : WeightedDesign m k)
    (window : Finset (Fin m)) (hgate : (subsetSum D window - 1).PosDef) :
    ∑ insider ∈ window, pivot D window insider
      = (k : ℝ) + Matrix.trace (subsetSum D window - 1)⁻¹ := by
  have hdet : IsUnit (subsetSum D window - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hgate.det_pos)
  have hcollapse : ∑ insider ∈ window, pivot D window insider
      = Matrix.trace ((subsetSum D window - 1)⁻¹ * subsetSum D window) := by
    rw [subsetSum, Matrix.mul_sum, Matrix.trace_sum]
    rfl
  have hsplit : (subsetSum D window - 1)⁻¹ * subsetSum D window
      = 1 + (subsetSum D window - 1)⁻¹ := by
    have hrewrite : subsetSum D window
        = (subsetSum D window - 1) + 1 := by abel
    calc (subsetSum D window - 1)⁻¹ * subsetSum D window
        = (subsetSum D window - 1)⁻¹ * ((subsetSum D window - 1) + 1) := by
          rw [← hrewrite]
      _ = (subsetSum D window - 1)⁻¹ * (subsetSum D window - 1)
            + (subsetSum D window - 1)⁻¹ * 1 := by rw [Matrix.mul_add]
      _ = 1 + (subsetSum D window - 1)⁻¹ := by
          rw [Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  rw [hcollapse, hsplit, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin]

/-! ## The window cofactor bridge -/

/-- **THE ERASURE TOTAL OF A GATED WINDOW.**  Summing the shipped determinant ratio
`det(S_{Q∖d} − 1) = det(S_Q − 1)·(1 − q_d)` over the window and collapsing the pivots:

    `Σ_{d ∈ Q} det(S_{Q∖d} − 1) = det(S_Q − 1)·(|Q| − rank − tr((S_Q − 1)⁻¹))` .

Stated at any window size; the residual's window size `rank+1` is the corollary. -/
theorem sum_det_erase_eq_det_mul_windowGap (D : WeightedDesign m k)
    (window : Finset (Fin m)) (hgate : (subsetSum D window - 1).PosDef) :
    ∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det
      = (subsetSum D window - 1).det
        * ((window.card : ℝ) - (k : ℝ) - Matrix.trace (subsetSum D window - 1)⁻¹) := by
  have hterm : ∀ dropped ∈ window,
      (subsetSum D (window.erase dropped) - 1).det
        = (subsetSum D window - 1).det * (1 - pivot D window dropped) :=
    fun dropped hdropped => det_erase_eq_det_mul_pivot_gap D window hgate hdropped
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, mul_one,
    sum_pivot_insider_eq_rank_add_traceInverse D window hgate]
  ring

/-- **The erasure total at the residual's window size.**  At `|Q| = rank+1` the bracket
collapses to `1 − tr((S_Q − 1)⁻¹)`: the whole trace-one question is the vanishing of a
sum of four gap determinants. -/
theorem sum_det_erase_eq_det_mul_one_sub_traceInverse (D : WeightedDesign m k)
    (window : Finset (Fin m)) (hgate : (subsetSum D window - 1).PosDef)
    (hcard : window.card = k + 1) :
    ∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det
      = (subsetSum D window - 1).det * (1 - Matrix.trace (subsetSum D window - 1)⁻¹) := by
  rw [sum_det_erase_eq_det_mul_windowGap D window hgate, hcard]
  push_cast
  ring_nf

/-- **THE BRIDGE.**  At a gated window of size `rank+1` the residual's trace equation is
EXACTLY the vanishing of the erasure total.  Left side lives in the window-inverse
world the first two walls exhausted; right side lives in the determinant world the
Cauchy–Binet layer sum aggregates. -/
theorem traceInverse_eq_one_iff_sum_det_erase_eq_zero (D : WeightedDesign m k)
    (window : Finset (Fin m)) (hgate : (subsetSum D window - 1).PosDef)
    (hcard : window.card = k + 1) :
    Matrix.trace (subsetSum D window - 1)⁻¹ = 1
      ↔ ∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det = 0 := by
  rw [sum_det_erase_eq_det_mul_one_sub_traceInverse D window hgate hcard]
  constructor
  · intro htrace
    rw [htrace]
    ring
  · intro hzero
    rcases mul_eq_zero.mp hzero with hdetZero | hbracket
    · exact absurd hdetZero (ne_of_gt hgate.det_pos)
    · linarith

/-! ## The tie's sign law on erasure determinants -/

/-- **A tie forces every insider pivot of a gated `(rank+1)`-window up to one.**  The
erasure `Q ∖ {d}` has `rank` atoms, so the tie denies it a positive definite gap, and
the rank-one Schur criterion turns that denial into `q_d ≥ 1`.

Re-derived here: the sibling independence lane proves the same statement, but that lane
is not in the tree and cannot be imported. -/
theorem one_le_pivot_of_isTie_window (D : WeightedDesign m k) (htie : IsTie D)
    (window : Finset (Fin m)) (hgate : (subsetSum D window - 1).PosDef)
    (hcard : window.card = k + 1) {dropped : Fin m} (hdropped : dropped ∈ window) :
    1 ≤ pivot D window dropped := by
  have heraseCard : (window.erase dropped).card = k := by
    rw [Finset.card_erase_of_mem hdropped, hcard]
    omega
  have hnotPosDef : ¬ (subsetSum D (window.erase dropped) - 1).PosDef :=
    htie.2 (window.erase dropped) heraseCard
  have hrewrite : subsetSum D (window.erase dropped) - 1
      = (subsetSum D window - 1) - Matrix.vecMulVec (D.atom dropped) (D.atom dropped) := by
    have hsum := Finset.sum_erase_add window (fun c => atomMatrix (D.atom c)) hdropped
    rw [subsetSum, subsetSum, ← hsum, atomMatrix]
    abel
  rw [hrewrite, posDef_sub_vecMulVec_iff _ hgate, ← pivot_eq_dot] at hnotPosDef
  exact le_of_not_gt hnotPosDef

/-- **Every erasure determinant of a gated `(rank+1)`-window is nonpositive at a tie.**
The determinant ratio carries the pivot bound across. -/
theorem det_erase_nonpos_of_isTie (D : WeightedDesign m k) (htie : IsTie D)
    (window : Finset (Fin m)) (hgate : (subsetSum D window - 1).PosDef)
    (hcard : window.card = k + 1) {dropped : Fin m} (hdropped : dropped ∈ window) :
    (subsetSum D (window.erase dropped) - 1).det ≤ 0 := by
  rw [det_erase_eq_det_mul_pivot_gap D window hgate hdropped]
  have hpivot := one_le_pivot_of_isTie_window D htie window hgate hcard hdropped
  have hdetPos := hgate.det_pos
  nlinarith

/-- **The erasure total of a gated `(rank+1)`-window is nonpositive at a tie** — the
same one-signed conclusion the window-local walls reach, now in determinant vocabulary
so that it can be aggregated. -/
theorem sum_det_erase_nonpos_of_isTie (D : WeightedDesign m k) (htie : IsTie D)
    (window : Finset (Fin m)) (hgate : (subsetSum D window - 1).PosDef)
    (hcard : window.card = k + 1) :
    ∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det ≤ 0 :=
  Finset.sum_nonpos fun _dropped hdropped =>
    det_erase_nonpos_of_isTie D htie window hgate hcard hdropped

/-- **A tie's gated `(rank+1)`-window has `tr((S_Q − 1)⁻¹) ≥ 1`** — the residual's
inequality half, recovered through the bridge rather than through Parseval. -/
theorem one_le_traceInverse_of_isTie (D : WeightedDesign m k) (htie : IsTie D)
    (window : Finset (Fin m)) (hgate : (subsetSum D window - 1).PosDef)
    (hcard : window.card = k + 1) :
    1 ≤ Matrix.trace (subsetSum D window - 1)⁻¹ := by
  have hnonpos := sum_det_erase_nonpos_of_isTie D htie window hgate hcard
  rw [sum_det_erase_eq_det_mul_one_sub_traceInverse D window hgate hcard] at hnonpos
  have hdetPos := hgate.det_pos
  nlinarith

/-! ## The double count: windows against the layer -/

/-- **The `rank`-subsets of a `(rank+1)`-set are its erasures.**  Dropping one element
is a bijection from the set onto its subsets of one lower size. -/
theorem sum_powersetCard_pred_eq_sum_erase {element : Type*} [DecidableEq element]
    {target : Type*} [AddCommMonoid target]
    (base : Finset element) (innerCard : ℕ) (hcard : base.card = innerCard + 1)
    (valueOf : Finset element → target) :
    ∑ inner ∈ base.powersetCard innerCard, valueOf inner
      = ∑ dropped ∈ base, valueOf (base.erase dropped) := by
  refine (Finset.sum_nbij (fun dropped => base.erase dropped) ?_ ?_ ?_ ?_).symm
  · intro dropped hdropped
    refine Finset.mem_powersetCard.mpr ⟨Finset.erase_subset _ _, ?_⟩
    rw [Finset.card_erase_of_mem hdropped, hcard]
    omega
  · intro firstDropped hfirst secondDropped hsecond herase
    simp only [Finset.mem_coe] at hfirst hsecond
    have heraseEq : base.erase firstDropped = base.erase secondDropped := herase
    by_contra hne
    have hmem : firstDropped ∈ base.erase secondDropped :=
      Finset.mem_erase.mpr ⟨hne, hfirst⟩
    rw [← heraseEq] at hmem
    exact (Finset.notMem_erase firstDropped base) hmem
  · intro inner hinner
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hinner
    obtain ⟨hsubset, hinnerCard⟩ := hinner
    have hdiffCard : (base \ inner).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsubset, hinnerCard, hcard]
      omega
    obtain ⟨dropped, hdiff⟩ := Finset.card_eq_one.mp hdiffCard
    have hdroppedMem : dropped ∈ base := by
      have : dropped ∈ base \ inner := by rw [hdiff]; exact Finset.mem_singleton_self _
      exact (Finset.mem_sdiff.mp this).1
    refine ⟨dropped, Finset.mem_coe.mpr hdroppedMem, ?_⟩
    have hforward : base.erase dropped ⊆ inner := by
      intro x hx
      obtain ⟨hxne, hxbase⟩ := Finset.mem_erase.mp hx
      by_contra hxnot
      have hxdiff : x ∈ base \ inner := Finset.mem_sdiff.mpr ⟨hxbase, hxnot⟩
      rw [hdiff, Finset.mem_singleton] at hxdiff
      exact hxne hxdiff
    have hbackward : inner ⊆ base.erase dropped := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, hsubset hx⟩
      intro hxeq
      have hdroppedNot : dropped ∉ inner := by
        have : dropped ∈ base \ inner := by rw [hdiff]; exact Finset.mem_singleton_self _
        exact (Finset.mem_sdiff.mp this).2
      exact hdroppedNot (hxeq ▸ hx)
    exact Finset.Subset.antisymm hforward hbackward
  · intro _ _
    rfl

/-- **THE COMPOSITION.**  Summing the erasure totals over every `(rank+1)`-window
visits each `rank`-subset exactly `size − rank` times, so the window aggregate IS the
layer sum, scaled:

    `Σ_{|Q| = rank+1} Σ_{d ∈ Q} det(S_{Q∖d} − 1) = (size − rank) · Σ_{|C| = rank} det(S_C − 1)` .

No gate, no tie, no cardinality side condition — pure double counting on top of the
tree's `sum_powersetCard_sum_powersetCard`. -/
theorem sum_window_erasureTotal_eq_layer_nsmul (D : WeightedDesign m k) :
    ∑ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
        ∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det
      = ((m - k : ℕ) : ℝ)
        * ∑ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
            (subsetSum D chosen - 1).det := by
  have hinner : ∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      ∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det
        = ∑ inner ∈ window.powersetCard k, (subsetSum D inner - 1).det := by
    intro window hwindow
    exact (sum_powersetCard_pred_eq_sum_erase window k
      (Finset.mem_powersetCard.mp hwindow).2
      (fun chosen => (subsetSum D chosen - 1).det)).symm
  rw [Finset.sum_congr rfl hinner,
    sum_powersetCard_sum_powersetCard (k + 1) k (Nat.le_succ k)
      (fun chosen => (subsetSum D chosen - 1).det)]
  rw [Fintype.card_fin, Nat.add_sub_cancel_left, Nat.choose_one_right, nsmul_eq_mul]

/-! ## The `(6,3)` reading -/

/-- **The `(6,3)` window aggregate.**  Fifteen windows of four atoms, each `rank`-subset
in three of them. -/
theorem window_erasureTotal_sixThree (D : WeightedDesign 6 3) :
    ∑ window ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
        ∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det
      = 3 * ∑ chosen ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
            (subsetSum D chosen - 1).det := by
  have haggregate := sum_window_erasureTotal_eq_layer_nsmul D
  norm_num at haggregate
  exact haggregate

/-- **The uniform `(6,3)` window aggregate is `−168`.**  The shipped uniform layer sum
is `−56`, and every triple sits in three windows.  A design-blind constant: the
aggregate cannot see the design, which is exactly why it cannot decide the residual. -/
theorem window_erasureTotal_uniform_sixThree (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, D.weight atomIndex = ((6 : ℝ))⁻¹) :
    ∑ window ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
        ∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det = -168 := by
  rw [window_erasureTotal_sixThree D, sum_det_subsetSum_sub_one_sixThree D huniform]
  norm_num

/-! ## The budget law and its necessary condition -/

/-- **THE TRACE-EXCESS BUDGET.**  At a tie whose every `(rank+1)`-window is gated, the
total trace excess weighted by the window gap determinants is fixed by the layer sum:

    `Σ_{|Q| = rank+1} det(S_Q − 1)·(tr((S_Q − 1)⁻¹) − 1) = −(size − rank)·Σ_{|C|=rank} det(S_C − 1)` ,

and by `one_le_traceInverse_of_isTie` every summand on the left is NONNEGATIVE.  The
design may spend exactly this much excess and no more; the residual asks that circuit
windows spend none of it. -/
theorem window_erasureTotal_budget (D : WeightedDesign m k)
    (hgateAll : ∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      (subsetSum D window - 1).PosDef) :
    ∑ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
        (subsetSum D window - 1).det
          * (Matrix.trace (subsetSum D window - 1)⁻¹ - 1)
      = -(((m - k : ℕ) : ℝ)
        * ∑ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
            (subsetSum D chosen - 1).det) := by
  have hstep : ∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      (subsetSum D window - 1).det
          * (Matrix.trace (subsetSum D window - 1)⁻¹ - 1)
        = -(∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det) := by
    intro window hwindow
    rw [sum_det_erase_eq_det_mul_one_sub_traceInverse D window (hgateAll window hwindow)
      (Finset.mem_powersetCard.mp hwindow).2]
    ring
  calc ∑ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
        (subsetSum D window - 1).det
          * (Matrix.trace (subsetSum D window - 1)⁻¹ - 1)
      = ∑ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
          -(∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det) :=
        Finset.sum_congr rfl hstep
    _ = -(∑ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
          ∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det) :=
        Finset.sum_neg_distrib _
    _ = -(((m - k : ℕ) : ℝ)
          * ∑ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
              (subsetSum D chosen - 1).det) := by
        rw [sum_window_erasureTotal_eq_layer_nsmul D]

/-- **A tie with every window gated has a nonpositive layer sum.**  Each window's
erasure total is nonpositive and they aggregate to `(size − rank)` copies of the layer
sum.  This is a necessary condition on the unweighted second moment that no single
window can see — the composition's first genuinely global consequence. -/
theorem layer_nonpos_of_isTie_of_forall_gated (D : WeightedDesign m k) (htie : IsTie D)
    (hkm : k < m)
    (hgateAll : ∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      (subsetSum D window - 1).PosDef) :
    ∑ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        (subsetSum D chosen - 1).det ≤ 0 := by
  have haggregate := sum_window_erasureTotal_eq_layer_nsmul D
  have hnonpos : ∑ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      ∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det ≤ 0 :=
    Finset.sum_nonpos fun window hwindow =>
      sum_det_erase_nonpos_of_isTie D htie window (hgateAll window hwindow)
        (Finset.mem_powersetCard.mp hwindow).2
  rw [haggregate] at hnonpos
  have hpos : (0 : ℝ) < ((m - k : ℕ) : ℝ) := by
    have : 0 < m - k := Nat.sub_pos_of_lt hkm
    exact_mod_cast this
  nlinarith

/-! ## The dichotomy: when one equation pins the window, and when it cannot -/

/-- **A nonpositive family summing to zero is identically zero.**  The saturation half
of the dichotomy, stated once so both readings below use the same step. -/
theorem all_eq_zero_of_nonpos_of_sum_eq_zero {element : Type*}
    (family : Finset element) (valueOf : element → ℝ)
    (hnonpos : ∀ item ∈ family, valueOf item ≤ 0)
    (hsum : ∑ item ∈ family, valueOf item = 0) :
    ∀ item ∈ family, valueOf item = 0 := by
  intro item hitem
  have hnegSum : ∑ other ∈ family, (-valueOf other) = 0 := by
    rw [Finset.sum_neg_distrib, hsum, neg_zero]
  have hnegNonneg : ∀ other ∈ family, 0 ≤ -valueOf other :=
    fun other hother => neg_nonneg.mpr (hnonpos other hother)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnegNonneg).mp hnegSum item hitem
  linarith [hzero]

/-- **SATURATION CLOSES THE RESIDUAL.**  At a tie with every `(rank+1)`-window gated and
a VANISHING layer sum, every window's erasure total is zero, hence every window has
`tr((S_Q − 1)⁻¹) = 1` — the residual, with no circuit hypothesis at all.  The
determinant vocabulary is what makes this visible: the aggregate is a sum of
nonpositive numbers, and a nonpositive family with zero total is zero. -/
theorem forall_gated_traceInverse_eq_one_of_layer_eq_zero (D : WeightedDesign m k)
    (htie : IsTie D)
    (hgateAll : ∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      (subsetSum D window - 1).PosDef)
    (hlayer : ∑ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        (subsetSum D chosen - 1).det = 0) :
    ∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      Matrix.trace (subsetSum D window - 1)⁻¹ = 1 := by
  have haggregate := sum_window_erasureTotal_eq_layer_nsmul D
  rw [hlayer, mul_zero] at haggregate
  have hzero := all_eq_zero_of_nonpos_of_sum_eq_zero
    ((Finset.univ : Finset (Fin m)).powersetCard (k + 1))
    (fun window => ∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det)
    (fun window hwindow => sum_det_erase_nonpos_of_isTie D htie window
      (hgateAll window hwindow) (Finset.mem_powersetCard.mp hwindow).2)
    haggregate
  intro window hwindow
  exact (traceInverse_eq_one_iff_sum_det_erase_eq_zero D window (hgateAll window hwindow)
    (Finset.mem_powersetCard.mp hwindow).2).mpr (hzero window hwindow)

/-- **The full regularity on the vanishing-layer locus**: every erasure of every gated
`(rank+1)`-window weakly dominates.  Read against the shipped no-go — a tie with a
NONZERO layer value cannot have all `rank`-subsets dominating — this is the exact
complement: the layer value decides the whole question when it is zero and says nothing
about individual windows when it is not. -/
theorem forall_erase_dominates_of_layer_eq_zero (D : WeightedDesign m k) (htie : IsTie D)
    (hgateAll : ∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      (subsetSum D window - 1).PosDef)
    (hlayer : ∑ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        (subsetSum D chosen - 1).det = 0) :
    ∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      ∀ dropped ∈ window, Dominates D (window.erase dropped) := by
  intro window hwindow dropped hdropped
  have hgate := hgateAll window hwindow
  have htrace := forall_gated_traceInverse_eq_one_of_layer_eq_zero D htie hgateAll hlayer
    window hwindow
  have hsumZero := (traceInverse_eq_one_iff_sum_det_erase_eq_zero D window hgate
    (Finset.mem_powersetCard.mp hwindow).2).mp htrace
  have hzero := all_eq_zero_of_nonpos_of_sum_eq_zero window
    (fun dropCandidate => (subsetSum D (window.erase dropCandidate) - 1).det)
    (fun dropCandidate hcandidate => det_erase_nonpos_of_isTie D htie window hgate
      (Finset.mem_powersetCard.mp hwindow).2 hcandidate)
    hsumZero
  exact (erase_dominates_iff_det_nonneg D window hgate hdropped).mpr
    (le_of_eq (hzero dropped hdropped).symm)

/-- **THE RESIDUAL'S EXACT PRICE, unconditional on circuits.**  At a tie with every
`(rank+1)`-window gated, trace one AT EVERY WINDOW is EQUIVALENT to the vanishing of the
layer sum.  One direction is saturation; the other is that trace one everywhere makes
every erasure total zero, and the aggregate of those is `(size − rank)` copies of the
layer value.

So the unconditional form of the residual is not merely implied by `layer = 0` — it IS
`layer = 0`, a single polynomial equation in the unweighted second moment.  The circuit
hypothesis is exactly what buys the gap between this equation and the true residual. -/
theorem forall_gated_traceInverse_eq_one_iff_layer_eq_zero (D : WeightedDesign m k)
    (htie : IsTie D) (hkm : k < m)
    (hgateAll : ∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      (subsetSum D window - 1).PosDef) :
    (∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
        Matrix.trace (subsetSum D window - 1)⁻¹ = 1)
      ↔ ∑ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (subsetSum D chosen - 1).det = 0 := by
  have hpos : (0 : ℝ) < ((m - k : ℕ) : ℝ) := by
    have hsub : 0 < m - k := Nat.sub_pos_of_lt hkm
    exact_mod_cast hsub
  constructor
  · intro hall
    have hzeroTotal : ∑ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
        ∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det = 0 := by
      refine Finset.sum_eq_zero fun window hwindow => ?_
      exact (traceInverse_eq_one_iff_sum_det_erase_eq_zero D window (hgateAll window hwindow)
        (Finset.mem_powersetCard.mp hwindow).2).mp (hall window hwindow)
    rw [sum_window_erasureTotal_eq_layer_nsmul D] at hzeroTotal
    rcases mul_eq_zero.mp hzeroTotal with hscale | hlayer
    · exact absurd hscale (ne_of_gt hpos)
    · exact hlayer
  · exact forall_gated_traceInverse_eq_one_of_layer_eq_zero D htie hgateAll

/-! ## General position: the residual becomes one polynomial equation -/

/-- **A window is a circuit** when every erasure of it is an independent family — the
operational form the Lorentz lane uses, a determinant sign rather than a rank. -/
def IsCircuitWindow (D : WeightedDesign m k) (window : Finset (Fin m)) : Prop :=
  ∀ dropped ∈ window, 0 < (subsetSum D (window.erase dropped)).det

/-- **A design is in general position** when every `rank`-subset is independent.  At
`(6,3)` this excludes parallel pairs and coplanar triples — the split tetrahedron fails
it, and the campaign's hinge says the counterexamples that matter do not. -/
def IsGeneralPosition (D : WeightedDesign m k) : Prop :=
  ∀ chosen : Finset (Fin m), chosen.card = k → 0 < (subsetSum D chosen).det

/-- In general position every `(rank+1)`-window is a circuit: its erasures are
`rank`-subsets, and general position makes those independent. -/
theorem isCircuitWindow_of_isGeneralPosition (D : WeightedDesign m k)
    (hgeneral : IsGeneralPosition D) (window : Finset (Fin m)) (hcard : window.card = k + 1) :
    IsCircuitWindow D window := by
  intro dropped hdropped
  refine hgeneral (window.erase dropped) ?_
  rw [Finset.card_erase_of_mem hdropped, hcard]
  omega

/-- **THE RESIDUAL AT A GENERAL-POSITION TIE IS ONE POLYNOMIAL EQUATION.**  When every
`rank`-subset is independent, every window is a circuit, so the residual's circuit
hypothesis buys nothing and the statement collapses onto its unconditional form:

    trace one at every circuit window  ⟺  `Σ_{|C| = rank} det(S_C − 1) = 0` .

At `(6,3)` the right side is `det N − 4 e_2(N) + 10 tr N − 20 = 0`, a hypersurface in
the unweighted second moment.  This is the tractable reformulation: on the
general-position stratum the residual is not a family of window inequalities but a
single equation in three invariants of one `3 × 3` matrix, and
`layer_nonpos_of_isTie_of_forall_gated` already proves the `≤` half of it. -/
theorem forall_circuitWindow_traceInverse_eq_one_iff_layer_eq_zero (D : WeightedDesign m k)
    (htie : IsTie D) (hkm : k < m) (hgeneral : IsGeneralPosition D)
    (hgateAll : ∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      (subsetSum D window - 1).PosDef) :
    (∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
        IsCircuitWindow D window → Matrix.trace (subsetSum D window - 1)⁻¹ = 1)
      ↔ ∑ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (subsetSum D chosen - 1).det = 0 := by
  rw [← forall_gated_traceInverse_eq_one_iff_layer_eq_zero D htie hkm hgateAll]
  constructor
  · intro hall window hwindow
    exact hall window hwindow (isCircuitWindow_of_isGeneralPosition D hgeneral window
      (Finset.mem_powersetCard.mp hwindow).2)
  · intro hall window hwindow _
    exact hall window hwindow

/-- **THE FALSIFICATION TEST.**  A general-position tie with every window gated and a
NONZERO layer sum would put some circuit window off trace one, refuting the residual.
Since the residual is measured true, the contrapositive is a sharp prediction the
campaign can check numerically and a lane can try to prove directly: *no general-position
`(6,3)` tie with all fifteen windows gated has `det N − 4 e_2(N) + 10 tr N − 20 ≠ 0`.*
Proving that statement about the moment alone would close the residual on the whole
general-position stratum through
`forall_circuitWindow_traceInverse_eq_one_iff_layer_eq_zero`. -/
theorem exists_circuitWindow_traceInverse_ne_one_of_layer_ne_zero (D : WeightedDesign m k)
    (htie : IsTie D) (hkm : k < m) (hgeneral : IsGeneralPosition D)
    (hgateAll : ∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      (subsetSum D window - 1).PosDef)
    (hlayer : ∑ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        (subsetSum D chosen - 1).det ≠ 0) :
    ∃ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      IsCircuitWindow D window ∧ Matrix.trace (subsetSum D window - 1)⁻¹ ≠ 1 := by
  by_contra hnone
  push Not at hnone
  refine hlayer ((forall_circuitWindow_traceInverse_eq_one_iff_layer_eq_zero D htie hkm
    hgeneral hgateAll).mp ?_)
  intro window hwindow hcircuit
  exact hnone window hwindow hcircuit

/-- **The uniform `(6,3)` cell is off the vanishing-layer locus.**  Its layer sum is the
shipped design-blind `−56`, so `forall_gated_traceInverse_eq_one_iff_layer_eq_zero` says
a uniform tie with all fifteen windows gated has SOME window off trace one — and by
`exists_circuitWindow_traceInverse_ne_one_of_layer_ne_zero`, if it were also in general
position it would refute the residual outright.  Read the other way: a uniform
`(6,3)` tie with every window gated CANNOT be in general position.  The composition is
silent about which non-circuit window carries the deficit, which is precisely the
residual. -/
theorem not_isGeneralPosition_of_isTie_uniform_sixThree (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, D.weight atomIndex = ((6 : ℝ))⁻¹)
    (htie : IsTie D)
    (hgateAll : ∀ window ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
      (subsetSum D window - 1).PosDef)
    (hresidual : ∀ window ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
      IsCircuitWindow D window → Matrix.trace (subsetSum D window - 1)⁻¹ = 1) :
    ¬ IsGeneralPosition D := by
  intro hgeneral
  have hlayerZero := (forall_circuitWindow_traceInverse_eq_one_iff_layer_eq_zero D htie
    (by norm_num) hgeneral hgateAll).mp hresidual
  rw [sum_det_subsetSum_sub_one_sixThree D huniform] at hlayerZero
  norm_num at hlayerZero

/-! ## Deficit localization: where the residual actually lives -/

/-- The erasure total of a window — the sum of the gap determinants of its `rank`-sized
subsets.  By the bridge it vanishes exactly when the window's trace is one. -/
noncomputable def erasureTotal (D : WeightedDesign m k) (window : Finset (Fin m)) : ℝ :=
  ∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det

/-- **DEFICIT LOCALIZATION — the residual as an aggregate statement.**  Fix any class of
windows to exempt.  At a tie with every `(rank+1)`-window gated, EVERY NON-EXEMPT WINDOW
HAS TRACE ONE if and only if THE EXEMPT WINDOWS CARRY THE WHOLE LAYER DEFICIT.

Taking the exempt class to be the non-circuit windows turns the residual into a single
scalar bookkeeping claim: at a tie the entire deficit `(size − rank)·Σ_{|C|=rank}
det(S_C − 1)` is carried by the windows that are not circuits.  At the split
tetrahedron this is visibly what happens — the four transversal windows have `S_Q = 4·1`
and erasure total zero while the eleven windows containing a doubled direction carry all
of `3·(−64)`.  The forward direction is the bridge applied window by window; the reverse
is `all_eq_zero_of_nonpos_of_sum_eq_zero` on the non-exempt block, whose terms the tie
already signs.

Only the NON-EXEMPT windows need be gated, so the exempt class may absorb the non-gated
windows as well: at the split tetrahedron, exempting everything that is not a circuit
covers its one non-gated window `{2,3,4,5}` and the law reads `0 = ` the four circuit
totals against `10·(−16) + (−32) = −192 = 3·(−64)`, which is what that design does. -/
theorem forall_traceInverse_eq_one_off_exempt_iff_exempt_carries_deficit
    (D : WeightedDesign m k) (htie : IsTie D)
    (isExempt : Finset (Fin m) → Prop) [DecidablePred isExempt]
    (hgateOffExempt : ∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      ¬ isExempt window → (subsetSum D window - 1).PosDef) :
    (∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1), ¬ isExempt window →
        Matrix.trace (subsetSum D window - 1)⁻¹ = 1)
      ↔ ∑ window ∈ ((Finset.univ : Finset (Fin m)).powersetCard (k + 1)).filter isExempt,
            erasureTotal D window
          = ((m - k : ℕ) : ℝ)
            * ∑ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
                (subsetSum D chosen - 1).det := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset (Fin m)).powersetCard (k + 1)) isExempt (erasureTotal D)
  have htotal : ∑ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      erasureTotal D window
      = ((m - k : ℕ) : ℝ)
        * ∑ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
            (subsetSum D chosen - 1).det :=
    sum_window_erasureTotal_eq_layer_nsmul D
  have hnonpos : ∀ window ∈ ((Finset.univ : Finset (Fin m)).powersetCard (k + 1)).filter
      (fun candidate => ¬ isExempt candidate), erasureTotal D window ≤ 0 := by
    intro window hwindow
    obtain ⟨hmem, hnot⟩ := Finset.mem_filter.mp hwindow
    exact sum_det_erase_nonpos_of_isTie D htie window
      (hgateOffExempt window hmem hnot) (Finset.mem_powersetCard.mp hmem).2
  constructor
  · intro hall
    have hcomplement : ∑ window ∈ ((Finset.univ : Finset (Fin m)).powersetCard (k + 1)).filter
        (fun candidate => ¬ isExempt candidate), erasureTotal D window = 0 := by
      refine Finset.sum_eq_zero fun window hwindow => ?_
      obtain ⟨hmem, hnot⟩ := Finset.mem_filter.mp hwindow
      exact (traceInverse_eq_one_iff_sum_det_erase_eq_zero D window
        (hgateOffExempt window hmem hnot)
        (Finset.mem_powersetCard.mp hmem).2).mp (hall window hmem hnot)
    rw [hcomplement, add_zero, htotal] at hsplit
    exact hsplit
  · intro hexempt window hwindow hnot
    rw [hexempt, htotal] at hsplit
    have hcomplement : ∑ candidate ∈
        ((Finset.univ : Finset (Fin m)).powersetCard (k + 1)).filter
          (fun candidate => ¬ isExempt candidate), erasureTotal D candidate = 0 := by
      linarith
    have hzero := all_eq_zero_of_nonpos_of_sum_eq_zero _ (erasureTotal D) hnonpos hcomplement
      window (Finset.mem_filter.mpr ⟨hwindow, hnot⟩)
    exact (traceInverse_eq_one_iff_sum_det_erase_eq_zero D window
      (hgateOffExempt window hwindow hnot)
      (Finset.mem_powersetCard.mp hwindow).2).mpr hzero

/-- **A strictly negative layer sum puts SOME window off trace one.**  The aggregate has
to be spent somewhere, and only windows can spend it.  This is the position half of the
budget: the residual asks that the spending avoid the circuits, and the aggregate
guarantees only that it happens. -/
theorem exists_window_traceInverse_gt_one_of_layer_neg (D : WeightedDesign m k)
    (htie : IsTie D) (hkm : k < m)
    (hgateAll : ∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      (subsetSum D window - 1).PosDef)
    (hlayerNeg : ∑ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        (subsetSum D chosen - 1).det < 0) :
    ∃ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      1 < Matrix.trace (subsetSum D window - 1)⁻¹ := by
  by_contra hnone
  push Not at hnone
  have hallOne : ∀ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      Matrix.trace (subsetSum D window - 1)⁻¹ = 1 := by
    intro window hwindow
    exact le_antisymm (hnone window hwindow)
      (one_le_traceInverse_of_isTie D htie window (hgateAll window hwindow)
        (Finset.mem_powersetCard.mp hwindow).2)
  have hzeroTotal : ∑ window ∈ (Finset.univ : Finset (Fin m)).powersetCard (k + 1),
      ∑ dropped ∈ window, (subsetSum D (window.erase dropped) - 1).det = 0 := by
    refine Finset.sum_eq_zero fun window hwindow => ?_
    exact (traceInverse_eq_one_iff_sum_det_erase_eq_zero D window (hgateAll window hwindow)
      (Finset.mem_powersetCard.mp hwindow).2).mp (hallOne window hwindow)
  rw [sum_window_erasureTotal_eq_layer_nsmul D] at hzeroTotal
  have hpos : (0 : ℝ) < ((m - k : ℕ) : ℝ) := by
    have hsub : 0 < m - k := Nat.sub_pos_of_lt hkm
    exact_mod_cast hsub
  nlinarith

/-! ## The depth bound: how deep the non-domination must go -/

/-- **Some `rank`-subset's gap determinant is at most the layer average.**  Pure
pigeonhole against the layer sum, no tie and no gate: `C(size, rank)` numbers totalling
the layer value cannot all exceed their average. -/
theorem exists_subset_det_mul_card_le_layer (D : WeightedDesign m k) (hkm : k ≤ m) :
    ∃ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      (subsetSum D chosen - 1).det * ((m.choose k : ℕ) : ℝ)
        ≤ ∑ other ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
            (subsetSum D other - 1).det := by
  have hcard : ((Finset.univ : Finset (Fin m)).powersetCard k).card = m.choose k := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hnonempty : ((Finset.univ : Finset (Fin m)).powersetCard k).Nonempty := by
    refine Finset.powersetCard_nonempty.mpr ?_
    rw [Finset.card_univ, Fintype.card_fin]
    exact hkm
  set layerTotal := ∑ other ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
    (subsetSum D other - 1).det with hlayerDef
  have hconst : ∑ _chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k, layerTotal
      = layerTotal * ((m.choose k : ℕ) : ℝ) := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    ring
  have hscaled : ∑ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      (subsetSum D chosen - 1).det * ((m.choose k : ℕ) : ℝ)
      = layerTotal * ((m.choose k : ℕ) : ℝ) := by
    rw [← Finset.sum_mul]
  have hcompare : ∑ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      (subsetSum D chosen - 1).det * ((m.choose k : ℕ) : ℝ)
      ≤ ∑ _chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k, layerTotal := by
    rw [hscaled, hconst]
  exact Finset.exists_le_of_sum_le hnonempty hcompare

/-- **A tie with a negative layer sum contains a DEEPLY non-dominating `rank`-subset.**
Every dominating subset of a tie has a singular gap, hence contributes nothing to the
layer sum; so the whole layer value is carried by non-dominators, and the pigeonhole
converts that into an explicit depth: some `rank`-subset has gap determinant at most the
layer average, and is therefore not a dominator.

This is the count-and-position residue of the composition, and it is reusable outside
this lane: it turns any bound on the unweighted moment into a quantitative statement
about how badly some subset of a tie must fail. -/
theorem exists_not_dominates_det_mul_card_le_layer_of_isTie (D : WeightedDesign m k)
    (htie : IsTie D) (hkm : k ≤ m)
    (hlayerNeg : ∑ other ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        (subsetSum D other - 1).det < 0) :
    ∃ chosen ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      ¬ Dominates D chosen
        ∧ (subsetSum D chosen - 1).det * ((m.choose k : ℕ) : ℝ)
          ≤ ∑ other ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
              (subsetSum D other - 1).det := by
  obtain ⟨chosen, hchosen, hdepth⟩ := exists_subset_det_mul_card_le_layer D hkm
  refine ⟨chosen, hchosen, ?_, hdepth⟩
  intro hdominates
  have hdetZero : (subsetSum D chosen - 1).det = 0 := by
    by_contra hne
    exact htie.2 chosen (Finset.mem_powersetCard.mp hchosen).2
      (hdominates.posDef_iff_det_ne_zero.mpr hne)
  rw [hdetZero, zero_mul] at hdepth
  linarith

/-- **THE THIRD WALL.**  Away from the vanishing-layer locus the composition is silent.
Everything the layer sum contributes, after the bridge, is ONE linear equation with a
fixed budget over coordinates the tie knows only to be nonpositive; for any negative
budget and any named coordinate there is an assignment satisfying every one of those
constraints with that coordinate strictly negative.  So no argument whose only global
input is the layer sum can force a chosen window's erasure total — and hence its trace
— to be the special value.

The mechanism is distinct from both earlier walls.  The independence lane's wall says a
tie's window-local consequences all carry the same sign; the Lorentz lane's wall
exhibits a genuine design realizing the window-local content with the trace off one.
This one says the sole global invariant available is rank one against a cone of
dimension `C(size, rank+1)`, and rank one pins a coordinate only when its budget is
zero — which `all_eq_zero_of_nonpos_of_sum_eq_zero` supplies and
`forall_gated_traceInverse_eq_one_of_layer_eq_zero` cashes.  The two known `(6,3)` tie
families have layer sums `−56` and `−64`. -/
theorem budget_does_not_pin_coordinate {element : Type*} [DecidableEq element]
    (family : Finset element) (targetItem otherItem : element)
    (htarget : targetItem ∈ family) (hother : otherItem ∈ family)
    (hdistinct : otherItem ≠ targetItem) (budget : ℝ) (hbudget : budget < 0) :
    ∃ candidate : element → ℝ,
      (∀ item ∈ family, candidate item ≤ 0)
      ∧ (∑ item ∈ family, candidate item = budget)
      ∧ candidate targetItem < 0 := by
  refine ⟨fun item => (if item = targetItem then budget / 2 else 0)
    + (if item = otherItem then budget / 2 else 0), ?_, ?_, ?_⟩
  · intro item _
    have hhalf : budget / 2 ≤ 0 := by linarith
    have hfirst : (if item = targetItem then budget / 2 else 0) ≤ 0 := by
      split_ifs
      · exact hhalf
      · exact le_refl 0
    have hsecond : (if item = otherItem then budget / 2 else 0) ≤ 0 := by
      split_ifs
      · exact hhalf
      · exact le_refl 0
    exact add_nonpos hfirst hsecond
  · have hfirst : ∑ item ∈ family, (if item = targetItem then budget / 2 else 0)
        = budget / 2 := by
      rw [Finset.sum_ite_eq' family targetItem (fun _ => budget / 2), if_pos htarget]
    have hsecond : ∑ item ∈ family, (if item = otherItem then budget / 2 else 0)
        = budget / 2 := by
      rw [Finset.sum_ite_eq' family otherItem (fun _ => budget / 2), if_pos hother]
    rw [Finset.sum_add_distrib, hfirst, hsecond]
    ring
  · show (if targetItem = targetItem then budget / 2 else 0)
        + (if targetItem = otherItem then budget / 2 else 0) < 0
    rw [if_pos rfl, if_neg (fun heq => hdistinct heq.symm)]
    linarith

/-- **The `(6,3)` instance of the third wall.**  Fifteen windows, one budget; naming any
window as the target and any other as a partner produces an assignment the composition
cannot exclude.  The witness is exhibited at the split tetrahedron's own budget
`3·(−64) = −192`, and at the uniform budget `3·(−56) = −168` by the same call. -/
theorem budget_does_not_pin_window_sixThree (budget : ℝ) (hbudget : budget < 0) :
    ∃ candidate : Finset (Fin 6) → ℝ,
      (∀ window ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4, candidate window ≤ 0)
      ∧ (∑ window ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4, candidate window = budget)
      ∧ candidate {0, 1, 2, 4} < 0 := by
  refine budget_does_not_pin_coordinate
    ((Finset.univ : Finset (Fin 6)).powersetCard 4) {0, 1, 2, 4} {0, 1, 2, 3}
    (by decide) (by decide) (by decide) budget hbudget

end Gtz

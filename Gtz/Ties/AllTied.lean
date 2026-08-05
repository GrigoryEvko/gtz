/-
# The `(6,3)` all-twenty-dominate locus: the weight-positivity wall

**The question.**  Is there a `(6,3)` weighted design in which ALL TWENTY 3-subsets
weakly dominate — is `{D : WeightedDesign 6 3 | ∀ C, C.card = 3 → Dominates D C}`
empty?  It arose from the general-weight layer sum: a tie with all twenty dominating
forces `det N - 4 e₂(N) + 10 tr N - 20 = 0`, and that window vanishes on spectra that
really do occur, so the aggregate cannot close it.

**Verdict (measured, not mechanized here): the locus is EMPTY, with NO MARGIN.**
Everything below is the kernel-checkable part of why, plus the exact shape of the wall.

**The coordinates.**  Put `a_c := sqrt(t_c) • g_c` and let `A` be the `m × k` matrix of
rows `a_c`.  Parseval says `AᵀA = 1`, so `P := A Aᵀ` is a rank-`k` orthogonal projection
on `ℝ^m` — the repo's `projectionOfDesign` — and `dominates_iff_posSemidef_projectionBlock`
reads domination off it:

        Dominates D C   ↔   P[C,C] ⪰ diag(t_C).

`P` and `t` are INDEPENDENT: any rank-`k` projection and any interior simplex point
reassemble into a design by `g_c := a_c / sqrt(t_c)`.  So `(6,3)` designs modulo `O(3)`
are `Gr(3,6) × (open 5-simplex)`, of dimension `9 + 5 = 14`; the twenty conditions are
overdetermined by six, not five — the brief's count of fifteen omits `∑ t = 1`.

**Where the supremum lives.**  Relax `t > 0` to `t ≥ 0`.  Then the twenty conditions
together with `∑ t = 1` ARE satisfiable, and the witness sits one cell down: the
`(4,3)` tetrahedron — whose four triples all dominate, at an exact tie — padded with
two weightless atoms,

        P = diagonal(chi) - (1/4) • chi chiᵀ ,   chi = (1,1,1,1,0,0),
        t = (1/4, 1/4, 1/4, 1/4, 0, 0).

Along any injective `pick` the block collapses to `(3/4) diagonal(chi_C) - (1/4) chi_C chi_Cᵀ`,
positive semidefinite for the single reason that a 0/1 vector of length three has
squared norm at most 3.  Every block determinant is identically zero: the whole witness
lies on the PSD boundary, transporting the tetrahedron's tie.

That is `tetraPadRelaxation_isSolvable`, and `weightPositivity_isIndispensable` is its
contrapositive: **the projection data, the twenty block inequalities and `∑ t = 1` are
CONSISTENT, so no proof of the no-go can avoid consuming strict positivity of all six
weights.**  In particular the weighted layer aggregate `∑_C det(P[C,C] - diag(t_C))`,
which is the window read in projection variables, is exactly zero at the witness — it
has no slack to spend.  (The unweighted window in `N = ∑_c g_c g_cᵀ` is a `1/t_c`
quantity, so it is not a projection-variable aggregate and survives as a genuine
constraint — but see the next paragraph for why it cannot carry a margin either.)

**Why no inequality with slack can exist.**  Measured outside Lean, at 1e-15 agreement
with the dictionary above.  Write `sigma(P) := max {∑ t : t ≥ 0, P[C,C] ⪰ diag(t_C)}`;
the locus is nonempty iff some `P` with all twenty blocks NONSINGULAR has `sigma(P) ≥ 1`
(nonsingularity is forced, since `det P[C,C] ≥ ∏_{c∈C} t_c > 0`, and conversely convexity
in `t` lets one mix an optimal `t` with a uniform vector to regain strict positivity).
Maximising `sigma` subject to a floor `rho` on the least block eigenvalue gives

      rho floor   3e-2    1e-2    3e-3    1e-3    3e-4    1e-4    1e-5    1e-6
      max sigma   0.193   0.588   0.808   0.896   0.971   0.987   0.998   0.99992

so the supremum over nonsingular `P` is exactly 1, approached and never attained.
Equivalently, imposing a weight floor `t_c ≥ eta` and maximising the least block
margin gives `V(eta) ≈ -0.82 eta` at `(6,3)` (`-0.0674` at `eta = 1/12`, `-0.0459` at
`1/18`) and `≈ -0.80 eta` at `(5,3)` — strictly negative for every `eta > 0`, vanishing
linearly.  The same computation returns `V ≡ 0` at `(4,3)`, recovering the tetrahedron.
So the no-go is true but carries zero margin: a Positivstellensatz or Nullstellensatz
certificate — which would exhibit a strictly positive deficiency — cannot be its shape.

**The mechanism of the jump.**  Let atom 5 shrink, `a_5 = eps * n`.  Rescaling the third
coordinate of the triple `{i,j,5}` block by `1/eps` sends it to an `eps`-free condition
`[[P_ii - t_i, P_ij], [P_ij, P_jj - t_j]] ⪰ w wᵀ` with `w = (⟨a_i,n⟩, ⟨a_j,n⟩)`.  At the
tetrahedron the left side is `[[1/2,-1/4],[-1/4,1/2]]`, so the condition is
`w_i² + w_i w_j + w_j² ≤ 3/8` for all six pairs.  But the tetrahedron has `∑_c a_c = 0`
and `∑_c a_c a_cᵀ = 1`, hence `∑_c w_c = 0` and `∑_c w_c² = 1`, so `e₂(w) = -1/2` and the
six pair-values total `3 - 1/2 = 5/2`: their maximum is at least `5/12 > 3/8` (the true
minimax is exactly `1/2`, at `w = (1,-1,0,0)/sqrt 2`).  The tetrahedral supremum is
therefore not approachable, which is why `sigma` JUMPS from 1 to about 0.76 rather than
decaying — and why the sup over nonsingular `P` is attained nowhere.

**The Gale dual** (derived and numerically verified here, not mechanized).  With
`Q := 1 - P = H Hᵀ`, `HᵀH = 1`, `s_c := 1 - t_c` and `u_c := h_c / sqrt(s_c)`, the
question is its own Loewner mirror:

    PRIMAL   ∑_c t_c g_c g_cᵀ = 1, ∑ t = 1,   ∑_{c∈C} g_c g_cᵀ ⪰ 1
    DUAL     ∑_c s_c u_c u_cᵀ = 1, ∑ s = 5,   ∑_{c∈C} u_c u_cᵀ ⪯ 1

With `M := ∑_c u_c u_cᵀ` one gets `1 ⪯ M ⪯ 2` and, by the same Cauchy–Binet layer law,
the SAME window polynomial with the OPPOSITE sign, read at `M`:
`det M - 4 e₂(M) + 10 tr M - 20 ≤ 0`.  In `z_i = eig_i(M) - 1 ≥ 0` that is
`3 e₁(z) - 3 e₂(z) + e₃(z) ≤ 1`, capping `tr M ≤ 3.3811`, whereas uniform weights force
`M = (6/5)·1` and `tr M = 18/5` — so uniform weights are excluded by the dual window
alone, with no tie hypothesis.

**Also here.**  `sq_rank_le_trace_subsetSum_univ`: every weighted `(m,k)` design has
`k² ≤ tr N`, unconditionally; at `(6,3)`, `tr N ≥ 9`.  Sharp as an infimum and not
attained — equality would force every `P_cc = 1`, i.e. `P = 1`, of rank `m` not `k`.
This is the realisability floor the campaign lacked.  Both spectra flagged as
window-zero, `(58/5, 8, 8)` and `(73/5, 46/5, 13/2)`, clear it (traces `138/5` and
`303/10`) and both were confirmed realisable as `N` of an honest `(6,3)` design with
strictly positive weights — so neither refutes anything, and the sibling lane's refusal
to claim the aggregate closes the cell was correct.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.PrincipalMinorsThree
import Gtz.Quantitative.FlooredSpreadRegion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## The diagonal of the design projection lies in `[0,1]`

`P = A Aᵀ` is symmetric idempotent, so `P_cc = ∑_d P_cd²  ≥  P_cc²`. -/

section ProjectionDiagonal

variable {m k : ℕ}

theorem isSymm_projectionOfDesign (design : WeightedDesign m k) :
    (projectionOfDesign design).IsSymm := by
  unfold Matrix.IsSymm projectionOfDesign
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

theorem projectionDiagonal_le_one (design : WeightedDesign m k) (atomIndex : Fin m) :
    projectionOfDesign design atomIndex atomIndex ≤ 1 := by
  have hidempotent := projectionOfDesign_mul_self design
  have hsymm := isSymm_projectionOfDesign design
  have hentry : ∑ other, projectionOfDesign design atomIndex other
        * projectionOfDesign design other atomIndex
      = projectionOfDesign design atomIndex atomIndex := by
    have := congrArg (fun matrix => matrix atomIndex atomIndex) hidempotent
    simpa [Matrix.mul_apply] using this
  have hsquares : ∑ other, projectionOfDesign design atomIndex other ^ 2
      = projectionOfDesign design atomIndex atomIndex := by
    rw [← hentry]
    refine Finset.sum_congr rfl fun other _ => ?_
    have hflip : projectionOfDesign design other atomIndex
        = projectionOfDesign design atomIndex other :=
      congrFun (congrFun hsymm atomIndex) other
    rw [hflip, sq]
  have hdominant : projectionOfDesign design atomIndex atomIndex ^ 2
      ≤ projectionOfDesign design atomIndex atomIndex := by
    calc projectionOfDesign design atomIndex atomIndex ^ 2
        ≤ ∑ other, projectionOfDesign design atomIndex other ^ 2 :=
          Finset.single_le_sum
            (f := fun other => projectionOfDesign design atomIndex other ^ 2)
            (fun other _ => sq_nonneg _) (Finset.mem_univ atomIndex)
      _ = projectionOfDesign design atomIndex atomIndex := hsquares
  nlinarith [hdominant]

theorem weight_mul_leverage_le_one (design : WeightedDesign m k) (atomIndex : Fin m) :
    design.weight atomIndex * leverageOf (design.atom atomIndex) ≤ 1 := by
  rw [← projectionOfDesign_diagonal design atomIndex]
  exact projectionDiagonal_le_one design atomIndex

end ProjectionDiagonal

/-! ## The trace floor `k² ≤ tr N`

`N = ∑_c g_c g_cᵀ` is the unweighted moment.  Cauchy–Schwarz on
`k = ∑_c t_c ℓ_c = ∑_c sqrt(ℓ_c) · (t_c sqrt(ℓ_c))` against `∑_c t_c (t_c ℓ_c) ≤ ∑_c t_c = 1`
gives `k² ≤ ∑_c ℓ_c = tr N`.  The bound is sharp as an infimum, not attained: equality
would force every `P_cc = 1`, i.e. `P = 1`, of rank `m` rather than `k`. -/

section TraceFloor

variable {m k : ℕ}

theorem trace_subsetSum_univ (design : WeightedDesign m k) :
    Matrix.trace (subsetSum design Finset.univ)
      = ∑ atomIndex, leverageOf (design.atom atomIndex) := by
  rw [subsetSum, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun atomIndex _ => trace_atomMatrix (design.atom atomIndex)

/-- **The realisability floor.**  Every weighted `(m,k)` design has
`k² ≤ tr(∑_c g_c g_cᵀ)`; at `(6,3)` that reads `tr N ≥ 9`. -/
theorem sq_rank_le_trace_subsetSum_univ (design : WeightedDesign m k) :
    ((k : ℝ)) ^ 2 ≤ Matrix.trace (subsetSum design Finset.univ) := by
  set leverage : Fin m → ℝ := fun atomIndex => leverageOf (design.atom atomIndex)
    with hleverage
  have hnonneg : ∀ atomIndex, 0 ≤ leverage atomIndex := fun atomIndex =>
    leverageOf_nonneg (design.atom atomIndex)
  have hweighted : ∑ atomIndex, design.weight atomIndex * leverage atomIndex = (k : ℝ) :=
    sum_weight_mul_leverage design
  have hsplit : ∀ atomIndex : Fin m,
      design.weight atomIndex * leverage atomIndex
        = Real.sqrt (leverage atomIndex)
          * (design.weight atomIndex * Real.sqrt (leverage atomIndex)) := by
    intro atomIndex
    have hsq : Real.sqrt (leverage atomIndex) * Real.sqrt (leverage atomIndex)
        = leverage atomIndex := Real.mul_self_sqrt (hnonneg atomIndex)
    calc design.weight atomIndex * leverage atomIndex
        = design.weight atomIndex
            * (Real.sqrt (leverage atomIndex) * Real.sqrt (leverage atomIndex)) := by
          rw [hsq]
      _ = Real.sqrt (leverage atomIndex)
            * (design.weight atomIndex * Real.sqrt (leverage atomIndex)) := by ring
  have hcauchy :
      (∑ atomIndex, Real.sqrt (leverage atomIndex)
          * (design.weight atomIndex * Real.sqrt (leverage atomIndex))) ^ 2
        ≤ (∑ atomIndex, Real.sqrt (leverage atomIndex) ^ 2)
          * ∑ atomIndex, (design.weight atomIndex * Real.sqrt (leverage atomIndex)) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hleft : (∑ atomIndex, Real.sqrt (leverage atomIndex) ^ 2) = ∑ atomIndex, leverage atomIndex := by
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [sq, Real.mul_self_sqrt (hnonneg atomIndex)]
  have hright : (∑ atomIndex, (design.weight atomIndex * Real.sqrt (leverage atomIndex)) ^ 2)
      ≤ 1 := by
    have hterm : ∀ atomIndex ∈ (Finset.univ : Finset (Fin m)),
        (design.weight atomIndex * Real.sqrt (leverage atomIndex)) ^ 2
          ≤ design.weight atomIndex := by
      intro atomIndex _
      have hsq : Real.sqrt (leverage atomIndex) ^ 2 = leverage atomIndex := by
        rw [sq, Real.mul_self_sqrt (hnonneg atomIndex)]
      have hcap : design.weight atomIndex * leverage atomIndex ≤ 1 :=
        weight_mul_leverage_le_one design atomIndex
      have hpos : 0 < design.weight atomIndex := design.weight_pos atomIndex
      have hexpand : (design.weight atomIndex * Real.sqrt (leverage atomIndex)) ^ 2
          = design.weight atomIndex * (design.weight atomIndex * leverage atomIndex) := by
        rw [mul_pow, hsq]; ring
      rw [hexpand]
      nlinarith [hcap, hpos]
    calc (∑ atomIndex, (design.weight atomIndex * Real.sqrt (leverage atomIndex)) ^ 2)
        ≤ ∑ atomIndex, design.weight atomIndex := Finset.sum_le_sum hterm
      _ = 1 := design.weight_sum_one
  have hsum : ∑ atomIndex, Real.sqrt (leverage atomIndex)
      * (design.weight atomIndex * Real.sqrt (leverage atomIndex)) = (k : ℝ) := by
    rw [← hweighted]
    exact Finset.sum_congr rfl fun atomIndex _ => (hsplit atomIndex).symm
  rw [trace_subsetSum_univ design, ← hleft]
  rw [hsum] at hcauchy
  have htotal : 0 ≤ ∑ atomIndex, Real.sqrt (leverage atomIndex) ^ 2 := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [hcauchy, hright, htotal]

/-- The `(6,3)` reading: the unweighted moment has trace at least nine. -/
theorem nine_le_trace_subsetSum_univ (design : WeightedDesign 6 3) :
    (9 : ℝ) ≤ Matrix.trace (subsetSum design Finset.univ) := by
  have := sq_rank_le_trace_subsetSum_univ design
  norm_num at this
  exact this

end TraceFloor

/-! ## The tetrahedron padded with two weightless atoms

The relaxation of the all-twenty-dominate question that allows `t_c = 0` is
satisfiable.  The witness is the `(4,3)` tetrahedron sitting inside `(6,3)` with two
null atoms; every block collapses to `(3/4) diagonal(chi) - (1/4) chi chiᵀ`. -/

section TetraPad

/-- The 0/1 indicator of the four tetrahedral slots. -/
def coreIndicator : Fin 6 → ℝ := fun index => if index.val < 4 then 1 else 0

@[simp] theorem coreIndicator_zero : coreIndicator 0 = 1 := if_pos (by decide)
@[simp] theorem coreIndicator_one : coreIndicator 1 = 1 := if_pos (by decide)
@[simp] theorem coreIndicator_two : coreIndicator 2 = 1 := if_pos (by decide)
@[simp] theorem coreIndicator_three : coreIndicator 3 = 1 := if_pos (by decide)
@[simp] theorem coreIndicator_four : coreIndicator 4 = 0 := if_neg (by decide)
@[simp] theorem coreIndicator_five : coreIndicator 5 = 0 := if_neg (by decide)

theorem coreIndicator_nonneg (index : Fin 6) : 0 ≤ coreIndicator index := by
  fin_cases index <;> norm_num [coreIndicator]

theorem coreIndicator_idem (index : Fin 6) :
    coreIndicator index * coreIndicator index = coreIndicator index := by
  fin_cases index <;> norm_num [coreIndicator]

theorem coreIndicator_eq_zero_or_one (index : Fin 6) :
    coreIndicator index = 0 ∨ coreIndicator index = 1 := by
  fin_cases index <;> norm_num [coreIndicator]

/-- `P = diagonal(chi) - (1/4) chi chiᵀ`: the tetrahedron's rank-3 projection on the
first four coordinates, padded by zero on the last two. -/
noncomputable def tetraPadProjection : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.diagonal coreIndicator - (1 / 4 : ℝ) • Matrix.vecMulVec coreIndicator coreIndicator

/-- `t = (1/4,1/4,1/4,1/4,0,0)`: uniform on the tetrahedron, zero on the padding. -/
noncomputable def tetraPadWeight : Fin 6 → ℝ := fun index => coreIndicator index / 4

theorem tetraPadWeight_nonneg (index : Fin 6) : 0 ≤ tetraPadWeight index := by
  unfold tetraPadWeight
  exact div_nonneg (coreIndicator_nonneg index) (by norm_num)

theorem sum_tetraPadWeight : ∑ index, tetraPadWeight index = 1 := by
  norm_num [tetraPadWeight, coreIndicator, Fin.sum_univ_six]

theorem isSymm_tetraPadProjection : tetraPadProjection.IsSymm := by
  unfold Matrix.IsSymm tetraPadProjection
  ext rowIndex colIndex
  simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.diagonal_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rcases eq_or_ne rowIndex colIndex with heq | hne
  · rw [heq]
  · rw [if_neg hne, if_neg (Ne.symm hne)]
    ring

theorem tetraPadProjection_diag (index : Fin 6) :
    tetraPadProjection index index = 3 / 4 * coreIndicator index := by
  simp only [tetraPadProjection, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.diagonal_apply_eq, Matrix.vecMulVec_apply, smul_eq_mul]
  have hidem := coreIndicator_idem index
  linarith [hidem]

theorem trace_tetraPadProjection : Matrix.trace tetraPadProjection = 3 := by
  rw [Matrix.trace, Fin.sum_univ_six]
  simp only [Matrix.diag_apply, tetraPadProjection_diag]
  norm_num [coreIndicator]

/-- `P` is idempotent, so it is the orthogonal projection onto a 3-dimensional
subspace of `ℝ⁶` — exactly the shape `projectionOfDesign` produces. -/
theorem tetraPadProjection_apply (rowIndex colIndex : Fin 6) :
    tetraPadProjection rowIndex colIndex
      = (if rowIndex = colIndex then coreIndicator rowIndex else 0)
        - coreIndicator rowIndex * coreIndicator colIndex / 4 := by
  simp only [tetraPadProjection, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.diagonal_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

theorem sum_coreIndicator : ∑ index, coreIndicator index = 4 := by
  rw [Fin.sum_univ_six]
  norm_num [coreIndicator]

theorem tetraPadProjection_mul_self :
    tetraPadProjection * tetraPadProjection = tetraPadProjection := by
  ext rowIndex colIndex
  rw [Matrix.mul_apply, tetraPadProjection_apply]
  have hexpand : ∀ middle : Fin 6,
      tetraPadProjection rowIndex middle * tetraPadProjection middle colIndex
        = (if rowIndex = middle then coreIndicator rowIndex else 0)
            * (if middle = colIndex then coreIndicator middle else 0)
          - (if middle = colIndex then coreIndicator middle else 0)
            * (coreIndicator rowIndex * coreIndicator middle / 4)
          - (if rowIndex = middle then coreIndicator rowIndex else 0)
            * (coreIndicator middle * coreIndicator colIndex / 4)
          + coreIndicator rowIndex * coreIndicator colIndex / 16
            * (coreIndicator middle * coreIndicator middle) := by
    intro middle
    rw [tetraPadProjection_apply rowIndex middle, tetraPadProjection_apply middle colIndex]
    ring
  rw [Finset.sum_congr rfl fun middle _ => hexpand middle]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hfirst : ∑ middle, (if rowIndex = middle then coreIndicator rowIndex else 0)
      * (if middle = colIndex then coreIndicator middle else 0)
      = if rowIndex = colIndex then coreIndicator rowIndex else 0 := by
    rw [Finset.sum_eq_single rowIndex]
    · rw [if_pos rfl]
      rcases eq_or_ne rowIndex colIndex with heq | hne
      · rw [if_pos heq]
        exact coreIndicator_idem rowIndex
      · rw [if_neg hne]
        ring
    · intro middle _ hne
      rw [if_neg (Ne.symm hne), zero_mul]
    · intro hcontra
      exact absurd (Finset.mem_univ rowIndex) hcontra
  have hsecond : ∑ middle, (if middle = colIndex then coreIndicator middle else 0)
      * (coreIndicator rowIndex * coreIndicator middle / 4)
      = coreIndicator rowIndex * coreIndicator colIndex / 4 := by
    rw [Finset.sum_eq_single colIndex]
    · rw [if_pos rfl]
      linear_combination (coreIndicator rowIndex / 4) * coreIndicator_idem colIndex
    · intro middle _ hne
      rw [if_neg hne, zero_mul]
    · intro hcontra
      exact absurd (Finset.mem_univ colIndex) hcontra
  have hthird : ∑ middle, (if rowIndex = middle then coreIndicator rowIndex else 0)
      * (coreIndicator middle * coreIndicator colIndex / 4)
      = coreIndicator rowIndex * coreIndicator colIndex / 4 := by
    rw [Finset.sum_eq_single rowIndex]
    · rw [if_pos rfl]
      linear_combination (coreIndicator colIndex / 4) * coreIndicator_idem rowIndex
    · intro middle _ hne
      rw [if_neg (Ne.symm hne), zero_mul]
    · intro hcontra
      exact absurd (Finset.mem_univ rowIndex) hcontra
  have hfourth : ∑ middle : Fin 6, coreIndicator rowIndex * coreIndicator colIndex / 16
      * (coreIndicator middle * coreIndicator middle)
      = coreIndicator rowIndex * coreIndicator colIndex / 4 := by
    rw [← Finset.mul_sum]
    have hidem : ∑ middle : Fin 6, coreIndicator middle * coreIndicator middle
        = 4 := by
      rw [← sum_coreIndicator]
      exact Finset.sum_congr rfl fun middle _ => coreIndicator_idem middle
    rw [hidem]
    ring
  rw [hfirst, hsecond, hthird, hfourth]
  ring

/-! ### The twenty blocks -/

/-- Along an injective `pick`, the block matrix is
`(3/4) diagonal(chi ∘ pick) - (1/4) (chi ∘ pick)(chi ∘ pick)ᵀ`. -/
theorem tetraPadBlock_apply (pick : Fin 3 → Fin 6) (hinj : Function.Injective pick)
    (rowSlot colSlot : Fin 3) :
    (tetraPadProjection.submatrix pick pick
        - Matrix.diagonal (fun slot => tetraPadWeight (pick slot))) rowSlot colSlot
      = (if rowSlot = colSlot then (3 / 4 : ℝ) * coreIndicator (pick rowSlot) else 0)
        - (1 / 4 : ℝ) * (coreIndicator (pick rowSlot) * coreIndicator (pick colSlot)) := by
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, tetraPadProjection,
    Matrix.smul_apply, Matrix.diagonal_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    tetraPadWeight]
  rcases eq_or_ne rowSlot colSlot with heq | hne
  · subst heq
    rw [if_pos rfl, if_pos rfl, if_pos rfl]
    ring
  · rw [if_neg hne, if_neg hne, if_neg (fun hcontra => hne (hinj hcontra))]
    ring

/-- **Every one of the twenty blocks is positive semidefinite.**  The determinant is
identically zero, so the witness sits exactly on the PSD boundary — this is the
tetrahedron's tie, transported. -/
theorem posSemidef_tetraPadBlock (pick : Fin 3 → Fin 6) (hinj : Function.Injective pick) :
    (tetraPadProjection.submatrix pick pick
      - Matrix.diagonal (fun slot => tetraPadWeight (pick slot))).PosSemidef := by
  have hentry := tetraPadBlock_apply pick hinj
  set block := tetraPadProjection.submatrix pick pick
    - Matrix.diagonal (fun slot => tetraPadWeight (pick slot)) with hblock
  have hdiag : ∀ slot : Fin 3, block slot slot = coreIndicator (pick slot) / 2 := by
    intro slot
    rw [hentry slot slot, if_pos rfl]
    have hidem := coreIndicator_idem (pick slot)
    linarith [hidem]
  have hoff : ∀ rowSlot colSlot : Fin 3, rowSlot ≠ colSlot →
      block rowSlot colSlot
        = -(coreIndicator (pick rowSlot) * coreIndicator (pick colSlot) / 4) := by
    intro rowSlot colSlot hne
    rw [hentry rowSlot colSlot, if_neg hne]; ring
  have hsymmetric : blockᵀ = block := by
    ext rowSlot colSlot
    rw [Matrix.transpose_apply, hentry colSlot rowSlot, hentry rowSlot colSlot]
    rcases eq_or_ne rowSlot colSlot with heq | hne
    · rw [heq]
    · rw [if_neg hne, if_neg (Ne.symm hne)]; ring
  have hzeroZero := hdiag 0
  have honeOne := hdiag 1
  have htwoTwo := hdiag 2
  have hzeroOne := hoff 0 1 (by decide)
  have hzeroTwo := hoff 0 2 (by decide)
  have honeTwo := hoff 1 2 (by decide)
  have honeZero := hoff 1 0 (by decide)
  have htwoZero := hoff 2 0 (by decide)
  have htwoOne := hoff 2 1 (by decide)
  rcases coreIndicator_eq_zero_or_one (pick 0) with hcase0 | hcase0 <;>
  rcases coreIndicator_eq_zero_or_one (pick 1) with hcase1 | hcase1 <;>
  rcases coreIndicator_eq_zero_or_one (pick 2) with hcase2 | hcase2 <;>
  refine posSemidef_three_of_principalMinors hsymmetric ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
  simp only [Matrix.det_fin_three, hzeroZero, honeOne, htwoTwo, hzeroOne, hzeroTwo,
    honeTwo, honeZero, htwoZero, htwoOne, hcase0, hcase1, hcase2] <;>
  norm_num

/-- **The relaxation is solvable.**  Dropping `weight_pos` — and only that — turns the
question into a satisfiable system: a rank-3 orthogonal projection on `ℝ⁶`, a
nonnegative weight vector summing to one, and all twenty block inequalities. -/
theorem tetraPadRelaxation_isSolvable :
    ∃ (projection : Matrix (Fin 6) (Fin 6) ℝ) (weight : Fin 6 → ℝ),
      projection.IsSymm ∧
      projection * projection = projection ∧
      Matrix.trace projection = 3 ∧
      (∀ atomIndex, 0 ≤ weight atomIndex) ∧
      (∑ atomIndex, weight atomIndex) = 1 ∧
      (∀ pick : Fin 3 → Fin 6, Function.Injective pick →
        (projection.submatrix pick pick
          - Matrix.diagonal (fun slot => weight (pick slot))).PosSemidef) :=
  ⟨tetraPadProjection, tetraPadWeight, isSymm_tetraPadProjection,
    tetraPadProjection_mul_self, trace_tetraPadProjection, tetraPadWeight_nonneg,
    sum_tetraPadWeight, posSemidef_tetraPadBlock⟩

/-- **The wall, as a theorem.**  No argument can refute all-twenty-domination at
`(6,3)` from the projection data, the twenty block inequalities, and `∑ t = 1` alone:
that package is consistent.  Any proof of the no-go must consume the STRICT positivity
of every one of the six weights.  In particular the layer window, and every other
aggregate identity in the projection variables, is powerless on its own — the
supremum it must beat is attained, exactly, by the `(4,3)` tetrahedron carrying two
weightless atoms. -/
theorem weightPositivity_isIndispensable :
    ¬ (∀ (projection : Matrix (Fin 6) (Fin 6) ℝ) (weight : Fin 6 → ℝ),
        projection.IsSymm →
        projection * projection = projection →
        Matrix.trace projection = 3 →
        (∀ atomIndex, 0 ≤ weight atomIndex) →
        (∑ atomIndex, weight atomIndex) = 1 →
        (∀ pick : Fin 3 → Fin 6, Function.Injective pick →
          (projection.submatrix pick pick
            - Matrix.diagonal (fun slot => weight (pick slot))).PosSemidef) →
        False) := by
  intro hrefutation
  obtain ⟨projection, weight, hsymm, hidem, htrace, hnonneg, hsum, hblocks⟩ :=
    tetraPadRelaxation_isSolvable
  exact hrefutation projection weight hsymm hidem htrace hnonneg hsum hblocks

end TetraPad

end Gtz

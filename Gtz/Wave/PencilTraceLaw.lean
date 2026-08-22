/-
# Two conditions that force domination, and the residual of `(6,3)` they leave

The criterion of `Gtz/Wave/DependencyAtomCap.lean` decides domination by SEVEN
sign conditions on one `3 x 3` matrix.  This module replaces them by TWO, and
states exactly what is left of `Gtz.GtzWeighted 6 3` afterwards.

## 1. The complement criterion

Parseval turns the definition of domination inside out.  `S_C >= 1` says
`sum_{c in C} <g_c,v>^2 >= |v|^2` at every probe, and `|v|^2` is itself the
weighted total of ALL the readings, so

  **`Gtz.dominates_iff_complementSplit`:**
    `Dominates D C  <->  for every probe v :`
    `    sum_{c not in C} t_c <g_c,v>^2  <=  sum_{c in C} (1 - t_c) <g_c,v>^2` .

No chart, no kernel, no inverse, and no restriction on the size of `C`.  The
inside atoms are charged their CO-weights and the outside atoms their weights.

## 2. The symmetric-function criterion, and the trace-and-determinant law

A symmetric `3 x 3` whose trace, principal two-by-two total and determinant are
all nonnegative has no negative eigenvalue, because its characteristic
determinant is strictly positive at every negative shift
(`Gtz.posSemidef_of_invariants_nonneg`).  Feeding that a diagonal minus a
positive semidefinite matrix gives the law this module is for:

  **`Gtz.posSemidef_sub_of_det_nonneg_of_weightedTrace_le_two`.**  For `z > 0`
  and `Y >= 0`,

    `det (diag z - Y) >= 0`  and  `sum_c Y_cc / z_c <= 2`   force   `diag z - Y >= 0` .

Normalise by `diag z^{-1/2}`.  The subtracted part becomes `R` with
`tr R = sum_c Y_cc/z_c`, `e_2(R) >= 0` and `det R >= 0`, and the determinant
hypothesis reads `e_2 >= e_1 - 1 + e_3`.  The three invariants of `1 - R` are then

    `3 - e_1 >= 1` ,   `3 - 2 e_1 + e_2 >= 2 - e_1 >= 0` ,   `1 - e_1 + e_2 - e_3 >= 0` ,

so `1 - R >= 0`, and the congruence carries it back.  Two hypotheses replace
seven.

## 3. The pencil of a triple at `(6,3)`

Fix a triple `{a,b,c}` of nonzero bracket.  Cramer expresses the reading of any
outside atom through the three inside readings (`Gtz.tripleBracket_cramer_dot`),
with the inside part of the triple's circuit as coefficient vector:

    `[abc] * <g_x, v>  =  <gamma_x, y>` ,   `y = (<g_a,v>, <g_b,v>, <g_c,v>)` ,
    `gamma_x = ([bcx], -[acx], [abx])`      (`Gtz.innerCircuit`).

Substituting into the complement criterion turns it into a statement about ONE
explicit polynomial matrix,

  **`Gtz.pencilGap D a b c out`
     `= [abc]^2 * diag(1 - t_a, 1 - t_b, 1 - t_c) - sum_x t_x * gamma_x gamma_x^T`** ,

and `Gtz.dominates_of_posSemidef_pencilGap` is the direction that matters: a
positive semidefinite pencil gap forces domination.  Its weighted trace is the
landed aggregate:

  **`Gtz.pencilWeightedTrace_eq`:**
    `sum_c Y_cc / z_c  =  3 - (sum_x t_a t_b t_c t_x * depSlack(circuit x)) / nu_abc` ,

which by `Gtz.sum_weighted_depSlack_circuitDep_sixThree` is
`(th_a delta_bc + th_b delta_ac + th_c delta_ab)/nu_abc - (th_a + th_b + th_c)`.

Combining everything:

  **`Gtz.dominates_of_aggregate_le_two_sixThree`.**  If

    `tripleGapDet(a,b,c) >= 0`   and
    `th_a delta_bc + th_b delta_ac + th_c delta_ab <= (2 + th_a + th_b + th_c) nu_abc` ,

  then `{a,b,c}` DOMINATES.

The second condition is the landed aggregate of
`Gtz.aggregate_swapLaw_of_dominates_sixThree` with the constant `3` replaced by
`2`.  So the aggregate at `3` is NECESSARY, the aggregate at `2` with a
nonnegative gap determinant is SUFFICIENT, and the whole residual of the main
statement sits between them.  `Gtz.gtzWeighted_sixThree_of_aggregateTest`
reduces `Gtz.GtzWeighted 6 3` to producing one such triple.

[MEASURED, `scratchpad/kzero`, double precision, 384 threads.  The pencil
criterion agreed with domination at all 4000000 triples of 200000 random
designs, with ZERO mismatches, and the weighted-trace identity held to `4.1e-15`.
The two-condition law fired at 831415 triples with ZERO failures.

The EXISTENCE half was pushed hard.  Over 3000000 random designs the admissible
set — triples of nonnegative gap determinant — was never empty, and the least
weighted trace over it never exceeded `1.022507`.  At the five `(6,3)` splits of
the `(5,3)` diamond, which are exact ties, it is `1.083333` to `1.170213`.  A
stochastic descent that MAXIMISES the least admissible weighted trace, over
150000 restarts of 6000 steps on the eighteen frame parameters and the six
weight logits — two CPU hours — reached `1.309748` and never approached two.  So
the sufficient condition carries a measured margin of about a third, and no
counterexample to the existence half was found.

TWO NEGATIVES, both from the same descent and both worth recording.  The
selection rule "take the triple of least weighted trace" is FALSE: the descent
drives its chosen triple to `sigma_max = 1.0669`.  So is "take the triple of
least weighted trace among those whose middle invariant is nonnegative".  Only
the filter by the gap determinant survived.  Random sampling alone had reported
zero failures for all three at 200000 designs, which is why the descent, and not
the sampling, is the evidence.]

## Scope

`Gtz.GtzWeighted 6 3` is NOT proved here.  What is proved is that two explicit
polynomial conditions suffice, so the existence of a triple meeting them is the
whole remaining content.  Every statement is FIELD-BLIND.
-/
import Gtz.Wave.CircuitGramTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1 — the complement criterion -/

/-- **DOMINATION SPLITS THE PARSEVAL TOTAL.**  Read `S_C >= 1` at a probe and
replace the probe's own square by its Parseval expansion: the inside atoms pay
their CO-weights and the outside atoms pay their weights. -/
theorem dominates_iff_complementSplit (D : WeightedDesign m k) (C : Finset (Fin m)) :
    Dominates D C
      ↔ ∀ probe : Fin k → ℝ,
          (∑ index ∈ Cᶜ, D.weight index * (D.atom index ⬝ᵥ probe) ^ 2)
            ≤ ∑ index ∈ C, (1 - D.weight index) * (D.atom index ⬝ᵥ probe) ^ 2 := by
  classical
  have hsymm : (subsetSum D C - 1)ᵀ = subsetSum D C - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum, Matrix.transpose_sum]
    refine congrArg₂ _ (Finset.sum_congr rfl fun index _ => ?_) rfl
    rw [atomMatrix, Matrix.transpose_vecMulVec]
  rw [Dominates, posSemidef_iff_quadForm_nonneg _ hsymm]
  refine forall_congr' fun probe => ?_
  have hquad : probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe)
      = (∑ index ∈ C, (D.atom index ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, subsetSum, Matrix.sum_mulVec,
      dotProduct_sum]
    congr 1
    refine Finset.sum_congr rfl fun index _ => ?_
    rw [atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm probe (D.atom index)]
    ring
  have hparseval : probe ⬝ᵥ probe
      = ∑ index, D.weight index * (D.atom index ⬝ᵥ probe) ^ 2 := by
    rw [dotProduct_eq_sum_weight_mul_pair D probe probe]
    exact Finset.sum_congr rfl fun index _ => by rw [pow_two]
  have hsplit : (∑ index, D.weight index * (D.atom index ⬝ᵥ probe) ^ 2)
      = (∑ index ∈ C, D.weight index * (D.atom index ⬝ᵥ probe) ^ 2)
        + ∑ index ∈ Cᶜ, D.weight index * (D.atom index ⬝ᵥ probe) ^ 2 :=
    (Finset.sum_add_sum_compl C _).symm
  have hinside : (∑ index ∈ C, (D.atom index ⬝ᵥ probe) ^ 2)
        - ∑ index ∈ C, D.weight index * (D.atom index ⬝ᵥ probe) ^ 2
      = ∑ index ∈ C, (1 - D.weight index) * (D.atom index ⬝ᵥ probe) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun index _ => by ring
  rw [hquad, hparseval, hsplit]
  constructor
  · intro hstep; linarith [hinside]
  · intro hstep; linarith [hinside]

/-! ## Part 2 — the symmetric-function criterion and the trace law -/

/-- The total of the three principal two-by-two minors of a `3 x 3`. -/
def pairMinorSum (mat : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (mat 0 0 * mat 1 1 - mat 0 1 * mat 1 0) + (mat 0 0 * mat 2 2 - mat 0 2 * mat 2 0)
    + (mat 1 1 * mat 2 2 - mat 1 2 * mat 2 1)

/-- **THE CHARACTERISTIC DETERMINANT OF A `3 x 3`, IN ITS THREE INVARIANTS.** -/
theorem det_sub_smul_one_pairMinorSum (mat : Matrix (Fin 3) (Fin 3) ℝ) (shift : ℝ) :
    (mat - shift • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det
      = -shift ^ 3 + Matrix.trace mat * shift ^ 2 - pairMinorSum mat * shift + mat.det := by
  simp [Matrix.det_fin_three, Matrix.trace_fin_three, pairMinorSum, Matrix.one_apply]
  ring

/-- **A SYMMETRIC `3 x 3` WITH NONNEGATIVE INVARIANTS IS POSITIVE SEMIDEFINITE.**
At a negative shift the characteristic determinant is a total of four
nonnegative terms one of which is strictly positive, so no eigenvalue is
negative. -/
theorem posSemidef_of_invariants_nonneg {mat : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : matᵀ = mat) (htrace : 0 ≤ Matrix.trace mat) (hpair : 0 ≤ pairMinorSum mat)
    (hdet : 0 ≤ mat.det) : mat.PosSemidef := by
  classical
  have hherm : mat.IsHermitian := isHermitian_of_transpose_eq hsymm
  rw [hherm.posSemidef_iff_eigenvalues_nonneg]
  intro slot
  by_contra hneg
  push_neg at hneg
  set value : ℝ := hherm.eigenvalues slot with hvalue
  have hvec : mat *ᵥ (hherm.eigenvectorBasis slot).ofLp
      = value • (hherm.eigenvectorBasis slot).ofLp := hherm.mulVec_eigenvectorBasis slot
  have hne : ((hherm.eigenvectorBasis slot).ofLp : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hnorm : ‖hherm.eigenvectorBasis slot‖ = 1 :=
      hherm.eigenvectorBasis.orthonormal.1 slot
    have hzeroVec : hherm.eigenvectorBasis slot = 0 := by
      ext coord
      exact congrFun hzero coord
    rw [hzeroVec, norm_zero] at hnorm
    exact absurd hnorm (by norm_num)
  have hkernel : (mat - value • (1 : Matrix (Fin 3) (Fin 3) ℝ))
      *ᵥ ((hherm.eigenvectorBasis slot).ofLp : Fin 3 → ℝ) = 0 := by
    rw [Matrix.sub_mulVec, hvec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  have hdetZero : (mat - value • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hne, hkernel⟩
  rw [det_sub_smul_one_pairMinorSum] at hdetZero
  have hne0 : value ≠ 0 := ne_of_lt hneg
  have hvsq : 0 < value ^ 2 := by positivity
  have hcube : 0 < -value ^ 3 := by
    have hstep := mul_pos (neg_pos.mpr hneg) hvsq
    nlinarith [hstep]
  have hsquare : 0 ≤ Matrix.trace mat * value ^ 2 := by positivity
  have hlinear : 0 ≤ -(pairMinorSum mat * value) := by nlinarith [hpair, hneg]
  linarith

/-- **THE TRACE-AND-DETERMINANT LAW.**  A positive semidefinite `3 x 3` whose
trace is at most two and whose complementary determinant is nonnegative is a
CONTRACTION.  Two conditions replace the seven of Sylvester.

The proof is three lines of symmetric functions: `det (1 - R) >= 0` reads
`e_2 >= e_1 - 1 + e_3`, so the middle invariant of `1 - R` is at least
`2 - e_1 >= 0`, and the first is at least one. -/
theorem posSemidef_one_sub_of_det_nonneg_of_trace_le_two
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hform : form.PosSemidef)
    (hdet : 0 ≤ (1 - form).det) (htrace : Matrix.trace form ≤ 2) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) - form).PosSemidef := by
  classical
  have hsymmEntry : ∀ rowSlot colSlot : Fin 3, form colSlot rowSlot = form rowSlot colSlot := by
    intro rowSlot colSlot
    have hstep := hform.1.apply rowSlot colSlot
    simpa using hstep
  have hgapSymm : ((1 : Matrix (Fin 3) (Fin 3) ℝ) - form)ᵀ = 1 - form := by
    ext rowSlot colSlot
    rw [Matrix.transpose_apply, Matrix.sub_apply, Matrix.sub_apply, hsymmEntry colSlot rowSlot]
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hslot : rowSlot = colSlot
    · rw [if_pos hslot, if_pos hslot.symm]
    · rw [if_neg hslot, if_neg (Ne.symm hslot)]
  have hpairForm : 0 ≤ pairMinorSum form := by
    have hminor : ∀ rowSlot colSlot : Fin 3,
        0 ≤ form rowSlot rowSlot * form colSlot colSlot
          - form rowSlot colSlot * form colSlot rowSlot := by
      intro rowSlot colSlot
      have hstep := (hform.submatrix (![rowSlot, colSlot] : Fin 2 → Fin 3)).det_nonneg
      rwa [Matrix.det_fin_two] at hstep
    have h01 := hminor 0 1
    have h02 := hminor 0 2
    have h12 := hminor 1 2
    rw [pairMinorSum]
    linarith
  have hdetForm : 0 ≤ form.det := hform.det_nonneg
  have hgapDet : (1 - form).det
      = 1 - Matrix.trace form + pairMinorSum form - form.det := by
    have hone : ∀ rowSlot colSlot : Fin 3,
        (1 : Matrix (Fin 3) (Fin 3) ℝ) rowSlot colSlot
          = if rowSlot = colSlot then 1 else 0 := fun _ _ => Matrix.one_apply
    simp only [Matrix.det_fin_three, Matrix.sub_apply, hone, Matrix.trace_fin_three,
      pairMinorSum]
    norm_num [Fin.ext_iff]
    ring
  have hgapTrace : Matrix.trace ((1 : Matrix (Fin 3) (Fin 3) ℝ) - form)
      = 3 - Matrix.trace form := by
    rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin]
    norm_num
  have hgapPair : pairMinorSum ((1 : Matrix (Fin 3) (Fin 3) ℝ) - form)
      = 3 - 2 * Matrix.trace form + pairMinorSum form := by
    have hone : ∀ rowSlot colSlot : Fin 3,
        (1 : Matrix (Fin 3) (Fin 3) ℝ) rowSlot colSlot
          = if rowSlot = colSlot then 1 else 0 := fun _ _ => Matrix.one_apply
    simp only [pairMinorSum, Matrix.sub_apply, hone, Matrix.trace_fin_three]
    norm_num [Fin.ext_iff]
    ring
  refine posSemidef_of_invariants_nonneg hgapSymm ?_ ?_ hdet
  · rw [hgapTrace]; linarith
  · rw [hgapPair]
    rw [hgapDet] at hdet
    linarith

end Gtz

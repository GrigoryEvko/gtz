/-
# The triple-sum law, and the first size marker in the corank-one arm

`Gtz.sum_fourSet_gapDet_eq_det_sub_e2` totals the four triple gap determinants
of a FOUR-set against the two invariants of that four-set's own gap.  That is
the `q = 1` case of a law valid at every size, and the general law carries the
size explicitly.

## The law

Write `G` for the gap `S_S − 1` of a whole atom set `S`, and `q = |S| − 3`.
Then

  `Σ_{T ⊆ S, |T| = 3} det (S_T − 1)`
      `= det G − q · e₂(G) + C(q,2) · tr G − C(q,3)` .

* `q = 1` (four atoms) — `det G − e₂(G)`, the landed four-set law.
* `q = 2` (five atoms) — `Gtz.sum_fiveSet_gapDet_eq`, `det G − 2 e₂(G) + tr G`.
* `q = 3` (six atoms) — `Gtz.sum_sixSet_gapDet_eq`, `det G − 3 e₂(G) + 3 tr G − 1`.

## Why the coefficients move with the size

`S_S` and the Gram `Γ` share their nonzero spectrum, so the `m × m` matrix
`Γ − 1` has eigenvalues `λ₁ − 1, λ₂ − 1, λ₃ − 1` together with `−1` repeated
`m − 3` times.  Every `3 × 3` principal minor of `Γ − 1` is a triple gap
determinant, and the sum of all of them is `e₃` of that spectrum, so the law is
the `x³` coefficient of `(1 + a₁x)(1 + a₂x)(1 + a₃x)(1 − x)^(m−3)`.  **The
multiplicity `m − 3` is the size, and it is the only place the size enters.**

At the two fixtures the law reads

* the `(5,3)` primitive diamond, `G = 4 · 1`:  `64 − 2·48 + 12 = −20`,
  matching its eight zero triples and two at `−10`;
* the `(6,3)` split diamond, `G` with spectrum `(6,4,4)`:
  `96 − 3·64 + 3·14 − 1 = −55`, matching its twelve zero triples.

Both statements below are polynomial identities in the atom coordinates with no
hypothesis at all — no Parseval, no positivity, no invertibility.
-/
import Gtz.Wave.DiamondNeighborhoodFourSet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace Gtz

open Matrix Finset

/-! ## 1. The second invariant of a gap, named -/

/-- The second invariant of a `3 × 3` matrix, in the trace form the four-set
law already uses. -/
noncomputable def gapSecondInvariant (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ((Matrix.trace M) ^ 2 - Matrix.trace (M * M)) / 2

theorem sum_fourSet_gapDet_eq_det_sub_secondInvariant (a b c d : Fin 3 → ℝ) :
    tripleGapDet b c d + tripleGapDet a c d + tripleGapDet a b d + tripleGapDet a b c
      = (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1).det
        - gapSecondInvariant
            (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1) := by
  rw [gapSecondInvariant]
  exact sum_fourSet_tripleGapDet_eq_det_sub_e2 a b c d

/-! ## 2. The five-atom law (`q = 2`) -/

set_option linter.unusedSimpArgs false in
/-- **THE FIVE-SET LAW.**  The ten triple gap determinants of five atoms total

  `det G − 2 · e₂(G) + tr G` ,  `G = S_S − 1` .

A polynomial identity in fifteen variables, no hypothesis.  The coefficient
`2` and the appearance of `tr G` are the size `q = 2` showing itself. -/
theorem sum_fiveSet_gapDet_eq (a b c d e : Fin 3 → ℝ) :
    tripleGapDet a b c + tripleGapDet a b d + tripleGapDet a b e
        + tripleGapDet a c d + tripleGapDet a c e + tripleGapDet a d e
        + tripleGapDet b c d + tripleGapDet b c e + tripleGapDet b d e
        + tripleGapDet c d e
      = (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d
            + atomMatrix e - 1).det
        - 2 * gapSecondInvariant (atomMatrix a + atomMatrix b + atomMatrix c
            + atomMatrix d + atomMatrix e - 1)
        + Matrix.trace (atomMatrix a + atomMatrix b + atomMatrix c
            + atomMatrix d + atomMatrix e - 1) := by
  simp only [tripleGapDet, gapSecondInvariant, leverageOf, dotProduct,
    Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.mul_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, atomMatrix,
    Matrix.vecMulVec_apply, Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  ring

/-! ## 3. The six-atom law (`q = 3`) -/

set_option linter.unusedSimpArgs false in
/-- **THE SIX-SET LAW — THE SIZE MARKER.**  The twenty triple gap determinants
of six atoms total

  `det G − 3 · e₂(G) + 3 · tr G − 1` ,  `G = S_S − 1` .

A polynomial identity in eighteen variables, no hypothesis.  Against the
five-set law every coefficient has moved — `2 → 3`, `1 → 3`, and a constant
`−1` has appeared — because each is a binomial in `q = m − 3`.  This is the
first law in the corank-one arm whose STATEMENT depends on the size, which is
exactly what the arm's fixture filter demands: a law taking equal values at
the two fixtures cannot separate them, and this one cannot even be stated at
both sizes without changing. -/
theorem sum_sixSet_gapDet_eq (a b c d e f : Fin 3 → ℝ) :
    tripleGapDet a b c + tripleGapDet a b d + tripleGapDet a b e
        + tripleGapDet a b f + tripleGapDet a c d + tripleGapDet a c e
        + tripleGapDet a c f + tripleGapDet a d e + tripleGapDet a d f
        + tripleGapDet a e f
        + tripleGapDet b c d + tripleGapDet b c e + tripleGapDet b c f
        + tripleGapDet b d e + tripleGapDet b d f + tripleGapDet b e f
        + tripleGapDet c d e + tripleGapDet c d f + tripleGapDet c e f
        + tripleGapDet d e f
      = (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d
            + atomMatrix e + atomMatrix f - 1).det
        - 3 * gapSecondInvariant (atomMatrix a + atomMatrix b + atomMatrix c
            + atomMatrix d + atomMatrix e + atomMatrix f - 1)
        + 3 * Matrix.trace (atomMatrix a + atomMatrix b + atomMatrix c
            + atomMatrix d + atomMatrix e + atomMatrix f - 1)
        - 1 := by
  simp only [tripleGapDet, gapSecondInvariant, leverageOf, dotProduct,
    Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.mul_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, atomMatrix,
    Matrix.vecMulVec_apply, Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  ring

/-! ## 4. Branch B, and what the size law says there -/

/-- **BRANCH B.**  Every atom heavy and every pair admissible.  Then EVERY
triple is live, so at a tie every one of the `C(m,3)` gap determinants is
nonpositive.

A parallel pair is never admissible once either member is heavy
(`Gtz.not_admissiblePair_of_parallel_of_heavy`), so a branch-B design has NO
parallel pair — branch B is exactly the region where the hinge's conclusion
fails.  The `(5,3)` primitive diamond lies in branch B; the `(6,3)` split
diamond does NOT, its two spine copies having pair minor `1 − 2ℓ = −3`. -/
def BranchB {m : ℕ} (D : WeightedDesign m 3) : Prop :=
  (∀ c : Fin m, HeavyAtom D c)
    ∧ ∀ x y : Fin m, x ≠ y → AdmissiblePair (D.atom x) (D.atom y)

/-- In branch B every triple of distinct labels is live. -/
theorem liveTriple_of_branchB {m : ℕ} {D : WeightedDesign m 3} (hB : BranchB D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    LiveTriple D x y z :=
  ⟨hB.1 x, hB.1 y, hB.1 z, hB.2 x y hxy, hB.2 x z hxz, hB.2 y z hyz⟩

/-- **THE SIZE LAW AT A BRANCH-B TIE, AT SIZE SIX.**  Every one of the twenty
triples is live, so every gap determinant is nonpositive, so the six-set law
turns twenty sign conditions into ONE bound on the invariants of the whole
design's gap:

  `det G − 3 · e₂(G) + 3 · tr G ≤ 1` .

The `(5,3)` statement carrying the same proof is `det G − 2 e₂(G) + tr G ≤ 0`,
and the primitive diamond satisfies it with room to spare (`−20`).  The two
bounds are different polynomials, so a design cannot satisfy one by satisfying
the other — the size is spent in the coefficients themselves. -/
theorem isTie_branchB_sixSet_bound (D : WeightedDesign 6 3) (htie : IsTie D)
    (hB : BranchB D) :
    (atomMatrix (D.atom 0) + atomMatrix (D.atom 1) + atomMatrix (D.atom 2)
        + atomMatrix (D.atom 3) + atomMatrix (D.atom 4) + atomMatrix (D.atom 5)
        - 1).det
      - 3 * gapSecondInvariant (atomMatrix (D.atom 0) + atomMatrix (D.atom 1)
          + atomMatrix (D.atom 2) + atomMatrix (D.atom 3) + atomMatrix (D.atom 4)
          + atomMatrix (D.atom 5) - 1)
      + 3 * Matrix.trace (atomMatrix (D.atom 0) + atomMatrix (D.atom 1)
          + atomMatrix (D.atom 2) + atomMatrix (D.atom 3) + atomMatrix (D.atom 4)
          + atomMatrix (D.atom 5) - 1)
      - 1 ≤ 0 := by
  have key := fun (x y z : Fin 6) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) =>
    isTie_live_gapDet_nonpos D htie hxy hxz hyz (liveTriple_of_branchB hB hxy hxz hyz)
  rw [← sum_sixSet_gapDet_eq]
  have h012 := key 0 1 2 (by decide) (by decide) (by decide)
  have h013 := key 0 1 3 (by decide) (by decide) (by decide)
  have h014 := key 0 1 4 (by decide) (by decide) (by decide)
  have h015 := key 0 1 5 (by decide) (by decide) (by decide)
  have h023 := key 0 2 3 (by decide) (by decide) (by decide)
  have h024 := key 0 2 4 (by decide) (by decide) (by decide)
  have h025 := key 0 2 5 (by decide) (by decide) (by decide)
  have h034 := key 0 3 4 (by decide) (by decide) (by decide)
  have h035 := key 0 3 5 (by decide) (by decide) (by decide)
  have h045 := key 0 4 5 (by decide) (by decide) (by decide)
  have h123 := key 1 2 3 (by decide) (by decide) (by decide)
  have h124 := key 1 2 4 (by decide) (by decide) (by decide)
  have h125 := key 1 2 5 (by decide) (by decide) (by decide)
  have h134 := key 1 3 4 (by decide) (by decide) (by decide)
  have h135 := key 1 3 5 (by decide) (by decide) (by decide)
  have h145 := key 1 4 5 (by decide) (by decide) (by decide)
  have h234 := key 2 3 4 (by decide) (by decide) (by decide)
  have h235 := key 2 3 5 (by decide) (by decide) (by decide)
  have h245 := key 2 4 5 (by decide) (by decide) (by decide)
  have h345 := key 3 4 5 (by decide) (by decide) (by decide)
  linarith

end Gtz

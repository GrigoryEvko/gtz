/-
# The corank-one adjugate law at every rank

The corank-one arm of the `(6,3)` campaign runs on two identities about a
symmetric gap `G` of corank one with unit kernel vector `w`:

  **`adj G = e_{k-1}(G) · w wᵀ`**   and   **`det (G + v vᵀ) = e_{k-1}(G) · ⟨v,w⟩²`** ,

where `e_{k-1}(G) = trace (adj G)` is the total of the principal minors of order
`k - 1`.  Both are landed only at rank three
(`Gtz.pairGapMinor_eq_pairMinorTotal_mul_reading_first` and
`Gtz.det_add_atomMatrix_of_unit_null`), where they are proved by explicit
`linear_combination` certificates on the nine entries.  That proof does not
generalize: at rank `k` the entries number `k²`.

This module proves both at EVERY rank, structurally.  The argument uses no
certificate, no eigenvalue and no characteristic polynomial:

* a symmetric matrix with a unit kernel vector is singular, so `G · adj G = 0`
  and every column of the adjugate lies in the kernel;
* under corank one the kernel is the line `ℝ w`, so the adjugate is `w cᵀ`;
* the adjugate of a symmetric matrix is symmetric, which forces `c ∈ ℝ w`;
* the trace names the scalar.

## Why this matters for the general-rank obligations

`Skeleton.obligationSubThresholdBandHinge` and
`Skeleton.obligationThresholdCellHingeRankFourAndUp` are the two registry
axioms above rank three, first live at `(8,4)`, `(9,4)` and `(10,4)`.  Their
`WHY OPEN` fields say that below the Veronese dimension the rank-three
instruments lose their precondition.  These two identities are exactly the
instruments the corank-one arm would carry there, and they are now available at
every rank, with the corank hypothesis written out rather than assumed silently.

The second identity is the general-rank form of the four-set law: adjoining one
atom to a corank-one gap produces a determinant that factors as the minor total
times the squared reading of that atom against the kernel.  At rank three it is
the campaign's `Gtz.det_add_atomMatrix_of_unit_null`, the law that makes a
corank-one weak dominator extend outward to a strictly dominating four-set.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.SchurRankOne
import Gtz.Wave.FlatPairWeakSeed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {k : ℕ}

/-! ## 1. A rank-one matrix applied to a vector

`Gtz.vecMulVec_mulVec_eq` (Gtz/LinAlg/SchurRankOne.lean) already states that the
rank-one matrix `a bᵀ` sends `x` to `(b · x) a`, in the form that rewrites —
Mathlib's own `Matrix.vecMulVec_mulVec` carries a `MulOpposite` scalar.  Only the
scaling of a dot product is missing. -/

/-- Scaling the right argument of a dot product scales the value. -/
theorem dotProduct_smul_right (s : ℝ) (v w : Fin k → ℝ) :
    v ⬝ᵥ (s • w) = s * (v ⬝ᵥ w) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ## 2. A unit kernel vector makes the matrix singular

`Gtz.ne_zero_of_dotProduct_self_eq_one` (Gtz/Wave/FlatPairWeakSeed.lean) supplies
that a unit vector is nonzero. -/

/-- **A KERNEL VECTOR KILLS THE DETERMINANT.**  Over a field a matrix with a
nonzero kernel vector is singular. -/
theorem det_eq_zero_of_mulVec_eq_zero {G : Matrix (Fin k) (Fin k) ℝ}
    {w : Fin k → ℝ} (hnull : G *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1) :
    G.det = 0 :=
  (Matrix.exists_mulVec_eq_zero_iff).mp ⟨w, ne_zero_of_dotProduct_self_eq_one hunit, hnull⟩

/-! ## 3. The adjugate of a singular matrix lands in the kernel -/

/-- **THE ADJUGATE ANNIHILATES.**  With the determinant zero the product with
the adjugate vanishes. -/
theorem mul_adjugate_eq_zero_of_unit_null {G : Matrix (Fin k) (Fin k) ℝ}
    {w : Fin k → ℝ} (hnull : G *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1) :
    G * G.adjugate = 0 := by
  rw [Matrix.mul_adjugate, det_eq_zero_of_mulVec_eq_zero hnull hunit, zero_smul]

/-- **EVERY COLUMN OF THE ADJUGATE IS A KERNEL VECTOR.** -/
theorem mulVec_adjugate_mulVec_eq_zero {G : Matrix (Fin k) (Fin k) ℝ}
    {w : Fin k → ℝ} (hnull : G *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1) (x : Fin k → ℝ) :
    G *ᵥ (G.adjugate *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, mul_adjugate_eq_zero_of_unit_null hnull hunit,
    Matrix.zero_mulVec]

/-- The adjugate of a symmetric matrix is symmetric. -/
theorem adjugate_transpose_eq_of_symm {G : Matrix (Fin k) (Fin k) ℝ}
    (hsym : Gᵀ = G) : (G.adjugate)ᵀ = G.adjugate := by
  rw [Matrix.adjugate_transpose, hsym]

/-! ## 4. The corank-one hypothesis, and the law -/

/-- The kernel of `G` is the line spanned by `w`.  This is the corank-one
hypothesis, written without any rank vocabulary. -/
def KernelIsLine (G : Matrix (Fin k) (Fin k) ℝ) (w : Fin k → ℝ) : Prop :=
  ∀ v : Fin k → ℝ, G *ᵥ v = 0 → ∃ c : ℝ, v = c • w

/-- **THE ADJUGATE IS A RANK-ONE MATRIX ALONG THE KERNEL.**  Under corank one
every column of the adjugate is a multiple of `w`, so the adjugate is `w cᵀ`. -/
theorem exists_adjugate_eq_vecMulVec {G : Matrix (Fin k) (Fin k) ℝ}
    {w : Fin k → ℝ} (hnull : G *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1)
    (hline : KernelIsLine G w) :
    ∃ c : Fin k → ℝ, G.adjugate = Matrix.vecMulVec w c := by
  classical
  have hcol : ∀ j : Fin k, ∃ s : ℝ, (fun i => G.adjugate i j) = s • w := by
    intro j
    refine hline _ ?_
    have h := mulVec_adjugate_mulVec_eq_zero hnull hunit (Pi.single j 1)
    have hcolumn : G.adjugate *ᵥ (Pi.single j (1 : ℝ)) = fun i => G.adjugate i j := by
      funext i
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rwa [hcolumn] at h
  choose s hs using hcol
  refine ⟨s, ?_⟩
  ext i j
  have hij := congrFun (hs j) i
  rw [Matrix.vecMulVec_apply]
  simp only [Pi.smul_apply, smul_eq_mul] at hij
  rw [hij, mul_comm]

/-- **THE CORANK-ONE ADJUGATE LAW, AT EVERY RANK.**  A symmetric matrix with a
unit kernel vector spanning its kernel has adjugate equal to the total of its
principal minors of order `k - 1` times the projector onto that kernel.

At rank three this is the entrywise content of the campaign's
`Gtz.pairGapMinor_eq_pairMinorTotal_mul_reading_first`, proved there by nine
explicit certificates. -/
theorem adjugate_eq_trace_smul_vecMulVec {G : Matrix (Fin k) (Fin k) ℝ}
    (hsym : Gᵀ = G) {w : Fin k → ℝ} (hnull : G *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1)
    (hline : KernelIsLine G w) :
    G.adjugate = Matrix.trace G.adjugate • Matrix.vecMulVec w w := by
  classical
  obtain ⟨c, hc⟩ := exists_adjugate_eq_vecMulVec hnull hunit hline
  -- symmetry of the adjugate makes the two rank-one writings agree entrywise
  have hsymadj : (G.adjugate)ᵀ = G.adjugate := adjugate_transpose_eq_of_symm hsym
  have hentry : ∀ i j : Fin k, c i * w j = w i * c j := by
    intro i j
    have h := congrFun (congrFun hsymadj i) j
    rw [Matrix.transpose_apply, hc, Matrix.vecMulVec_apply, Matrix.vecMulVec_apply] at h
    linarith [h]
  -- pairing that against `w` and using `|w| = 1` pins `c` to a multiple of `w`
  have hc_eq : ∀ i : Fin k, c i = (c ⬝ᵥ w) * w i := by
    intro i
    have hstep : ∀ j : Fin k, c i * (w j * w j) = w i * (c j * w j) := by
      intro j
      linear_combination (w j) * hentry i j
    have hsum : c i * (w ⬝ᵥ w) = w i * (c ⬝ᵥ w) := by
      calc c i * (w ⬝ᵥ w) = ∑ j, c i * (w j * w j) := by
            rw [dotProduct, Finset.mul_sum]
        _ = ∑ j, w i * (c j * w j) := Finset.sum_congr rfl fun j _ => hstep j
        _ = w i * (c ⬝ᵥ w) := by rw [dotProduct, Finset.mul_sum]
    rw [hunit, mul_one] at hsum
    rw [hsum, mul_comm]
  have htrace : Matrix.trace G.adjugate = c ⬝ᵥ w := by
    rw [hc, Matrix.trace_vecMulVec]
    exact dotProduct_comm w c
  ext i j
  rw [htrace, hc, Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, hc_eq j]
  ring

/-! ## 5. The reading form, and the four-set law at every rank -/

/-- **THE ADJUGATE READS EVERY PROBE THROUGH THE KERNEL.**  The quadratic form
of the adjugate is the minor total times the squared reading against `w`. -/
theorem adjugate_quadForm_eq {G : Matrix (Fin k) (Fin k) ℝ}
    (hsym : Gᵀ = G) {w : Fin k → ℝ} (hnull : G *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1)
    (hline : KernelIsLine G w) (v : Fin k → ℝ) :
    v ⬝ᵥ (G.adjugate *ᵥ v) = Matrix.trace G.adjugate * (v ⬝ᵥ w) ^ 2 := by
  have hlaw := adjugate_eq_trace_smul_vecMulVec hsym hnull hunit hline
  have htr : Matrix.trace (Matrix.trace G.adjugate • Matrix.vecMulVec w w)
      = Matrix.trace G.adjugate := by
    rw [Matrix.trace_smul, Matrix.trace_vecMulVec, hunit, smul_eq_mul, mul_one]
  calc v ⬝ᵥ (G.adjugate *ᵥ v)
      = v ⬝ᵥ ((Matrix.trace G.adjugate • Matrix.vecMulVec w w) *ᵥ v) := by rw [← hlaw]
    _ = Matrix.trace G.adjugate * (v ⬝ᵥ w) ^ 2 := by
        rw [Matrix.smul_mulVec, vecMulVec_mulVec_eq, smul_smul,
          dotProduct_smul_right, dotProduct_comm w v]
        ring

/-- **THE FOUR-SET LAW AT EVERY RANK.**  Adjoining one rank-one atom to a
corank-one gap produces a determinant that factors as the minor total times the
squared reading of the atom against the kernel.  The matrix determinant lemma in
its singular form is supplied as `hdetlaw`; at rank three the campaign carries it
unconditionally as `Gtz.det_add_atomMatrix_fin_three`. -/
theorem det_add_atomMatrix_of_kernelIsLine {G : Matrix (Fin k) (Fin k) ℝ}
    (hsym : Gᵀ = G) {w : Fin k → ℝ} (hnull : G *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1)
    (hline : KernelIsLine G w) (v : Fin k → ℝ)
    (hdetlaw : (G + atomMatrix v).det = G.det + v ⬝ᵥ (G.adjugate *ᵥ v)) :
    (G + atomMatrix v).det = Matrix.trace G.adjugate * (v ⬝ᵥ w) ^ 2 := by
  rw [hdetlaw, det_eq_zero_of_mulVec_eq_zero hnull hunit, zero_add,
    adjugate_quadForm_eq hsym hnull hunit hline]

/-- **A BLIND ATOM CANNOT LIFT THE GAP.**  If the adjoined atom reads the kernel
at zero, the enlarged gap is still singular — at every rank, with no corank
hypothesis and no determinant lemma. -/
theorem det_add_atomMatrix_eq_zero_of_blind {G : Matrix (Fin k) (Fin k) ℝ}
    {w : Fin k → ℝ} (hnull : G *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1) {v : Fin k → ℝ}
    (hblind : v ⬝ᵥ w = 0) :
    (G + atomMatrix v).det = 0 := by
  refine (Matrix.exists_mulVec_eq_zero_iff).mp
    ⟨w, ne_zero_of_dotProduct_self_eq_one hunit, ?_⟩
  have hatom : atomMatrix v *ᵥ w = 0 := by
    rw [atomMatrix, vecMulVec_mulVec_eq, hblind, zero_smul]
  rw [Matrix.add_mulVec, hnull, hatom, add_zero]

/-- **THE KERNEL SURVIVES A BLIND ATOM.**  The same computation as a vector
statement: the enlarged gap still kills `w`. -/
theorem add_atomMatrix_mulVec_eq_zero_of_blind {G : Matrix (Fin k) (Fin k) ℝ}
    {w : Fin k → ℝ} (hnull : G *ᵥ w = 0) {v : Fin k → ℝ} (hblind : v ⬝ᵥ w = 0) :
    (G + atomMatrix v) *ᵥ w = 0 := by
  have hatom : atomMatrix v *ᵥ w = 0 := by
    rw [atomMatrix, vecMulVec_mulVec_eq, hblind, zero_smul]
  rw [Matrix.add_mulVec, hnull, hatom, add_zero]

end Gtz

/-
# The Naimark dual of a weighted design, and what it does to a triple

A weighted design of size `m` and rank `k` is `m` vectors `g_c` with weights
`t_c > 0`, `Σ t_c = 1`, `Σ t_c g_c g_cᵀ = 1`.  Put `A c i = √(t_c) · g_c i`.
Then `Aᵀ A = 1`, so `A` has orthonormal columns and its `m × m` column space is a
`k`-plane in `ℝ^m`.  The orthogonal complement of that plane is an `(m-k)`-plane,
and any isometry `Λ` onto it satisfies `Λ Λᵀ = 1 - A Aᵀ`.  Dividing the rows of
`Λ` by `√(t_c)` again gives vectors `Λ̃_c ∈ ℝ^{m-k}` that carry the SAME weights
and resolve the identity of `ℝ^{m-k}`.  That is the Naimark dual design.

This module builds the dual without one square root, proves the single identity
everything else follows from, and reads it on a `k`-selection.

## The master identity

`Gtz.naimark_gram_identity`:

  **`t_d · (g_c ⬝ᵥ g_d + Λ̃_c ⬝ᵥ Λ̃_d) = δ_{cd}`.**

Two matrices carry the design: `Φ = [G | Λ̃]` of shape `m × (k ⊕ r)` and
`Ψ = Φᵀ · diag t`.  Parseval, the dependency law and the dual Parseval law say
exactly `Ψ Φ = 1`, block by block.  A square matrix over a commutative ring has a
two-sided inverse as soon as it has a one-sided one, so `Φ Ψ = 1`, and that is
the identity above.  No square root and no rank argument appear.

Three laws drop out at once:

  * `Gtz.naimark_dot_eq_neg` — off the diagonal the dual Gram is the NEGATED
    Gram, `Λ̃_c ⬝ᵥ Λ̃_d = -(g_c ⬝ᵥ g_d)`.  Every cross norm is preserved and every
    3-cycle product changes sign.
  * `Gtz.naimark_leverage_add` — on the diagonal, `t_c(ℓ_c + ℓ̃_c) = 1`.  The dual
    leverage is `1/t_c - ℓ_c`, and the dual co-share `t_c ℓ̃_c` is the original
    co-share `1 - t_c ℓ_c`.
  * `Gtz.NaimarkDual.dual` — the dual carries the ORIGINAL weights, so it is a
    weighted design of size `m` and rank `m - k`, and the construction is an
    involution up to the Gram (`Gtz.naimark_dual_dual_gram`).

## What it says about domination

`Gtz.naimark_dominates_iff_coGram_le`:

  **`C` dominates  ⟺  the dual Gram of `C` is capped by `diag((1-t_c)/t_c)`.**

Domination is a LOWER Loewner bound on the Gram of the selection.  On the dual it
is an UPPER Loewner bound on the Gram of the SAME selection, with an explicit
diagonal cap.  At `(6,3)` the dual of a design is again a `(6,3)` design, so the
conjecture turns into a capping statement about all `(6,3)` designs —
`Gtz.gtzWeighted_six_three_iff_coGram_cap`.

## The determinant law and the bracket law

`Gtz.naimark_gramGap_det` writes the `k × k` gap determinant of a selection as a
scalar times an `(m-k) × (m-k)` determinant built from the dual atoms of the
SAME selection.  At `m = 4, k = 3` the second factor is a scalar and the law is
the landed four-atom mechanism.  At `m = 6, k = 3` it is a `3 × 3` determinant,
whose nonpositivity fixes only the parity of the negative eigenvalue count.

`Gtz.naimark_bracket_law` runs the same computation with the identity replaced by
zero and then spends the dual Parseval law:

  **`(∏_{c ∈ C} t_c) · det Gram_C  =  (∏_{c ∉ C} t_c) · det Gram*_{Cᶜ}`.**

The squared bracket of a `k`-selection is the squared bracket of the
complementary `(m-k)`-selection in the dual, weighted.  No Jacobi complementary
minor identity is needed: the dual Parseval law supplies it.

## The realness equation at six points

At `(6,3)` both sides of the bracket law are `3 × 3`.  Expanding the dual
determinant and substituting the two laws above turns it into an equation for
the Bargmann 3-cycle — `Gtz.sixThree_bargmann_cycle`:

  **`2 p_ab p_ac p_bc = ℓ̃_a ℓ̃_b ℓ̃_c - ℓ̃_a q_bc - ℓ̃_b q_ac - ℓ̃_c q_ab
      - (t_x t_y t_z / t_a t_b t_c) · [x y z]²`**

for the two complementary triples `{a,b,c}` and `{x,y,z}`.  The left side is the
one genuinely real-only quantity in the vocabulary and the right side is built
from squares, leverages and weights.  Squaring gives
`Gtz.sixThree_bargmann_realness`, an equation whose right side is `4 q q q`.

[MEASURED before proving.  The master identity, the dual Parseval law, the
dependency law, the leverage law and the determinant law were checked at
`(6,3)`, `(5,3)`, `(4,3)`, `(7,3)`, `(6,4)`, `(8,3)`, `(7,4)` with residuals at
most `1.3e-12`, and the Loewner cap agreed with domination on EVERY selection of
every design with zero mismatches.  The bracket law and the cycle equation were
checked at `(6,3)` to `2.3e-14` and `6.5e-11`.  At the named fixtures — regular
tetrahedron, `K4` at six, icosahedron, coordinate diagonal, split tetrahedron —
every residual is at most `7e-13` and the cap reproduces the domination count
exactly (4/4, 4/20, 10/20, 1/20, 12/20).  FIELD: over `ℂ` the master identity
and the cycle equation still hold, but the squared form
`(…)² = 4 q_ab q_ac q_bc` fails, with slack `4qqq - (…)²` between `1.4e-9` and
`1.2e4` over 8000 complex triples.  The realness statement is real-only.]
-/
import Gtz.LinAlg.ProjectionForm
import Gtz.LinAlg.PsdKit
import Gtz.Design.TripleGramSylvester
import Gtz.Design.LeverageBound
import Gtz.Core.Sanity

namespace Gtz

open Matrix Finset

variable {m k r : ℕ}

/-! ## 1. The dual frame -/

/-- A **Naimark dual frame** for a design: `m` vectors in `ℝ^r` with `k + r = m`
that are orthogonal to the design in the weighted pairing and resolve the
identity of `ℝ^r` against the SAME weights. -/
structure NaimarkDual (D : WeightedDesign m k) (r : ℕ) where
  /-- The dual atom at each index. -/
  co : Fin m → (Fin r → ℝ)
  /-- The two ranks fill the size. -/
  rankAdd : k + r = m
  /-- The dual atoms are weighted-orthogonal to the design. -/
  dependency : ∀ i : Fin k, ∀ j : Fin r,
    ∑ c, D.weight c * D.atom c i * co c j = 0
  /-- The dual atoms resolve the identity of `ℝ^r` against the design weights. -/
  coParseval : ∑ c, D.weight c • atomMatrix (co c) = 1

variable {D : WeightedDesign m k}

/-- The `m × (k ⊕ r)` frame that carries the design and its dual side by side. -/
def naimarkFrame (D : WeightedDesign m k) (N : NaimarkDual D r) :
    Matrix (Fin m) (Fin k ⊕ Fin r) ℝ :=
  Matrix.fromCols (Matrix.of fun c i => D.atom c i) (Matrix.of fun c j => N.co c j)

/-- The weighted transpose of the frame. -/
def naimarkCoframe (D : WeightedDesign m k) (N : NaimarkDual D r) :
    Matrix (Fin k ⊕ Fin r) (Fin m) ℝ :=
  Matrix.fromRows (Matrix.of fun i c => D.weight c * D.atom c i)
    (Matrix.of fun j c => D.weight c * N.co c j)

/-- Parseval, read as a matrix product of the design against its weighted
transpose. -/
theorem naimark_parseval_block (N : NaimarkDual D r) :
    (Matrix.of fun i c => D.weight c * D.atom c i) * (Matrix.of fun c i => D.atom c i)
      = (1 : Matrix (Fin k) (Fin k) ℝ) := by
  ext i j
  have h : (∑ c, D.weight c • atomMatrix (D.atom c)) i j
      = (1 : Matrix (Fin k) (Fin k) ℝ) i j := by rw [D.isParseval]
  simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
    smul_eq_mul] at h
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [← h]
  refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ) fun c _ => ?_
  ring

/-- The dual Parseval law, read as a matrix product. -/
theorem naimark_coParseval_block (N : NaimarkDual D r) :
    (Matrix.of fun j c => D.weight c * N.co c j) * (Matrix.of fun c j => N.co c j)
      = (1 : Matrix (Fin r) (Fin r) ℝ) := by
  ext i j
  have h : (∑ c, D.weight c • atomMatrix (N.co c)) i j
      = (1 : Matrix (Fin r) (Fin r) ℝ) i j := by rw [N.coParseval]
  simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
    smul_eq_mul] at h
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [← h]
  refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ) fun c _ => ?_
  ring

/-- The dependency law, read as a matrix product. -/
theorem naimark_dependency_block (N : NaimarkDual D r) :
    (Matrix.of fun i c => D.weight c * D.atom c i) * (Matrix.of fun c j => N.co c j)
      = (0 : Matrix (Fin k) (Fin r) ℝ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  exact N.dependency i j

/-- The dependency law transposed. -/
theorem naimark_dependency_block' (N : NaimarkDual D r) :
    (Matrix.of fun j c => D.weight c * N.co c j) * (Matrix.of fun c i => D.atom c i)
      = (0 : Matrix (Fin r) (Fin k) ℝ) := by
  ext j i
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  rw [← N.dependency i j]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- **The coframe is a left inverse of the frame.**  The four blocks are exactly
Parseval, the dependency law twice, and the dual Parseval law. -/
theorem naimark_coframe_mul_frame (N : NaimarkDual D r) :
    naimarkCoframe D N * naimarkFrame D N = 1 := by
  rw [naimarkCoframe, naimarkFrame, Matrix.fromRows_mul_fromCols,
    naimark_parseval_block N, naimark_dependency_block N, naimark_dependency_block' N,
    naimark_coParseval_block N, Matrix.fromBlocks_one]

/-- The size equivalence that makes the frame square. -/
def naimarkSizeEquiv (N : NaimarkDual D r) : Fin m ≃ (Fin k ⊕ Fin r) :=
  (finCongr N.rankAdd.symm).trans finSumFinEquiv.symm

/-- **The frame is a two-sided inverse of the coframe.**  A one-sided inverse of
a square matrix over a commutative ring is two-sided, and the frame is square
because `k + r = m`. -/
theorem naimark_frame_mul_coframe (N : NaimarkDual D r) :
    naimarkFrame D N * naimarkCoframe D N = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (naimarkSizeEquiv N)).mpr (naimark_coframe_mul_frame N)

/-- **THE MASTER IDENTITY.**  The Gram of the design and the Gram of its dual add
to the inverse weight on the diagonal and to zero off it.  Everything in this
module is a reading of this one line. -/
theorem naimark_gram_identity (N : NaimarkDual D r) (c d : Fin m) :
    D.weight d * (D.atom c ⬝ᵥ D.atom d + N.co c ⬝ᵥ N.co d) = if c = d then 1 else 0 := by
  have hone := naimark_frame_mul_coframe N
  have hentry : (naimarkFrame D N * naimarkCoframe D N) c d
      = (1 : Matrix (Fin m) (Fin m) ℝ) c d := by rw [hone]
  rw [Matrix.mul_apply, Fintype.sum_sum_type] at hentry
  simp only [naimarkFrame, naimarkCoframe, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
    Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.of_apply,
    Matrix.one_apply] at hentry
  rw [← hentry]
  simp only [dotProduct, mul_add, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

/-- **The off-diagonal law.**  Away from the diagonal the dual Gram is the
negated Gram: every cross norm survives duality and every 3-cycle product
changes sign. -/
theorem naimark_dot_eq_neg (N : NaimarkDual D r) {c d : Fin m} (hcd : c ≠ d) :
    N.co c ⬝ᵥ N.co d = -(D.atom c ⬝ᵥ D.atom d) := by
  have h := naimark_gram_identity N c d
  rw [if_neg hcd] at h
  have hw := (D.weight_pos d).ne'
  have : D.atom c ⬝ᵥ D.atom d + N.co c ⬝ᵥ N.co d = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hw
    · exact h'
  linarith

/-- **The diagonal law.**  The weight times the sum of the two leverages is one,
so the dual leverage is `1/t_c - ℓ_c` and the dual co-share is the original
co-share. -/
theorem naimark_leverage_add (N : NaimarkDual D r) (c : Fin m) :
    D.weight c * (leverageOf (D.atom c) + leverageOf (N.co c)) = 1 := by
  have h := naimark_gram_identity N c c
  rw [if_pos rfl] at h
  rwa [leverageOf_eq_dotProduct, leverageOf_eq_dotProduct]

/-- The dual leverage in closed form. -/
theorem naimark_coLeverage (N : NaimarkDual D r) (c : Fin m) :
    leverageOf (N.co c) = (D.weight c)⁻¹ - leverageOf (D.atom c) := by
  have h := naimark_leverage_add N c
  have hw := (D.weight_pos c).ne'
  field_simp at h ⊢
  linarith [h]

/-- The dual co-share is the original co-share: `t_c ℓ̃_c = 1 - t_c ℓ_c`. -/
theorem naimark_coShare (N : NaimarkDual D r) (c : Fin m) :
    D.weight c * leverageOf (N.co c) = 1 - D.weight c * leverageOf (D.atom c) := by
  have h := naimark_leverage_add N c
  nlinarith [h]

/-! ## 2. The dual design and the involution -/

/-- **The Naimark dual is a weighted design of rank `m - k` carrying the SAME
weights.**  Only the dual Parseval law is needed. -/
def NaimarkDual.dual (N : NaimarkDual D r) : WeightedDesign m r where
  atom := N.co
  weight := D.weight
  weight_pos := D.weight_pos
  weight_sum_one := D.weight_sum_one
  isParseval := N.coParseval

@[simp] theorem NaimarkDual.dual_atom (N : NaimarkDual D r) (c : Fin m) :
    N.dual.atom c = N.co c := rfl

@[simp] theorem NaimarkDual.dual_weight (N : NaimarkDual D r) (c : Fin m) :
    N.dual.weight c = D.weight c := rfl

/-- **Duality is an involution.**  The original design is a Naimark dual frame
for the dual design. -/
def NaimarkDual.flip (N : NaimarkDual D r) : NaimarkDual N.dual k where
  co := D.atom
  rankAdd := by have h := N.rankAdd; omega
  dependency := fun i j => by
    show ∑ c, D.weight c * N.co c i * D.atom c j = 0
    rw [← N.dependency j i]
    exact Finset.sum_congr rfl fun c _ => by ring
  coParseval := D.isParseval

@[simp] theorem NaimarkDual.flip_co (N : NaimarkDual D r) (c : Fin m) :
    N.flip.co c = D.atom c := rfl

/-- **The dual of the dual has the original Gram.**  Domination reads only the
Gram, so duality is an involution for every question this campaign asks. -/
theorem naimark_dual_dual_gram (N : NaimarkDual D r) (c d : Fin m) :
    N.flip.dual.atom c ⬝ᵥ N.flip.dual.atom d = D.atom c ⬝ᵥ D.atom d := rfl

/-! ## 3. The Gram of a selection, primal and dual -/

/-- The Gram matrix of a selection of the design. -/
def naimarkGram (D : WeightedDesign m k) {size : ℕ} (pick : Fin size → Fin m) :
    Matrix (Fin size) (Fin size) ℝ :=
  Matrix.of fun a b => D.atom (pick a) ⬝ᵥ D.atom (pick b)

/-- The Gram matrix of a selection read in the dual. -/
def naimarkCoGram (N : NaimarkDual D r) {size : ℕ} (pick : Fin size → Fin m) :
    Matrix (Fin size) (Fin size) ℝ :=
  Matrix.of fun a b => N.co (pick a) ⬝ᵥ N.co (pick b)

/-- The dual atoms of a selection, as the rows of a `size × r` matrix. -/
def naimarkCoRows (N : NaimarkDual D r) {size : ℕ} (pick : Fin size → Fin m) :
    Matrix (Fin size) (Fin r) ℝ :=
  Matrix.of fun a j => N.co (pick a) j

/-- The dual Gram of a selection is the outer square of its dual rows. -/
theorem naimarkCoGram_eq_mul (N : NaimarkDual D r) {size : ℕ} (pick : Fin size → Fin m) :
    naimarkCoGram N pick = naimarkCoRows N pick * (naimarkCoRows N pick)ᵀ := by
  ext a b
  simp only [naimarkCoGram, naimarkCoRows, Matrix.of_apply, Matrix.mul_apply,
    Matrix.transpose_apply, dotProduct]

/-- The diagonal cap `(1 - t_c)/t_c` of a selection. -/
noncomputable def naimarkCap (D : WeightedDesign m k) {size : ℕ} (pick : Fin size → Fin m) :
    Matrix (Fin size) (Fin size) ℝ :=
  Matrix.diagonal fun a => (D.weight (pick a))⁻¹ - 1

/-- The inverse weight diagonal of a selection. -/
noncomputable def naimarkInvWeight (D : WeightedDesign m k) {size : ℕ} (pick : Fin size → Fin m) :
    Matrix (Fin size) (Fin size) ℝ :=
  Matrix.diagonal fun a => (D.weight (pick a))⁻¹

/-- **THE SELECTION SPLIT.**  On an injective selection the primal Gram and the
dual Gram add to the inverse weight diagonal.  This is the master identity
restricted, and it is the only place injectivity is spent. -/
theorem naimark_gram_add_coGram (N : NaimarkDual D r) {size : ℕ} {pick : Fin size → Fin m}
    (hpick : Function.Injective pick) :
    naimarkGram D pick + naimarkCoGram N pick = naimarkInvWeight D pick := by
  ext a b
  have h := naimark_gram_identity N (pick a) (pick b)
  have hw := (D.weight_pos (pick b)).ne'
  simp only [naimarkGram, naimarkCoGram, naimarkInvWeight, Matrix.add_apply, Matrix.of_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl] at h
    rw [Matrix.diagonal_apply_eq]
    field_simp at h ⊢
    linarith
  · rw [if_neg (fun hcontra : pick a = pick b => hab (hpick hcontra))] at h
    rw [Matrix.diagonal_apply_ne _ hab]
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hw
    · linarith

/-- The Loewner gap of the primal Gram is the cap minus the dual Gram. -/
theorem naimark_gap_eq_cap_sub (N : NaimarkDual D r) {size : ℕ} {pick : Fin size → Fin m}
    (hpick : Function.Injective pick) :
    naimarkGram D pick - 1 = naimarkCap D pick - naimarkCoGram N pick := by
  have h := naimark_gram_add_coGram N hpick
  ext a b
  have hab : (naimarkGram D pick + naimarkCoGram N pick) a b = naimarkInvWeight D pick a b := by
    rw [h]
  rw [Matrix.add_apply] at hab
  rw [Matrix.sub_apply, Matrix.sub_apply, naimarkCap]
  rw [naimarkInvWeight] at hab
  by_cases hx : a = b
  · subst hx
    rw [Matrix.diagonal_apply_eq] at hab
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    linarith
  · rw [Matrix.diagonal_apply_ne _ hx] at hab
    rw [Matrix.diagonal_apply_ne _ hx, Matrix.one_apply_ne hx]
    linarith

/-! ## 4. Domination is a cap on the dual Gram -/

/-- Domination of a `k`-selection is the Loewner gap of its Gram. -/
theorem dominates_iff_naimarkGram (D : WeightedDesign m k) {pick : Fin k → Fin m}
    (hpick : Function.Injective pick) :
    Dominates D (Finset.image pick Finset.univ) ↔ (naimarkGram D pick - 1).PosSemidef := by
  have hg : selectedAtomRows D pick * (selectedAtomRows D pick)ᵀ = naimarkGram D pick := by
    ext a b
    simp only [naimarkGram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      selectedAtomRows, dotProduct]
  rw [Dominates, ← transpose_mul_selectedAtomRows D pick hpick,
    posSemidef_transpose_mul_sub_one_comm (selectedAtomRows D pick), hg]

/-- **DOMINATION IS A CAP ON THE DUAL.**  A `k`-selection dominates exactly when
its DUAL Gram sits below the diagonal `(1 - t_c)/t_c`.  The primal statement is a
LOWER Loewner bound on a Gram against the identity, the dual statement an UPPER
Loewner bound on the Gram of the SAME atoms against an explicit diagonal. -/
theorem naimark_dominates_iff_coGram_le (N : NaimarkDual D r) {pick : Fin k → Fin m}
    (hpick : Function.Injective pick) :
    Dominates D (Finset.image pick Finset.univ)
      ↔ (naimarkCap D pick - naimarkCoGram N pick).PosSemidef := by
  rw [dominates_iff_naimarkGram D hpick, naimark_gap_eq_cap_sub N hpick]

/-! ## 5. The two determinant laws -/

/-- **THE DIAGONAL SPLIT DETERMINANT.**  A positive diagonal minus an outer
square has determinant the product of the diagonal times the determinant of the
`r × r` reading.  This is Sylvester's determinant identity with the diagonal
divided out, and it is the only determinant step in the module. -/
theorem det_diagonal_sub_mul_transpose {size : ℕ} {e : Fin size → ℝ} (he : ∀ a, e a ≠ 0)
    (X : Matrix (Fin size) (Fin r) ℝ) :
    (Matrix.diagonal e - X * Xᵀ).det
      = (∏ a, e a) * (1 - Xᵀ * Matrix.diagonal (fun a => (e a)⁻¹) * X).det := by
  have hd : Matrix.diagonal e * Matrix.diagonal (fun a => (e a)⁻¹)
      = (1 : Matrix (Fin size) (Fin size) ℝ) := by
    rw [Matrix.diagonal_mul_diagonal]
    have : (fun a => e a * (e a)⁻¹) = fun _ : Fin size => (1 : ℝ) :=
      funext fun a => mul_inv_cancel₀ (he a)
    rw [this, Matrix.diagonal_one]
  have hfac : Matrix.diagonal e - X * Xᵀ
      = Matrix.diagonal e * (1 - Matrix.diagonal (fun a => (e a)⁻¹) * (X * Xᵀ)) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hd, Matrix.one_mul]
  rw [hfac, Matrix.det_mul, Matrix.det_diagonal]
  congr 1
  have hcomm := Matrix.det_one_add_mul_comm (-(Matrix.diagonal (fun a => (e a)⁻¹) * X)) Xᵀ
  have hleft : (1 : Matrix (Fin size) (Fin size) ℝ)
      + -(Matrix.diagonal (fun a => (e a)⁻¹) * X) * Xᵀ
      = 1 - Matrix.diagonal (fun a => (e a)⁻¹) * (X * Xᵀ) := by
    rw [Matrix.neg_mul, ← sub_eq_add_neg, Matrix.mul_assoc]
  have hright : (1 : Matrix (Fin r) (Fin r) ℝ)
      + Xᵀ * -(Matrix.diagonal (fun a => (e a)⁻¹) * X)
      = 1 - Xᵀ * Matrix.diagonal (fun a => (e a)⁻¹) * X := by
    rw [Matrix.mul_neg, ← sub_eq_add_neg, Matrix.mul_assoc]
  rw [hleft, hright] at hcomm
  exact hcomm

/-- The `r × r` reading of a selection: the dual atoms weighted by a scalar. -/
theorem naimark_coRows_reading {size : ℕ} (N : NaimarkDual D r) (pick : Fin size → Fin m)
    (scaling : Fin size → ℝ) :
    (naimarkCoRows N pick)ᵀ * Matrix.diagonal scaling * naimarkCoRows N pick
      = ∑ a, scaling a • atomMatrix (N.co (pick a)) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, naimarkCoRows, Matrix.of_apply,
    Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
  refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin size)) = Finset.univ) fun a _ => ?_
  ring

/-- **THE COMPLEMENT DETERMINANT LAW.**  The `k × k` gap determinant of a
selection equals the product of `(1 - t_c)/t_c` over the selection times an
`(m - k) × (m - k)` determinant built from the DUAL atoms of the SAME selection.
At `m = k + 1` the second factor is a scalar and nonpositivity is an order
relation.  At `m = k + 3` it is a `3 × 3` determinant, and nonpositivity fixes
only the parity of the number of negative eigenvalues. -/
theorem naimark_gapDet_law (N : NaimarkDual D r) (hm : 2 ≤ m) {pick : Fin k → Fin m}
    (hpick : Function.Injective pick) :
    (naimarkGram D pick - 1).det
      = (∏ a, ((D.weight (pick a))⁻¹ - 1))
        * (1 - ∑ a, (D.weight (pick a) / (1 - D.weight (pick a)))
              • atomMatrix (N.co (pick a))).det := by
  have hne : ∀ a : Fin k, (D.weight (pick a))⁻¹ - 1 ≠ 0 := by
    intro a
    have hlt := weight_lt_one D hm (pick a)
    have hpos := D.weight_pos (pick a)
    have : 1 < (D.weight (pick a))⁻¹ := by
      rw [lt_inv_comm₀ one_pos hpos]
      simpa using hlt
    linarith
  have hscale : (fun a : Fin k => ((D.weight (pick a))⁻¹ - 1)⁻¹)
      = fun a : Fin k => D.weight (pick a) / (1 - D.weight (pick a)) := by
    funext a
    have hpos := D.weight_pos (pick a)
    have hlt := weight_lt_one D hm (pick a)
    have hw : D.weight (pick a) ≠ 0 := hpos.ne'
    rw [show (D.weight (pick a))⁻¹ - 1 = (1 - D.weight (pick a)) / D.weight (pick a) by
      field_simp]
    rw [inv_div]
  rw [naimark_gap_eq_cap_sub N hpick, naimarkCap, naimarkCoGram_eq_mul,
    det_diagonal_sub_mul_transpose hne (naimarkCoRows N pick), hscale,
    naimark_coRows_reading]

/-- **THE BRACKET LAW.**  The same computation with the identity replaced by
zero, then spending the dual Parseval law across the complementary selection:
the weighted Gram determinant of a `k`-selection is the weighted dual Gram
determinant of the complementary `(m - k)`-selection.  No Jacobi complementary
minor identity is used. -/
theorem naimark_bracket_law (N : NaimarkDual D r) (sel : Fin k → Fin m) (cosel : Fin r → Fin m)
    (hpart : Function.Bijective (Sum.elim sel cosel)) :
    (∏ a, D.weight (sel a)) * (naimarkGram D sel).det
      = (∏ j, D.weight (cosel j)) * (naimarkCoGram N cosel).det := by
  classical
  have hinj := hpart.1
  have hselinj : Function.Injective sel := by
    intro a b hab
    have h : Sum.elim sel cosel (Sum.inl a) = Sum.elim sel cosel (Sum.inl b) := hab
    exact Sum.inl.inj (hinj h)
  have hwne : ∀ a : Fin k, (D.weight (sel a))⁻¹ ≠ 0 :=
    fun a => inv_ne_zero (D.weight_pos (sel a)).ne'
  have hsplit : naimarkGram D sel
      = Matrix.diagonal (fun a => (D.weight (sel a))⁻¹)
        - naimarkCoRows N sel * (naimarkCoRows N sel)ᵀ := by
    have h := naimark_gram_add_coGram N hselinj
    rw [naimarkCoGram_eq_mul, naimarkInvWeight] at h
    rw [← h]
    exact (add_sub_cancel_right _ _).symm
  have hdet1 : (naimarkGram D sel).det
      = (∏ a, (D.weight (sel a))⁻¹)
        * (1 - ∑ a, D.weight (sel a) • atomMatrix (N.co (sel a))).det := by
    rw [hsplit, det_diagonal_sub_mul_transpose hwne (naimarkCoRows N sel)]
    simp only [inv_inv]
    rw [naimark_coRows_reading]
  have hread : (1 : Matrix (Fin r) (Fin r) ℝ)
      - ∑ a, D.weight (sel a) • atomMatrix (N.co (sel a))
      = ∑ j, D.weight (cosel j) • atomMatrix (N.co (cosel j)) := by
    have hall : ∑ s : Fin k ⊕ Fin r,
        D.weight (Sum.elim sel cosel s) • atomMatrix (N.co (Sum.elim sel cosel s)) = 1 := by
      rw [← N.coParseval]
      exact Fintype.sum_equiv (Equiv.ofBijective _ hpart) _ _ fun _ => rfl
    rw [Fintype.sum_sum_type] at hall
    simp only [Sum.elim_inl, Sum.elim_inr] at hall
    rw [← hall]
    abel
  have hdet2 : (∑ j, D.weight (cosel j) • atomMatrix (N.co (cosel j))).det
      = (∏ j, D.weight (cosel j)) * (naimarkCoGram N cosel).det := by
    rw [← naimark_coRows_reading N cosel (fun j => D.weight (cosel j)),
      Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
      naimarkCoGram_eq_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hone : (∏ a, D.weight (sel a)) * (∏ a, (D.weight (sel a))⁻¹) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun a _ => mul_inv_cancel₀ (D.weight_pos (sel a)).ne'
  rw [hdet1, hread, hdet2, ← mul_assoc, hone, one_mul]

/-! ## 6. The three realness readings of duality -/

/-- The dual leverage in closed form, as a function of weight and leverage. -/
noncomputable def coLeverageDual (D : WeightedDesign m k) (c : Fin m) : ℝ :=
  (D.weight c)⁻¹ - leverageOf (D.atom c)

theorem coLeverageDual_eq (N : NaimarkDual D r) (c : Fin m) :
    coLeverageDual D c = leverageOf (N.co c) := (naimark_coLeverage N c).symm

/-- **THE DUAL RANK BUDGET.**  The dual leverages carry total weighted mass
`m - k`, the rank of the dual. -/
theorem naimark_sum_weight_coLeverage (N : NaimarkDual D r) :
    ∑ c, D.weight c * coLeverageDual D c = (m : ℝ) - k := by
  have hshare : ∀ c : Fin m, D.weight c * coLeverageDual D c
      = 1 - D.weight c * leverageOf (D.atom c) := by
    intro c
    rw [coLeverageDual_eq N]
    exact naimark_coShare N c
  rw [Finset.sum_congr rfl fun c _ => hshare c, Finset.sum_sub_distrib,
    sum_weight_mul_leverage D]
  simp

/-- **THE CROSS NORM IS A DUALITY INVARIANT.**  Every squared pair reading is
unchanged by the Naimark dual. -/
theorem naimark_crossNormSq_invariant (N : NaimarkDual D r) {c d : Fin m} (hcd : c ≠ d) :
    (N.co c ⬝ᵥ N.co d) ^ 2 = (D.atom c ⬝ᵥ D.atom d) ^ 2 := by
  rw [naimark_dot_eq_neg N hcd, neg_pow_two]

/-- **THE BARGMANN 3-CYCLE CHANGES SIGN.**  The product around a triangle is the
one quantity in the vocabulary that duality does not preserve: it is negated.
Negating the three off-diagonal entries of a `3 × 3` symmetric matrix is not a
diagonal congruence, because the product of the three sign changes is `-1`. -/
theorem naimark_threeCycle_neg (N : NaimarkDual D r) {a b c : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (N.co a ⬝ᵥ N.co b) * (N.co a ⬝ᵥ N.co c) * (N.co b ⬝ᵥ N.co c)
      = -((D.atom a ⬝ᵥ D.atom b) * (D.atom a ⬝ᵥ D.atom c) * (D.atom b ⬝ᵥ D.atom c)) := by
  rw [naimark_dot_eq_neg N hab, naimark_dot_eq_neg N hac, naimark_dot_eq_neg N hbc]
  ring

/-! ## 7. Rank three at six points: the realness equation -/

/-- The `3 × 3` dual Gram of a triple, expanded in primal data.  The cycle term
enters with the OPPOSITE sign to the primal expansion — that is the whole
content of duality at rank three. -/
theorem naimark_coGram_det_triple (N : NaimarkDual D r) (pick : Fin 3 → Fin m)
    (hpick : Function.Injective pick) :
    (naimarkCoGram N pick).det
      = coLeverageDual D (pick 0) * coLeverageDual D (pick 1) * coLeverageDual D (pick 2)
        - coLeverageDual D (pick 0) * (D.atom (pick 1) ⬝ᵥ D.atom (pick 2)) ^ 2
        - coLeverageDual D (pick 1) * (D.atom (pick 0) ⬝ᵥ D.atom (pick 2)) ^ 2
        - coLeverageDual D (pick 2) * (D.atom (pick 0) ⬝ᵥ D.atom (pick 1)) ^ 2
        - 2 * (D.atom (pick 0) ⬝ᵥ D.atom (pick 1)) * (D.atom (pick 0) ⬝ᵥ D.atom (pick 2))
            * (D.atom (pick 1) ⬝ᵥ D.atom (pick 2)) := by
  have h01 : pick 0 ≠ pick 1 := fun h => by simpa using hpick h
  have h02 : pick 0 ≠ pick 2 := fun h => by simpa using hpick h
  have h12 : pick 1 ≠ pick 2 := fun h => by simpa using hpick h
  rw [Matrix.det_fin_three]
  simp only [naimarkCoGram, Matrix.of_apply]
  rw [coLeverageDual_eq N, coLeverageDual_eq N, coLeverageDual_eq N]
  rw [leverageOf_eq_dotProduct, leverageOf_eq_dotProduct, leverageOf_eq_dotProduct]
  rw [naimark_dot_eq_neg N h01, naimark_dot_eq_neg N h02, naimark_dot_eq_neg N h12,
    naimark_dot_eq_neg N h01.symm, naimark_dot_eq_neg N h02.symm, naimark_dot_eq_neg N h12.symm]
  rw [dotProduct_comm (D.atom (pick 1)) (D.atom (pick 0)),
    dotProduct_comm (D.atom (pick 2)) (D.atom (pick 0)),
    dotProduct_comm (D.atom (pick 2)) (D.atom (pick 1))]
  ring

/-- **THE BARGMANN 3-CYCLE EQUATION AT SIX POINTS.**  On a `(6,3)` design the
product around a triangle is pinned by the leverages and weights of that
triangle together with the squared bracket of the COMPLEMENTARY triangle.  The
left side is the campaign's realness carrier and the right side is built only
from squares, leverages and weights. -/
theorem sixThree_bargmann_cycle (D : WeightedDesign 6 3) (N : NaimarkDual D 3)
    (sel cosel : Fin 3 → Fin 6) (hpart : Function.Bijective (Sum.elim sel cosel)) :
    2 * (D.atom (cosel 0) ⬝ᵥ D.atom (cosel 1)) * (D.atom (cosel 0) ⬝ᵥ D.atom (cosel 2))
        * (D.atom (cosel 1) ⬝ᵥ D.atom (cosel 2)) * (∏ j, D.weight (cosel j))
      = (∏ j, D.weight (cosel j))
          * (coLeverageDual D (cosel 0) * coLeverageDual D (cosel 1) * coLeverageDual D (cosel 2)
             - coLeverageDual D (cosel 0) * (D.atom (cosel 1) ⬝ᵥ D.atom (cosel 2)) ^ 2
             - coLeverageDual D (cosel 1) * (D.atom (cosel 0) ⬝ᵥ D.atom (cosel 2)) ^ 2
             - coLeverageDual D (cosel 2) * (D.atom (cosel 0) ⬝ᵥ D.atom (cosel 1)) ^ 2)
        - (∏ a, D.weight (sel a)) * (naimarkGram D sel).det := by
  have hcoinj : Function.Injective cosel := by
    intro a b hab
    have h : Sum.elim sel cosel (Sum.inr a) = Sum.elim sel cosel (Sum.inr b) := hab
    exact Sum.inr.inj (hpart.1 h)
  have hbr := naimark_bracket_law N sel cosel hpart
  rw [naimark_coGram_det_triple N cosel hcoinj] at hbr
  linarith [hbr]

/-- **THE REALNESS EQUATION AT SIX POINTS.**  Squaring the cycle equation removes
the sign and leaves an equation whose right side is four times the product of the
three cross norms.  Over `ℝ` this is an EQUALITY, because the squared cycle
product is the product of the squared readings.  Over `ℂ` the same left side is
`(2 Re c)²` while the right side is `4 |c|²`, so the statement degrades to an
inequality — it is the first realness-consuming equation on a `(6,3)` design. -/
theorem sixThree_bargmann_realness (D : WeightedDesign 6 3) (N : NaimarkDual D 3)
    (sel cosel : Fin 3 → Fin 6) (hpart : Function.Bijective (Sum.elim sel cosel)) :
    ((∏ j, D.weight (cosel j))
        * (coLeverageDual D (cosel 0) * coLeverageDual D (cosel 1) * coLeverageDual D (cosel 2)
           - coLeverageDual D (cosel 0) * (D.atom (cosel 1) ⬝ᵥ D.atom (cosel 2)) ^ 2
           - coLeverageDual D (cosel 1) * (D.atom (cosel 0) ⬝ᵥ D.atom (cosel 2)) ^ 2
           - coLeverageDual D (cosel 2) * (D.atom (cosel 0) ⬝ᵥ D.atom (cosel 1)) ^ 2)
      - (∏ a, D.weight (sel a)) * (naimarkGram D sel).det) ^ 2
      = 4 * (D.atom (cosel 0) ⬝ᵥ D.atom (cosel 1)) ^ 2
          * (D.atom (cosel 0) ⬝ᵥ D.atom (cosel 2)) ^ 2
          * (D.atom (cosel 1) ⬝ᵥ D.atom (cosel 2)) ^ 2
          * (∏ j, D.weight (cosel j)) ^ 2 := by
  have hcyc := sixThree_bargmann_cycle D N sel cosel hpart
  rw [← hcyc]
  ring

end Gtz

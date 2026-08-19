import Gtz.Wave.CornerRefusalCensus
import Gtz.Wave.LightSetFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The outside atoms of a corank-two corner are a frame, and their pivot block is
exactly a rank-one deflation of the identity

At a corank-two corner the complement `Cᶜ` of the dominator carries THREE atoms
in three dimensions.  That coincidence — `6 = 3 + 3` — makes the outside atoms a
BASIS, and a basis obeys two laws that no smaller or larger complement obeys.

## The pivot block is capped by the identity

The cross-block law `Gtz.outside_pivot_compose` says the outside pivot block
`S := P_DD` squares to itself less the spike: `S² = S − lam·η ηᵀ`.  Reading both
sides at a probe and applying Cauchy–Schwarz to `Σ_d x_d (S x)_d` gives
`(xᵀSx)² ≤ (Σ x_d²)·(xᵀSx − lam (η·x)²) ≤ (Σ x_d²)·(xᵀSx)`, hence

  `xᵀ S x ≤ Σ_d x_d²`   (`Gtz.outside_gram_le`),

with no positive definiteness proviso beyond the one the six-set gap always has.
So `1 − P_DD` is positive semidefinite, and every two-by-two minor of it is
NONNEGATIVE (`Gtz.outside_pivot_minor_nonneg`).  Together with the opposite
inequality `Gtz.outside_pivot_minor_nonpos` the minors VANISH
(`Gtz.outside_pivot_minor_eq_zero`).  That repairs
`Gtz.outsidePivot_minor_vanishes'`, whose conclusion is void when the cross mass
`E` vanishes — the degenerate corner where the corner pivot reaches one.

## The frame law

Write `G` for the three outside atoms as the columns of a square matrix.  Then
`S_out = G Gᵀ`, and the adjugate distributes: `adj(G Gᵀ) = adj(Gᵀ) adj(G)`.
Since `Gᵀ adj(Gᵀ) = det(G)·1` and `adj(G) G = det(G)·1`, every weighted outer
product collapses:

  `(Σ_d f_d g_d g_dᵀ)·adj(S_out)·(Σ_d f_d g_d g_dᵀ) = det(S_out)·Σ_d f_d² g_d g_dᵀ`
  (`Gtz.outside_weighted_adj_square`),

and at `f = 1` its polarisation is the LEVERAGE law

  `g_dᵀ adj(S_out) g_{d'} = det(S_out)·[d = d']`   (`Gtz.outside_leverage_adj`).

Both fail the moment the complement stops being a basis: at `(5,3)` the
complement of a triple is a pair, and at `(7,3)` it is four atoms.  The frame law
is the sharpest size marker the campaign has produced — it is an EQUALITY that
holds at `6 = 3 + 3` and at no other size.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The outside pivot block is capped by the identity -/

/-- A sum over the complement whose summand is supported on a pair collapses. -/
theorem sum_compl_of_support_pair {C : Finset (Fin m)} {d d' : Fin m}
    (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) (hne : d ≠ d') (f : Fin m → ℝ)
    (hz : ∀ a ∈ Cᶜ, a ≠ d → a ≠ d' → f a = 0) :
    ∑ a ∈ Cᶜ, f a = f d + f d' := by
  classical
  have hsub : ({d, d'} : Finset (Fin m)) ⊆ Cᶜ := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha'
    · exact hd
    · rw [Finset.mem_singleton] at ha'
      exact ha' ▸ hd'
  rw [← Finset.sum_subset hsub (fun a ha hna => ?_), Finset.sum_pair hne]
  refine hz a ha (fun hc => hna ?_) (fun hc => hna ?_)
  · exact Finset.mem_insert.mpr (Or.inl hc)
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hc)

/-- **The outside pivot block is capped by the identity.**  The cross-block law
makes the block idempotent up to the spike, and Cauchy–Schwarz turns that into a
one-sided cap on every probe. -/
theorem outside_gram_le (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (x : Fin m → ℝ) :
    ∑ a ∈ Cᶜ, x a * ∑ b ∈ Cᶜ, x b * sixSetPivot D a b ≤ ∑ a ∈ Cᶜ, x a ^ 2 := by
  classical
  set y : Fin m → ℝ := fun a => ∑ b ∈ Cᶜ, x b * sixSetPivot D a b with hy
  set Q : ℝ := ∑ a ∈ Cᶜ, x a * y a with hQ
  set E : ℝ := ∑ a ∈ Cᶜ, x a * gapCross D u a with hE
  have hcompose : ∀ b b' : Fin m,
      ∑ a ∈ Cᶜ, sixSetPivot D a b * sixSetPivot D a b'
        = sixSetPivot D b b' - lam * (gapCross D u b * gapCross D u b') := by
    intro b b'
    rw [← outside_pivot_compose D C hgap hPD b b']
    exact Finset.sum_congr rfl fun a _ => by rw [sixSetPivot_comm D a b]
  have hQform : Q = ∑ b ∈ Cᶜ, ∑ b' ∈ Cᶜ, (x b * x b') * sixSetPivot D b b' := by
    rw [hQ, hy]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b' _ => by rw [sixSetPivot_comm D b b']; ring
  have hyy : ∑ a ∈ Cᶜ, y a ^ 2 = Q - lam * E ^ 2 := by
    have hexp : ∀ a : Fin m, y a ^ 2
        = ∑ b ∈ Cᶜ, ∑ b' ∈ Cᶜ,
            (x b * x b') * (sixSetPivot D a b * sixSetPivot D a b') := by
      intro a
      rw [hy, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring
    calc ∑ a ∈ Cᶜ, y a ^ 2
        = ∑ a ∈ Cᶜ, ∑ b ∈ Cᶜ, ∑ b' ∈ Cᶜ,
            (x b * x b') * (sixSetPivot D a b * sixSetPivot D a b') :=
          Finset.sum_congr rfl fun a _ => hexp a
      _ = ∑ b ∈ Cᶜ, ∑ b' ∈ Cᶜ, (x b * x b')
            * ∑ a ∈ Cᶜ, sixSetPivot D a b * sixSetPivot D a b' := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b' _ => by rw [Finset.mul_sum]
      _ = ∑ b ∈ Cᶜ, ∑ b' ∈ Cᶜ, ((x b * x b') * sixSetPivot D b b'
            - lam * ((x b * gapCross D u b) * (x b' * gapCross D u b'))) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by
            rw [hcompose b b']; ring
      _ = Q - lam * E ^ 2 := by
          rw [hQform, hE, sq, Finset.sum_mul_sum, Finset.mul_sum,
            ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hcs : Q ^ 2 ≤ (∑ a ∈ Cᶜ, x a ^ 2) * ∑ a ∈ Cᶜ, y a ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Cᶜ _ _
  have hxx : 0 ≤ ∑ a ∈ Cᶜ, x a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  rw [hyy] at hcs
  nlinarith [hcs, hxx, mul_nonneg hlam (sq_nonneg E),
    mul_nonneg hxx (mul_nonneg hlam (sq_nonneg E))]

/-! ## 2. The two-by-two minors of the outside co-pivot block -/

/-- **The outside co-pivot block is positive semidefinite on every pair.** -/
theorem outside_gram_pair_le (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef)
    {d d' : Fin m} (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) (hne : d ≠ d') (s t : ℝ) :
    s ^ 2 * sixSetPivot D d d + 2 * (s * t * sixSetPivot D d d')
        + t ^ 2 * sixSetPivot D d' d'
      ≤ s ^ 2 + t ^ 2 := by
  classical
  set x : Fin m → ℝ := fun a => if a = d then s else if a = d' then t else 0 with hx
  have hxd : x d = s := by rw [hx]; simp
  have hxd' : x d' = t := by rw [hx]; simp [Ne.symm hne]
  have hxz : ∀ a : Fin m, a ≠ d → a ≠ d' → x a = 0 := by
    intro a h1 h2
    rw [hx]
    simp [h1, h2]
  have hinner : ∀ a : Fin m, ∑ b ∈ Cᶜ, x b * sixSetPivot D a b
      = s * sixSetPivot D a d + t * sixSetPivot D a d' := by
    intro a
    rw [sum_compl_of_support_pair hd hd' hne _
      (fun b _ h1 h2 => by rw [hxz b h1 h2]; ring), hxd, hxd']
  have hmain := outside_gram_le D C hlam hgap hPD x
  simp only [hinner] at hmain
  rw [sum_compl_of_support_pair hd hd' hne _
      (fun a _ h1 h2 => by rw [hxz a h1 h2]; ring),
    sum_compl_of_support_pair hd hd' hne _
      (fun a _ h1 h2 => by rw [hxz a h1 h2]; ring),
    hxd, hxd', sixSetPivot_comm D d' d] at hmain
  nlinarith [hmain]

/-- **The two-by-two minors of `1 − P_DD` are nonnegative.**  The one-sided cap
is a positive semidefiniteness statement, and a positive semidefinite two-by-two
block has a nonnegative determinant. -/
theorem outside_pivot_minor_nonneg (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (C : Finset (Fin m)) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef)
    {d d' : Fin m} (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) (hne : d ≠ d') :
    sixSetPivot D d d' ^ 2
      ≤ (1 - sixSetPivot D d d) * (1 - sixSetPivot D d' d') := by
  have hAnn : 0 ≤ sixSetPivot D d d := sixSetPivot_self_nonneg D hm hPD d
  have hCnn : 0 ≤ sixSetPivot D d' d' := sixSetPivot_self_nonneg D hm hPD d'
  have hA : 0 ≤ 1 - sixSetPivot D d d := by
    have h := outside_pivot_le_one D C hlam hgap hPD hd
    simp only [show D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom d)
      = sixSetPivot D d d from rfl] at h
    linarith
  have hC : 0 ≤ 1 - sixSetPivot D d' d' := by
    have h := outside_pivot_le_one D C hlam hgap hPD hd'
    simp only [show D.atom d' ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom d')
      = sixSetPivot D d' d' from rfl] at h
    linarith
  have h := outside_gram_pair_le D C hlam hgap hPD hd hd' hne
  -- the pair form reads `A s² − 2 B s t + C t² ≥ 0` with `A, C ∈ [0,1]`
  have hBA : sixSetPivot D d d' ^ 2 ≤ 1 - sixSetPivot D d d := by
    nlinarith [h 1 (sixSetPivot D d d'), hCnn]
  have hkey : 0 ≤ (1 - sixSetPivot D d d)
      * ((1 - sixSetPivot D d d) * (1 - sixSetPivot D d' d')
        - sixSetPivot D d d' ^ 2) := by
    nlinarith [h (sixSetPivot D d d') (1 - sixSetPivot D d d)]
  rcases eq_or_lt_of_le hA with hzero | hpos
  · nlinarith [hBA, hzero]
  · nlinarith [hkey, hpos]

/-! ## 3. The minors vanish, with no proviso -/

/-- **The outside pivot block of a corank-two corner is exactly a rank-one
deflation of the identity.**  Every two-by-two minor of `1 − P_DD` vanishes.  The
landed `Gtz.outsidePivot_minor_vanishes'` carries a factor of the cross mass `E`,
so it is void at the degenerate corner `E = 0`; this statement is unconditional. -/
theorem outside_pivot_minor_eq_zero (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {d d' : Fin 6} (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) (hne : d ≠ d') :
    (1 - sixSetPivot D d d) * (1 - sixSetPivot D d' d') = sixSetPivot D d d' ^ 2 := by
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have hle := outside_pivot_minor_nonpos D C hcard hlam hgap hd hd' hne
  have hge := outside_pivot_minor_nonneg D (by norm_num) C hlam hgap hPD hd hd' hne
  linarith

/-! ## 4. The outside atoms are a frame -/

/-- **The adjugate sandwich of a square frame.**  For a square matrix `G` and any
`Df`, the adjugate of `G Gᵀ` collapses the sandwich: the two halves each pay one
determinant and the middle multiplies out. -/
theorem square_frame_adj (G Df : Matrix (Fin 3) (Fin 3) ℝ) :
    (G * Df * Gᵀ) * (G * Gᵀ).adjugate * (G * Df * Gᵀ)
      = (G * Gᵀ).det • (G * (Df * Df) * Gᵀ) := by
  have hcore : Gᵀ * ((G * Gᵀ).adjugate * G)
      = (G.det * G.det) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [Matrix.adjugate_mul_distrib, Matrix.mul_assoc (Gᵀ).adjugate,
      Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul,
      Matrix.mul_adjugate, Matrix.det_transpose, smul_smul]
  have hdet : (G * Gᵀ).det = G.det * G.det := by
    rw [Matrix.det_mul, Matrix.det_transpose]
  calc (G * Df * Gᵀ) * (G * Gᵀ).adjugate * (G * Df * Gᵀ)
      = (G * Df) * (Gᵀ * ((G * Gᵀ).adjugate * G)) * (Df * Gᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = (G * Df) * ((G.det * G.det) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) * (Df * Gᵀ) := by
        rw [hcore]
    _ = (G.det * G.det) • (G * (Df * Df) * Gᵀ) := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
    _ = (G * Gᵀ).det • (G * (Df * Df) * Gᵀ) := by rw [hdet]

/-- **The columns of a square frame are orthonormal in the adjugate metric.** -/
theorem square_frame_adj_column (G : Matrix (Fin 3) (Fin 3) ℝ) (j l : Fin 3) :
    (fun i => G i j) ⬝ᵥ ((G * Gᵀ).adjugate *ᵥ fun i => G i l)
      = (G * Gᵀ).det * (if j = l then 1 else 0) := by
  have hcore : Gᵀ * ((G * Gᵀ).adjugate * G)
      = (G.det * G.det) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [Matrix.adjugate_mul_distrib, Matrix.mul_assoc (Gᵀ).adjugate,
      Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul,
      Matrix.mul_adjugate, Matrix.det_transpose, smul_smul]
  have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M j l) hcore
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at hentry
  rw [Matrix.det_mul, Matrix.det_transpose]
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum] using hentry

/-! ## 5. The frame laws of the complement triple -/

/-- The three outside atoms as the columns of a square matrix. -/
noncomputable def outsideFrame (D : WeightedDesign m 3) (lbl : Fin 3 → Fin m) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => D.atom (lbl j) i

/-- The frame times a diagonal times its transpose is the weighted atom sum. -/
theorem outsideFrame_diagonal (D : WeightedDesign m 3) (lbl : Fin 3 → Fin m)
    (g : Fin 3 → ℝ) :
    outsideFrame D lbl * Matrix.diagonal g * (outsideFrame D lbl)ᵀ
      = ∑ j : Fin 3, g j • atomMatrix (D.atom (lbl j)) := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, outsideFrame, Matrix.of_apply,
    Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The frame times its transpose is the outside atom sum. -/
theorem outsideFrame_transpose (D : WeightedDesign m 3) (lbl : Fin 3 → Fin m) :
    outsideFrame D lbl * (outsideFrame D lbl)ᵀ
      = ∑ j : Fin 3, atomMatrix (D.atom (lbl j)) := by
  have h := outsideFrame_diagonal D lbl (fun _ => 1)
  rw [Matrix.diagonal_one, Matrix.mul_one] at h
  rw [h]
  exact Finset.sum_congr rfl fun j _ => one_smul _ _

/-- A sum over a three-element complement runs over an explicit enumeration. -/
theorem sum_compl_eq_enum {C : Finset (Fin m)} {d1 d2 d3 : Fin m}
    (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3)
    (hset : (Cᶜ : Finset (Fin m)) = {d1, d2, d3})
    {M : Type*} [AddCommMonoid M] (h : Fin m → M) :
    ∑ d ∈ Cᶜ, h d = ∑ j : Fin 3, h (![d1, d2, d3] j) := by
  classical
  rw [hset, Finset.sum_insert (by simp [h12, h13]),
    Finset.sum_insert (by simp [h23]), Finset.sum_singleton, Fin.sum_univ_three]
  simp [add_assoc]

/-- The enumeration of a three-element complement is injective. -/
theorem enum_injective {d1 d2 d3 : Fin m} (h12 : d1 ≠ d2) (h13 : d1 ≠ d3)
    (h23 : d2 ≠ d3) : Function.Injective (![d1, d2, d3] : Fin 3 → Fin m) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

/-- **The second-moment frame law.**  The outside atoms of a corank-two corner
form a BASIS, so their weighted outer-product sums compose through the adjugate:
`(Σ f_d g_d g_dᵀ)·adj(S_out)·(Σ f_d g_d g_dᵀ) = det(S_out)·Σ f_d² g_d g_dᵀ`.
The identity fails at every other size, because only at `6 = 3 + 3` is the
complement of a dominating triple a basis of the ambient space. -/
theorem outside_weighted_adj_square (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcompl : (Cᶜ : Finset (Fin m)).card = 3) (f : Fin m → ℝ) :
    (∑ d ∈ Cᶜ, f d • atomMatrix (D.atom d)) * (subsetSum D Cᶜ).adjugate
        * ∑ d ∈ Cᶜ, f d • atomMatrix (D.atom d)
      = (subsetSum D Cᶜ).det • ∑ d ∈ Cᶜ, f d ^ 2 • atomMatrix (D.atom d) := by
  classical
  obtain ⟨d1, d2, d3, h12, h13, h23, hset⟩ := Finset.card_eq_three.mp hcompl
  set lbl : Fin 3 → Fin m := ![d1, d2, d3] with hlbl
  set G : Matrix (Fin 3) (Fin 3) ℝ := outsideFrame D lbl with hG
  have hS : subsetSum D Cᶜ = G * Gᵀ := by
    rw [hG, outsideFrame_transpose, subsetSum,
      sum_compl_eq_enum h12 h13 h23 hset (fun d => atomMatrix (D.atom d))]
  have hf : ∑ d ∈ Cᶜ, f d • atomMatrix (D.atom d)
      = G * Matrix.diagonal (fun j => f (lbl j)) * Gᵀ := by
    rw [hG, outsideFrame_diagonal,
      sum_compl_eq_enum h12 h13 h23 hset (fun d => f d • atomMatrix (D.atom d))]
  have hf2 : ∑ d ∈ Cᶜ, f d ^ 2 • atomMatrix (D.atom d)
      = G * (Matrix.diagonal (fun j => f (lbl j))
          * Matrix.diagonal (fun j => f (lbl j))) * Gᵀ := by
    rw [Matrix.diagonal_mul_diagonal, hG, outsideFrame_diagonal,
      sum_compl_eq_enum h12 h13 h23 hset (fun d => f d ^ 2 • atomMatrix (D.atom d))]
    exact Finset.sum_congr rfl fun j _ => by rw [sq]
  rw [hS, hf, hf2]
  exact square_frame_adj G _

/-- **The leverage law of the complement triple.**  Every outside atom reads its
own adjugate metric at the determinant, and reads every other outside atom at
zero: `g_dᵀ adj(S_out) g_{d'} = det(S_out)·[d = d']`. -/
theorem outside_leverage_adj (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcompl : (Cᶜ : Finset (Fin m)).card = 3) {d d' : Fin m}
    (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) :
    D.atom d ⬝ᵥ ((subsetSum D Cᶜ).adjugate *ᵥ D.atom d')
      = (subsetSum D Cᶜ).det * (if d = d' then 1 else 0) := by
  classical
  obtain ⟨d1, d2, d3, h12, h13, h23, hset⟩ := Finset.card_eq_three.mp hcompl
  set lbl : Fin 3 → Fin m := ![d1, d2, d3] with hlbl
  set G : Matrix (Fin 3) (Fin 3) ℝ := outsideFrame D lbl with hG
  have hS : subsetSum D Cᶜ = G * Gᵀ := by
    rw [hG, outsideFrame_transpose, subsetSum,
      sum_compl_eq_enum h12 h13 h23 hset (fun c => atomMatrix (D.atom c))]
  have hmem : ∀ c : Fin m, c ∈ Cᶜ → ∃ j : Fin 3, lbl j = c := by
    intro c hc
    rw [hset] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  obtain ⟨j, hj⟩ := hmem d hd
  obtain ⟨l, hl⟩ := hmem d' hd'
  have hcol : ∀ n : Fin 3, (fun i => G i n) = D.atom (lbl n) := fun n => rfl
  rw [← hj, ← hl, ← hcol j, ← hcol l, hS]
  rw [square_frame_adj_column G j l]
  congr 1
  by_cases hjl : j = l
  · simp [hjl]
  · rw [if_neg hjl, if_neg (fun hc => hjl (enum_injective h12 h13 h23 hc))]

end Gtz

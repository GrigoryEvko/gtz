import Gtz.Wave.SharedPrivateStrataDispatch
import Gtz.Wave.SharedPrivateKernelResidue
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The shared-private kernel Gram — the split laws and the trace floor

The strata dispatch left three residues.  The two diagonal residues
read a symmetric idempotent `S` through six supported vectors, and the
kill must consume the commutation layer.  This module builds the
kernel-side calculus that carries those kills.

The split.  Each read vector `z` divides along `S`: the fixed part
`S z` and the kernel part `z - S z`.  The read value prices the two
energies: the fixed part carries `d` times the energy of `z`, and the
kernel part carries `1 - d` times that energy.  For two read vectors
with disjoint carriers, the kernel cross product equals the negative
fixed cross product, and the Cauchy-Schwarz bound caps it.

The trace floor.  A family of vectors fixed by a symmetric idempotent
with a kernel-free Gram counts below the trace.  The proof builds the
span projector from the Gram inverse and reads the trace of the
difference as a sum of squares.  Thus a kernel-free family of kernel
parts caps at the complement trace `basisCount - trace M`.

The composition.  At a diagonal Gram core, a family of atoms with
pairwise disjoint support carriers has a kernel-free kernel Gram,
because the shifted weights sum below one.  One atom more than the
complement trace kills the datum.  The pin atom is disjoint from every
atom off the pinned support, thus the family always starts with two
members.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.read_fixed_energy`, `Gtz.read_fixed_self_energy`,
  `Gtz.kernel_part_energy` — the split energies.
* `Gtz.kernel_cross_law`, `Gtz.disjoint_support_dot` — the cross laws.
* `Gtz.gram_kernel_free_of_bounded_cross` — **THE GRAM BOUND.**
* `Gtz.trace_floor_of_fixed_family` — **THE TRACE FLOOR.**
* `Gtz.exists_gram_kernel_of_trace_lt` — the kernel extraction.
* `Gtz.SharedPrivateData.basisCount_le_six` — the basis cap.
* `Gtz.SharedPrivateData.support_eq_block` — supports are blocks.
* `Gtz.SharedPrivateData.pin_only_slot`,
  `Gtz.SharedPrivateData.pin_disjoint_of_offSupport` — the pin laws.
* `Gtz.SharedPrivateData.exists_kernel_read_frame` — **THE READ
  FRAME PACKAGE.**
* `Gtz.SharedPrivateData.false_of_disjoint_support_family` — **THE
  DISJOINT-FAMILY KILL.**

## Vacuity

The matrix statements are unconditional.  The datum statements
quantify over shared-private data, and no datum exists if
`Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the split energies and the cross laws -/

/-- **THE FIXED ENERGY.**  A supported read prices the quadratic form:
the energy of a read vector against the idempotent is the read value
times its own energy. -/
theorem read_fixed_energy {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    {car : Finset (Fin n)} {vec : Fin n → ℝ} {readVal : ℝ}
    (hsupp : ∀ slot ∉ car, vec slot = 0)
    (hread : ∀ slot ∈ car, (S *ᵥ vec) slot = readVal * vec slot) :
    vec ⬝ᵥ (S *ᵥ vec) = readVal * (vec ⬝ᵥ vec) := by
  rw [dotProduct, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun slot _ => ?_
  by_cases hmem : slot ∈ car
  · rw [hread slot hmem]
    ring
  · rw [hsupp slot hmem]
    ring

/-- The fixed part carries the read value times the energy. -/
theorem read_fixed_self_energy {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S)
    {car : Finset (Fin n)} {vec : Fin n → ℝ} {readVal : ℝ}
    (hsupp : ∀ slot ∉ car, vec slot = 0)
    (hread : ∀ slot ∈ car, (S *ᵥ vec) slot = readVal * vec slot) :
    (S *ᵥ vec) ⬝ᵥ (S *ᵥ vec) = readVal * (vec ⬝ᵥ vec) := by
  have hswap : vec ⬝ᵥ ((Sᵀ * S) *ᵥ vec) = (S *ᵥ vec) ⬝ᵥ (S *ᵥ vec) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  rw [← hswap, hsymm, hidem]
  exact read_fixed_energy hsupp hread

/-- **THE KERNEL ENERGY.**  The kernel part carries the complementary
read value times the energy. -/
theorem kernel_part_energy {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S)
    {car : Finset (Fin n)} {vec : Fin n → ℝ} {readVal : ℝ}
    (hsupp : ∀ slot ∉ car, vec slot = 0)
    (hread : ∀ slot ∈ car, (S *ᵥ vec) slot = readVal * vec slot) :
    (vec - S *ᵥ vec) ⬝ᵥ (vec - S *ᵥ vec)
      = (1 - readVal) * (vec ⬝ᵥ vec) := by
  have hfix := read_fixed_energy hsupp hread
  have hself := read_fixed_self_energy hsymm hidem hsupp hread
  have hcomm : (S *ᵥ vec) ⬝ᵥ vec = vec ⬝ᵥ (S *ᵥ vec) := dotProduct_comm _ _
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hcomm, hfix, hself]
  ring

/-- **THE CROSS LAW.**  The kernel cross product is the plain cross
product minus the fixed cross product. -/
theorem kernel_cross_law {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (vecOne vecTwo : Fin n → ℝ) :
    (vecOne - S *ᵥ vecOne) ⬝ᵥ (vecTwo - S *ᵥ vecTwo)
      = vecOne ⬝ᵥ vecTwo - (S *ᵥ vecOne) ⬝ᵥ (S *ᵥ vecTwo) := by
  have hSS : (S *ᵥ vecOne) ⬝ᵥ (S *ᵥ vecTwo)
      = vecOne ⬝ᵥ (S *ᵥ vecTwo) := by
    have hswap : vecOne ⬝ᵥ ((Sᵀ * S) *ᵥ vecTwo)
        = (S *ᵥ vecOne) ⬝ᵥ (S *ᵥ vecTwo) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose]
    rw [← hswap, hsymm, hidem]
  have hleft : (S *ᵥ vecOne) ⬝ᵥ vecTwo = vecOne ⬝ᵥ (S *ᵥ vecTwo) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← hsymm,
      Matrix.vecMul_transpose, dotProduct_comm, hsymm]
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hleft, hSS]
  ring

/-- Two vectors with disjoint carriers have a zero dot product. -/
theorem disjoint_support_dot {n : ℕ} {carOne carTwo : Finset (Fin n)}
    {vecOne vecTwo : Fin n → ℝ}
    (hsuppOne : ∀ slot ∉ carOne, vecOne slot = 0)
    (hsuppTwo : ∀ slot ∉ carTwo, vecTwo slot = 0)
    (hdisj : ∀ slot ∈ carOne, slot ∉ carTwo) :
    vecOne ⬝ᵥ vecTwo = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero fun slot _ => ?_
  by_cases hmem : slot ∈ carOne
  · rw [hsuppTwo slot (hdisj slot hmem), mul_zero]
  · rw [hsuppOne slot hmem, zero_mul]

/-! ## Layer 2 — the Gram bound and the trace floor -/

/-- **THE GRAM BOUND.**  A family with diagonal energies `(1 - d) n`,
cross squares below `(d n) (d' n')`, positive scales, and a shifted
sum below one has a kernel-free Gram.  The proof prices the quadratic
form below by `(1 - sum d)` times the scaled square mass through the
Cauchy-Schwarz inequality. -/
theorem gram_kernel_free_of_bounded_cross {m n : ℕ}
    (V : Fin m → Fin n → ℝ) (dcoef ncoef : Fin m → ℝ)
    (hn : ∀ i, 0 < ncoef i) (hd : ∀ i, 0 ≤ dcoef i)
    (hself : ∀ i, V i ⬝ᵥ V i = (1 - dcoef i) * ncoef i)
    (hcross : ∀ i j, i ≠ j →
      (V i ⬝ᵥ V j) ^ 2 ≤ dcoef i * ncoef i * (dcoef j * ncoef j))
    (hsum : ∑ i, dcoef i < 1) :
    ∀ x : Fin m → ℝ,
      (Matrix.of fun i j => V i ⬝ᵥ V j) *ᵥ x = 0 → x = 0 := by
  intro x hx
  classical
  set u : Fin m → ℝ := fun i => |x i| * Real.sqrt (dcoef i * ncoef i)
    with hu
  -- the vanished quadratic form
  have hq : x ⬝ᵥ ((Matrix.of fun i j => V i ⬝ᵥ V j) *ᵥ x) = 0 := by
    rw [hx, dotProduct_zero]
  have hexpand : x ⬝ᵥ ((Matrix.of fun i j => V i ⬝ᵥ V j) *ᵥ x)
      = ∑ i, ∑ j, x i * ((V i ⬝ᵥ V j) * x j) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    have happly : ((Matrix.of fun i j => V i ⬝ᵥ V j) *ᵥ x) i
        = ∑ j, (V i ⬝ᵥ V j) * x j := rfl
    rw [happly, Finset.mul_sum]
  -- the diagonal split of each row
  have hsplit : ∀ i, ∑ j, x i * ((V i ⬝ᵥ V j) * x j)
      = (1 - dcoef i) * ncoef i * (x i * x i)
        + ∑ j ∈ Finset.univ.erase i, x i * ((V i ⬝ᵥ V j) * x j) := by
    intro i
    have hterm : x i * ((V i ⬝ᵥ V i) * x i)
        = (1 - dcoef i) * ncoef i * (x i * x i) := by
      rw [hself i]
      ring
    rw [← Finset.add_sum_erase Finset.univ
      (fun j => x i * ((V i ⬝ᵥ V j) * x j)) (Finset.mem_univ i), hterm]
  -- the pair floor from the cross bound
  have hpair : ∀ i : Fin m, ∀ j ∈ Finset.univ.erase i,
      -(u i * u j) ≤ x i * ((V i ⬝ᵥ V j) * x j) := by
    intro i j hj
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hcs := hcross i j (Ne.symm hne)
    have habs : |V i ⬝ᵥ V j|
        ≤ Real.sqrt (dcoef i * ncoef i) * Real.sqrt (dcoef j * ncoef j) := by
      have hsq : |V i ⬝ᵥ V j| = Real.sqrt ((V i ⬝ᵥ V j) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
      rw [hsq, ← Real.sqrt_mul (mul_nonneg (hd i) (hn i).le)]
      exact Real.sqrt_le_sqrt hcs
    have hprod : |x i * ((V i ⬝ᵥ V j) * x j)| ≤ u i * u j := by
      rw [abs_mul, abs_mul]
      have hstep : |x i| * (|V i ⬝ᵥ V j| * |x j|)
          ≤ |x i| * (Real.sqrt (dcoef i * ncoef i)
            * Real.sqrt (dcoef j * ncoef j) * |x j|) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right habs (abs_nonneg _)) (abs_nonneg _)
      calc |x i| * (|V i ⬝ᵥ V j| * |x j|)
          ≤ |x i| * (Real.sqrt (dcoef i * ncoef i)
              * Real.sqrt (dcoef j * ncoef j) * |x j|) := hstep
        _ = u i * u j := by rw [hu]; ring
    linarith [neg_abs_le (x i * ((V i ⬝ᵥ V j) * x j)), hprod,
      abs_nonneg (x i * ((V i ⬝ᵥ V j) * x j))]
  -- the off-diagonal floor, summed
  have hoff : ∑ i, ∑ j ∈ Finset.univ.erase i, (-(u i * u j))
      ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, x i * ((V i ⬝ᵥ V j) * x j) :=
    Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j hj => hpair i j hj
  -- the square of the u-sum splits the same way
  have hsq_u : (∑ i, u i) ^ 2
      = ∑ i, (u i * u i)
        + ∑ i, ∑ j ∈ Finset.univ.erase i, u i * u j := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase Finset.univ (fun j => u i * u j)
      (Finset.mem_univ i)]
  have hu_sq : ∀ i, u i * u i = dcoef i * ncoef i * (x i * x i) := by
    intro i
    have hroot := Real.mul_self_sqrt (mul_nonneg (hd i) (hn i).le)
    calc u i * u i
        = |x i| * |x i| * (Real.sqrt (dcoef i * ncoef i)
            * Real.sqrt (dcoef i * ncoef i)) := by rw [hu]; ring
      _ = x i * x i * (dcoef i * ncoef i) := by
          rw [hroot, abs_mul_abs_self]
      _ = dcoef i * ncoef i * (x i * x i) := by ring
  -- the Cauchy-Schwarz cap on the u-sum
  have hcs2 : (∑ i, u i) ^ 2
      ≤ (∑ i, ncoef i * (x i * x i)) * (∑ i, dcoef i) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => |x i| * Real.sqrt (ncoef i))
      (fun i => Real.sqrt (dcoef i))
    have hfg : ∀ i : Fin m,
        |x i| * Real.sqrt (ncoef i) * Real.sqrt (dcoef i) = u i := by
      intro i
      show |x i| * Real.sqrt (ncoef i) * Real.sqrt (dcoef i)
        = |x i| * Real.sqrt (dcoef i * ncoef i)
      rw [Real.sqrt_mul (hd i)]
      ring
    have hf2 : ∀ i : Fin m,
        (|x i| * Real.sqrt (ncoef i)) ^ 2 = ncoef i * (x i * x i) := by
      intro i
      rw [mul_pow, sq_abs, Real.sq_sqrt (hn i).le]
      ring
    have hg2 : ∀ i : Fin m, Real.sqrt (dcoef i) ^ 2 = dcoef i :=
      fun i => Real.sq_sqrt (hd i)
    calc (∑ i, u i) ^ 2
        = (∑ i, |x i| * Real.sqrt (ncoef i) * Real.sqrt (dcoef i)) ^ 2 := by
          rw [Finset.sum_congr rfl fun i _ => hfg i]
      _ ≤ (∑ i, (|x i| * Real.sqrt (ncoef i)) ^ 2)
            * (∑ i, Real.sqrt (dcoef i) ^ 2) := hcs
      _ = (∑ i, ncoef i * (x i * x i)) * (∑ i, dcoef i) := by
          rw [Finset.sum_congr rfl fun i _ => hf2 i,
            Finset.sum_congr rfl fun i _ => hg2 i]
  -- assemble the main inequality
  have hzero : (0 : ℝ)
      = ∑ i, (1 - dcoef i) * ncoef i * (x i * x i)
        + ∑ i, ∑ j ∈ Finset.univ.erase i, x i * ((V i ⬝ᵥ V j) * x j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_congr rfl fun i _ => hsplit i,
      ← hexpand, hq]
  have hneg_distrib : ∑ i, ∑ j ∈ Finset.univ.erase i, (-(u i * u j))
      = -(∑ i, ∑ j ∈ Finset.univ.erase i, u i * u j) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_neg_distrib]
  have hdiag_split : ∑ i, (1 - dcoef i) * ncoef i * (x i * x i)
      = ∑ i, ncoef i * (x i * x i)
        - ∑ i, dcoef i * ncoef i * (x i * x i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have husum : ∑ i, (u i * u i)
      = ∑ i, dcoef i * ncoef i * (x i * x i) :=
    Finset.sum_congr rfl fun i _ => hu_sq i
  -- the scaled square mass dies
  have hN : ∑ i, ncoef i * (x i * x i) ≤ (∑ i, u i) ^ 2 := by
    have h1 : -(∑ i, ∑ j ∈ Finset.univ.erase i, u i * u j)
        ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, x i * ((V i ⬝ᵥ V j) * x j) := by
      rw [← hneg_distrib]
      exact hoff
    linarith [hzero, h1, hsq_u, husum, hdiag_split]
  have hNnonneg : (0 : ℝ) ≤ ∑ i, ncoef i * (x i * x i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hn i).le (mul_self_nonneg _)
  have hN0 : ∑ i, ncoef i * (x i * x i) = 0 := by
    have hchain : ∑ i, ncoef i * (x i * x i)
        ≤ (∑ i, ncoef i * (x i * x i)) * (∑ i, dcoef i) :=
      le_trans hN hcs2
    nlinarith [hchain, hNnonneg, hsum]
  -- each coordinate dies
  funext i
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    mul_nonneg (hn i).le (mul_self_nonneg (x i))).mp hN0 i
    (Finset.mem_univ i)
  have hxx : x i * x i = 0 := by
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h (hn i).ne'
    · exact h
  show x i = 0
  exact mul_self_eq_zero.mp hxx

/-- **THE TRACE FLOOR.**  A family of vectors fixed by a symmetric
idempotent with a kernel-free Gram counts below the trace.  The span
projector of the family sits inside the idempotent, and the difference
has a nonnegative trace. -/
theorem trace_floor_of_fixed_family {m n : ℕ}
    {Q : Matrix (Fin n) (Fin n) ℝ} (hsymm : Qᵀ = Q) (hidem : Q * Q = Q)
    (V : Fin m → Fin n → ℝ) (hfix : ∀ i, Q *ᵥ V i = V i)
    (hker : ∀ x : Fin m → ℝ,
      (Matrix.of fun i j => V i ⬝ᵥ V j) *ᵥ x = 0 → x = 0) :
    (m : ℝ) ≤ Matrix.trace Q := by
  classical
  set Γ : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.of fun i j => V i ⬝ᵥ V j with hΓ
  set Vmat : Matrix (Fin n) (Fin m) ℝ :=
    Matrix.of fun rowIndex i => V i rowIndex with hVmat
  have hgram : Vmatᵀ * Vmat = Γ := by
    ext i j
    rw [Matrix.mul_apply]
    show ∑ rowIndex, Vmat rowIndex i * Vmat rowIndex j = V i ⬝ᵥ V j
    rw [dotProduct]
    rfl
  -- the Gram is invertible
  have hdet : IsUnit Γ.det := by
    rw [isUnit_iff_ne_zero]
    intro hzero
    obtain ⟨x, hxne, hx0⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hzero
    exact hxne (hker x hx0)
  have hΓiΓ : Γ⁻¹ * Γ = 1 := Matrix.nonsing_inv_mul Γ hdet
  have hΓΓi : Γ * Γ⁻¹ = 1 := Matrix.mul_nonsing_inv Γ hdet
  have hΓsymm : Γᵀ = Γ := by
    ext i j
    rw [Matrix.transpose_apply]
    show V j ⬝ᵥ V i = V i ⬝ᵥ V j
    exact dotProduct_comm _ _
  -- the span projector
  set spanProj := Vmat * Γ⁻¹ * Vmatᵀ with hπdef
  have hQV : Q * Vmat = Vmat := by
    ext rowIndex i
    have happly := congrFun (hfix i) rowIndex
    rw [Matrix.mulVec, dotProduct] at happly
    rw [Matrix.mul_apply]
    exact happly
  have hπsymm : spanProjᵀ = spanProj := by
    rw [hπdef, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, hΓsymm,
      ← Matrix.mul_assoc]
  have hQπ : Q * spanProj = spanProj := by
    rw [hπdef, ← Matrix.mul_assoc Q (Vmat * Γ⁻¹) Vmatᵀ,
      ← Matrix.mul_assoc Q Vmat Γ⁻¹, hQV]
  have hπQ : spanProj * Q = spanProj := by
    have htrans := congrArg Matrix.transpose hQπ
    rwa [Matrix.transpose_mul, hπsymm, hsymm] at htrans
  have hππ : spanProj * spanProj = spanProj := by
    rw [hπdef]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vmatᵀ Vmat (Γ⁻¹ * Vmatᵀ), hgram,
      ← Matrix.mul_assoc Γ⁻¹ Γ (Γ⁻¹ * Vmatᵀ), hΓiΓ, Matrix.one_mul]
  -- the difference is a symmetric idempotent
  have hDsymm : (Q - spanProj)ᵀ = Q - spanProj := by
    rw [Matrix.transpose_sub, hsymm, hπsymm]
  have hDidem : (Q - spanProj) * (Q - spanProj) = Q - spanProj := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hidem, hQπ, hπQ,
      hππ]
    abel
  -- its trace is a sum of squares
  have hnn : (0 : ℝ) ≤ Matrix.trace ((Q - spanProj)ᵀ * (Q - spanProj)) := by
    rw [Matrix.trace]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_nonneg fun j _ => ?_
    rw [Matrix.transpose_apply]
    exact mul_self_nonneg _
  have htraceD : (0 : ℝ) ≤ Matrix.trace (Q - spanProj) := by
    have hDD : (Q - spanProj)ᵀ * (Q - spanProj) = Q - spanProj := by
      rw [hDsymm, hDidem]
    rwa [hDD] at hnn
  -- the projector's trace is the family count
  have htraceπ : Matrix.trace spanProj = (m : ℝ) := by
    have hgroup : spanProj = Vmat * Γ⁻¹ * Vmatᵀ := hπdef
    rw [hgroup, Matrix.trace_mul_comm (Vmat * Γ⁻¹) Vmatᵀ,
      ← Matrix.mul_assoc, hgram, hΓΓi, Matrix.trace_one, Fintype.card_fin]
  have htrace_sub : Matrix.trace (Q - spanProj)
      = Matrix.trace Q - (m : ℝ) := by
    rw [Matrix.trace_sub, htraceπ]
  linarith

/-- **THE KERNEL EXTRACTION.**  A family of fixed vectors larger than
the trace has a Gram kernel vector. -/
theorem exists_gram_kernel_of_trace_lt {m n : ℕ}
    {Q : Matrix (Fin n) (Fin n) ℝ} (hsymm : Qᵀ = Q) (hidem : Q * Q = Q)
    (V : Fin m → Fin n → ℝ) (hfix : ∀ i, Q *ᵥ V i = V i)
    (hlt : Matrix.trace Q < (m : ℝ)) :
    ∃ x : Fin m → ℝ, x ≠ 0
      ∧ (Matrix.of fun i j => V i ⬝ᵥ V j) *ᵥ x = 0 := by
  by_contra hnot
  push Not at hnot
  have hker : ∀ x : Fin m → ℝ,
      (Matrix.of fun i j => V i ⬝ᵥ V j) *ᵥ x = 0 → x = 0 := by
    intro x hx
    by_contra hxne
    exact absurd hx (hnot x hxne)
  exact absurd (trace_floor_of_fixed_family hsymm hidem V hfix hker)
    (not_le.mpr hlt)

/-! ## Layer 3 — the datum laws -/

/-- The basis count caps at six: the left inverse forces independent
columns inside the six-atom space. -/
theorem SharedPrivateData.basisCount_le_six {crux : SixThreeCrux}
    (data : SharedPrivateData crux) : data.basisCount ≤ 6 := by
  have hrank : (data.leftInv
      * tightBasisColumns data.tightDir data.basisLabel).rank
      ≤ data.leftInv.rank :=
    Matrix.rank_mul_le_left _ _
  rw [data.hleft, Matrix.rank_one, Fintype.card_fin] at hrank
  exact le_trans hrank (Matrix.rank_le_width data.leftInv)

/-- Every basis support equals its block: the support sits inside the
block, and the two cards agree at three. -/
theorem SharedPrivateData.support_eq_block {crux : SixThreeCrux}
    (data : SharedPrivateData crux) (slot : Fin data.basisCount) :
    datumTightSupport data.tightDir (data.basisLabel slot)
      = data.activeSubset (data.basisLabel slot) := by
  have hmemActive : data.basisLabel slot ∈ data.activeSet := by
    have hmem := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at hmem
    exact hmem.1
  refine Finset.eq_of_subset_of_card_le
    (datumTightSupport_subset data.hdata hmemActive) ?_
  rw [data.hdata.activeSubset_card (data.basisLabel slot) hmemActive,
    data.hthree slot]

/-- **THE PIN UNIQUENESS.**  The pinned slot is the only slot whose
support carries the pin atom. -/
theorem SharedPrivateData.pin_only_slot {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {slot : Fin data.basisCount}
    (hmem : data.pinAtom ∈ datumTightSupport data.tightDir
      (data.basisLabel slot)) : slot = data.privateSlot := by
  classical
  have hcard : (Finset.univ.filter fun columnIndex =>
      data.pinAtom ∈ datumTightSupport data.tightDir
        (data.basisLabel columnIndex)).card = 1 := data.hmultOne
  obtain ⟨uniqueSlot, huniq⟩ := Finset.card_eq_one.mp hcard
  have hslot : slot ∈ Finset.univ.filter fun columnIndex =>
      data.pinAtom ∈ datumTightSupport data.tightDir
        (data.basisLabel columnIndex) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ slot, hmem⟩
  have hprivate : data.privateSlot ∈ Finset.univ.filter fun columnIndex =>
      data.pinAtom ∈ datumTightSupport data.tightDir
        (data.basisLabel columnIndex) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ data.privateSlot,
      mem_datumTightSupport.mpr data.hpinNe⟩
  rw [huniq, Finset.mem_singleton] at hslot hprivate
  rw [hslot, hprivate]

/-- **THE PIN DISJOINTNESS.**  The pin atom is support-disjoint from
every atom off the pinned support: a slot that carries the pin atom is
the pinned slot, and its support misses the other atom. -/
theorem SharedPrivateData.pin_disjoint_of_offSupport {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {atomIndex : Fin 6}
    (hoff : atomIndex ∉ datumTightSupport data.tightDir
      (data.basisLabel data.privateSlot)) :
    ∀ slot : Fin data.basisCount,
      data.pinAtom ∈ datumTightSupport data.tightDir
        (data.basisLabel slot) →
      atomIndex ∉ datumTightSupport data.tightDir
        (data.basisLabel slot) := by
  intro slot hpin
  rw [data.pin_only_slot hpin]
  exact hoff

set_option maxHeartbeats 1600000 in
/-- **THE READ FRAME PACKAGE.**  At a diagonal Gram core, the datum
carries a symmetric idempotent with the coefficient trace and six read
vectors: each vector vanishes off its support carrier, reads the
shifted weight on its block carrier, has energy one sixth, and does
not vanish. -/
theorem SharedPrivateData.exists_kernel_read_frame {crux : SixThreeCrux}
    (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) :
    ∃ (S : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ)
      (readVecs : Fin 6 → Fin data.basisCount → ℝ),
      Sᵀ = S ∧ S * S = S
      ∧ Matrix.trace S = Matrix.trace data.coeff
      ∧ (∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
          atomIndex ∉ datumTightSupport data.tightDir
            (data.basisLabel slot) →
          readVecs atomIndex slot = 0)
      ∧ (∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
          atomIndex ∈ data.activeSubset (data.basisLabel slot) →
          (S *ᵥ readVecs atomIndex) slot
            = (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomIndex)
              * readVecs atomIndex slot)
      ∧ (∀ atomIndex : Fin 6,
          readVecs atomIndex ⬝ᵥ readVecs atomIndex = (6 : ℝ)⁻¹)
      ∧ (∀ atomIndex : Fin 6, readVecs atomIndex ≠ 0)
      ∧ (∀ atomIndex : Fin 6,
          chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex = 0 →
          S *ᵥ readVecs atomIndex = 0)
      ∧ (∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
          atomIndex ∈ datumTightSupport data.tightDir
            (data.basisLabel slot) →
          readVecs atomIndex slot ≠ 0)
      ∧ (∀ x : Fin data.basisCount → ℝ,
          (∀ atomIndex : Fin 6, readVecs atomIndex ⬝ᵥ x = 0) → x = 0)
      ∧ (∀ rowSlot colSlot : Fin data.basisCount,
          (∑ atomIndex : Fin 6,
              readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot)
            = ∑ atomIndex : Fin 6,
              (S *ᵥ readVecs atomIndex) rowSlot
                * readVecs atomIndex colSlot) := by
  classical
  -- the positive diagonal of the Gram core
  have hpsd := data.hpsd
  have hker := data.hker
  rw [hdiag] at hpsd hker
  have hg : ∀ slot, 0 < gramDiag slot := by
    intro slot
    have hpos := posSemidef_diagonal_pos_of_kernel_free hpsd hker slot
    rwa [Matrix.diagonal_apply_eq] at hpos
  set sq : Fin data.basisCount → ℝ := fun slot => Real.sqrt (gramDiag slot)
    with hsqdef
  have hsq : ∀ slot, 0 < sq slot := fun slot => Real.sqrt_pos.mpr (hg slot)
  have hsqsq : ∀ slot, sq slot * sq slot = gramDiag slot :=
    fun slot => Real.mul_self_sqrt (hg slot).le
  -- the exchange entries under the diagonal core
  have hexchange := data.hexchange
  rw [hdiag] at hexchange
  have hx : ∀ rowSlot colSlot, data.coeff rowSlot colSlot * gramDiag colSlot
      = gramDiag rowSlot * data.coeff colSlot rowSlot := by
    intro rowSlot colSlot
    have hentry := congrFun (congrFun hexchange rowSlot) colSlot
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.transpose_apply] at hentry
  -- the conjugated coefficient matrix
  set S : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ :=
    Matrix.of fun rowSlot colSlot =>
      (sq rowSlot)⁻¹ * (data.coeff rowSlot colSlot * sq colSlot) with hSdef
  have hSapply : ∀ rowSlot colSlot, S rowSlot colSlot
      = (sq rowSlot)⁻¹ * (data.coeff rowSlot colSlot * sq colSlot) :=
    fun _ _ => rfl
  have hSsymm : Sᵀ = S := by
    ext rowSlot colSlot
    rw [Matrix.transpose_apply, hSapply, hSapply]
    refine mul_left_cancel₀
      (mul_ne_zero (hsq rowSlot).ne' (hsq colSlot).ne') ?_
    have hci : sq rowSlot * (sq rowSlot)⁻¹ = 1 :=
      mul_inv_cancel₀ (hsq rowSlot).ne'
    have hcj : sq colSlot * (sq colSlot)⁻¹ = 1 :=
      mul_inv_cancel₀ (hsq colSlot).ne'
    have hgi := hsqsq rowSlot
    have hgj := hsqsq colSlot
    have hxi := hx rowSlot colSlot
    linear_combination
      (data.coeff colSlot rowSlot * sq rowSlot * sq rowSlot) * hcj
      - (data.coeff rowSlot colSlot * sq colSlot * sq colSlot) * hci
      + data.coeff colSlot rowSlot * hgi
      - data.coeff rowSlot colSlot * hgj
      - hxi
  have hSidem : S * S = S := by
    ext rowSlot colSlot
    rw [Matrix.mul_apply]
    have hterm : ∀ midSlot, S rowSlot midSlot * S midSlot colSlot
        = (sq rowSlot)⁻¹
          * (data.coeff rowSlot midSlot * data.coeff midSlot colSlot)
          * sq colSlot := by
      intro midSlot
      rw [hSapply, hSapply]
      have hck : sq midSlot * (sq midSlot)⁻¹ = 1 :=
        mul_inv_cancel₀ (hsq midSlot).ne'
      linear_combination ((sq rowSlot)⁻¹ * data.coeff rowSlot midSlot
        * data.coeff midSlot colSlot * sq colSlot) * hck
    rw [Finset.sum_congr rfl fun midSlot _ => hterm midSlot,
      ← Finset.sum_mul, ← Finset.mul_sum]
    have hMM : ∑ midSlot, data.coeff rowSlot midSlot
        * data.coeff midSlot colSlot = data.coeff rowSlot colSlot := by
      have hentry := congrFun (congrFun data.hidempotent rowSlot) colSlot
      rwa [Matrix.mul_apply] at hentry
    rw [hMM, hSapply]
    ring
  have hStrace : Matrix.trace S = Matrix.trace data.coeff := by
    rw [Matrix.trace, Matrix.trace]
    refine Finset.sum_congr rfl fun slot _ => ?_
    have happly : S slot slot
        = (sq slot)⁻¹ * (data.coeff slot slot * sq slot) := rfl
    have hinv : (sq slot)⁻¹ * sq slot = 1 :=
      inv_mul_cancel₀ (hsq slot).ne'
    show S slot slot = data.coeff slot slot
    rw [happly]
    linear_combination data.coeff slot slot * hinv
  -- the read vectors
  set readVecs : Fin 6 → Fin data.basisCount → ℝ := fun atomIndex slot =>
    sq slot * data.tightDir (data.basisLabel slot) atomIndex with hreadVecs
  have hmemActive : ∀ slot, data.basisLabel slot ∈ data.activeSet := by
    intro slot
    have hmem := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at hmem
    exact hmem.1
  -- the support law
  have hsupp : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot) →
      readVecs atomIndex slot = 0 := by
    intro atomIndex slot hslot
    rw [mem_datumTightSupport, not_not] at hslot
    show sq slot * data.tightDir (data.basisLabel slot) atomIndex = 0
    rw [hslot, mul_zero]
  -- the carried rows
  have hcarried : ∀ (slot : Fin data.basisCount) (atomIndex : Fin 6),
      atomIndex ∈ data.activeSubset (data.basisLabel slot) →
      ∑ colSlot, data.tightDir (data.basisLabel colSlot) atomIndex
        * data.coeff colSlot slot
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * data.tightDir (data.basisLabel slot) atomIndex := by
    intro slot atomIndex hmemSubset
    have hrep := congrFun (congrFun data.hrepresentation atomIndex) slot
    rw [Matrix.mul_apply, Matrix.mul_apply] at hrep
    have hproj := projection_mulVec_tightDir_of_mem data.hdata
      (hmemActive slot) hmemSubset
    have hlhs : ∑ x, (chartPointOfDesign crux.design).chart atomIndex x
        * tightBasisColumns data.tightDir data.basisLabel x slot
        = ((chartPointOfDesign crux.design).chart
            *ᵥ data.tightDir (data.basisLabel slot)) atomIndex := rfl
    rw [hlhs, hproj] at hrep
    exact hrep.symm
  -- the block reads
  have hread : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      atomIndex ∈ data.activeSubset (data.basisLabel slot) →
      (S *ᵥ readVecs atomIndex) slot
        = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
          * readVecs atomIndex slot := by
    intro atomIndex slot hmemSubset
    have hterm : ∀ colSlot, S slot colSlot * readVecs atomIndex colSlot
        = ((sq slot)⁻¹ * gramDiag slot)
          * (data.tightDir (data.basisLabel colSlot) atomIndex
              * data.coeff colSlot slot) := by
      intro colSlot
      rw [hSapply]
      show (sq slot)⁻¹ * (data.coeff slot colSlot * sq colSlot)
          * (sq colSlot * data.tightDir (data.basisLabel colSlot) atomIndex)
        = ((sq slot)⁻¹ * gramDiag slot)
          * (data.tightDir (data.basisLabel colSlot) atomIndex
              * data.coeff colSlot slot)
      have hgj := hsqsq colSlot
      have hxj := hx slot colSlot
      linear_combination ((sq slot)⁻¹ * data.coeff slot colSlot
          * data.tightDir (data.basisLabel colSlot) atomIndex) * hgj
        + ((sq slot)⁻¹
            * data.tightDir (data.basisLabel colSlot) atomIndex) * hxj
    have hmul : (S *ᵥ readVecs atomIndex) slot
        = ∑ colSlot, S slot colSlot * readVecs atomIndex colSlot := rfl
    rw [hmul, Finset.sum_congr rfl fun colSlot _ => hterm colSlot,
      ← Finset.mul_sum, hcarried slot atomIndex hmemSubset]
    have hsimp : (sq slot)⁻¹ * gramDiag slot = sq slot := by
      rw [← hsqsq slot, ← mul_assoc, inv_mul_cancel₀ (hsq slot).ne',
        one_mul]
    show ((sq slot)⁻¹ * gramDiag slot)
        * ((chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
          * data.tightDir (data.basisLabel slot) atomIndex)
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * (sq slot * data.tightDir (data.basisLabel slot) atomIndex)
    rw [hsimp]
    ring
  -- the row norms from the Gram form and the constant diagonal
  have hnorm : ∀ atomIndex : Fin 6,
      readVecs atomIndex ⬝ᵥ readVecs atomIndex = (6 : ℝ)⁻¹ := by
    intro atomIndex
    have hH := congrFun (congrFun data.hHform atomIndex) atomIndex
    rw [hdiag] at hH
    have hlhs : (tightBasisColumns data.tightDir data.basisLabel
        * Matrix.diagonal gramDiag
        * (tightBasisColumns data.tightDir data.basisLabel)ᵀ)
          atomIndex atomIndex
        = ∑ slot, tightBasisColumns data.tightDir data.basisLabel
            atomIndex slot * gramDiag slot
          * tightBasisColumns data.tightDir data.basisLabel
            atomIndex slot := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun slot _ => ?_
      rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    rw [hlhs] at hH
    have hdiagval := data.hdata.assembly_diagonal atomIndex
    rw [hdiagval] at hH
    have hdot : readVecs atomIndex ⬝ᵥ readVecs atomIndex
        = ∑ slot, tightBasisColumns data.tightDir data.basisLabel
            atomIndex slot * gramDiag slot
          * tightBasisColumns data.tightDir data.basisLabel
            atomIndex slot := by
      rw [dotProduct]
      refine Finset.sum_congr rfl fun slot _ => ?_
      show sq slot * data.tightDir (data.basisLabel slot) atomIndex
          * (sq slot * data.tightDir (data.basisLabel slot) atomIndex)
        = tightBasisColumns data.tightDir data.basisLabel atomIndex slot
          * gramDiag slot
          * tightBasisColumns data.tightDir data.basisLabel atomIndex slot
      have hgk := hsqsq slot
      show sq slot * data.tightDir (data.basisLabel slot) atomIndex
          * (sq slot * data.tightDir (data.basisLabel slot) atomIndex)
        = data.tightDir (data.basisLabel slot) atomIndex * gramDiag slot
          * data.tightDir (data.basisLabel slot) atomIndex
      linear_combination (data.tightDir (data.basisLabel slot) atomIndex
        * data.tightDir (data.basisLabel slot) atomIndex) * hgk
    rw [hdot, hH]
    norm_num
  -- the coverage law
  have hnz : ∀ atomIndex : Fin 6, readVecs atomIndex ≠ 0 := by
    intro atomIndex hzero
    obtain ⟨slot, hslot⟩ := exists_basisIndex_datumTightSupport data.hdata
      data.basisLabel data.hspan data.leftInv data.hleft atomIndex
    have hq := mem_datumTightSupport.mp hslot
    have hv : readVecs atomIndex slot = 0 := congrFun hzero slot
    exact mul_ne_zero (hsq slot).ne' hq hv
  -- the boundary law: a zero shifted weight puts the read in the kernel
  have hboundary : ∀ atomIndex : Fin 6,
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0 →
      S *ᵥ readVecs atomIndex = 0 := by
    intro atomIndex hzero
    funext slot
    have hrow := basis_capture_column_zero_of_diagonal_zero data.hdata
      data.hspan data.hrepresentation hzero slot
    have hentry : (tightBasisColumns data.tightDir data.basisLabel
        * data.coeff) atomIndex slot
        = ∑ colSlot, data.tightDir (data.basisLabel colSlot) atomIndex
          * data.coeff colSlot slot := by
      rw [Matrix.mul_apply]
      rfl
    rw [hentry] at hrow
    have hterm : ∀ colSlot, S slot colSlot * readVecs atomIndex colSlot
        = ((sq slot)⁻¹ * gramDiag slot)
          * (data.tightDir (data.basisLabel colSlot) atomIndex
              * data.coeff colSlot slot) := by
      intro colSlot
      rw [hSapply]
      show (sq slot)⁻¹ * (data.coeff slot colSlot * sq colSlot)
          * (sq colSlot * data.tightDir (data.basisLabel colSlot) atomIndex)
        = ((sq slot)⁻¹ * gramDiag slot)
          * (data.tightDir (data.basisLabel colSlot) atomIndex
              * data.coeff colSlot slot)
      have hgj := hsqsq colSlot
      have hxj := hx slot colSlot
      linear_combination ((sq slot)⁻¹ * data.coeff slot colSlot
          * data.tightDir (data.basisLabel colSlot) atomIndex) * hgj
        + ((sq slot)⁻¹
            * data.tightDir (data.basisLabel colSlot) atomIndex) * hxj
    have hmul : (S *ᵥ readVecs atomIndex) slot
        = ∑ colSlot, S slot colSlot * readVecs atomIndex colSlot := rfl
    rw [hmul, Finset.sum_congr rfl fun colSlot _ => hterm colSlot,
      ← Finset.mul_sum, hrow, mul_zero]
    rfl
  -- the carrier law: a read does not vanish on its own carrier
  have hcarrierNz : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      readVecs atomIndex slot ≠ 0 := by
    intro atomIndex slot hmem
    show sq slot * data.tightDir (data.basisLabel slot) atomIndex ≠ 0
    exact mul_ne_zero (hsq slot).ne' (mem_datumTightSupport.mp hmem)
  -- the span law: no nonzero slot functional annihilates every read
  have hspanLaw : ∀ x : Fin data.basisCount → ℝ,
      (∀ atomIndex : Fin 6, readVecs atomIndex ⬝ᵥ x = 0) → x = 0 := by
    intro x hx
    set scaled : Fin data.basisCount → ℝ := fun slot => sq slot * x slot
      with hscaled
    have hzero : tightBasisColumns data.tightDir data.basisLabel *ᵥ scaled
        = 0 := by
      funext atomIndex
      have heq : (tightBasisColumns data.tightDir data.basisLabel
          *ᵥ scaled) atomIndex = readVecs atomIndex ⬝ᵥ x := by
        show (∑ slot, data.tightDir (data.basisLabel slot) atomIndex
            * (sq slot * x slot))
          = ∑ slot, sq slot * data.tightDir (data.basisLabel slot) atomIndex
            * x slot
        exact Finset.sum_congr rfl fun slot _ => by ring
      rw [heq, hx atomIndex]
      rfl
    have hrecover : data.leftInv
        *ᵥ (tightBasisColumns data.tightDir data.basisLabel *ᵥ scaled)
        = scaled := by
      rw [Matrix.mulVec_mulVec, data.hleft, Matrix.one_mulVec]
    rw [hzero, Matrix.mulVec_zero] at hrecover
    funext slot
    have hslot : sq slot * x slot = 0 := (congrFun hrecover slot).symm
    rcases mul_eq_zero.mp hslot with hcase | hcase
    · exact absurd hcase (hsq slot).ne'
    · exact hcase
  -- the read Gram commutes with the read idempotent
  have hSval : ∀ colSlot midSlot : Fin data.basisCount,
      S colSlot midSlot * sq midSlot
        = sq colSlot * data.coeff midSlot colSlot := by
    intro colSlot midSlot
    have hsym := congrFun (congrFun hSsymm colSlot) midSlot
    rw [Matrix.transpose_apply] at hsym
    rw [← hsym, hSapply]
    have hkinv : (sq midSlot)⁻¹ * sq midSlot = 1 :=
      inv_mul_cancel₀ (hsq midSlot).ne'
    linear_combination (data.coeff midSlot colSlot * sq colSlot) * hkinv
  have hNentry : ∀ rowSlot midSlot : Fin data.basisCount,
      ((tightBasisColumns data.tightDir data.basisLabel)ᵀ
          * tightBasisColumns data.tightDir data.basisLabel)
        rowSlot midSlot
        = ∑ atomIndex : Fin 6,
          data.tightDir (data.basisLabel rowSlot) atomIndex
            * data.tightDir (data.basisLabel midSlot) atomIndex := by
    intro rowSlot midSlot
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun atomIndex _ => rfl
  have hkey : ∀ rowSlot colSlot : Fin data.basisCount,
      (∑ atomIndex : Fin 6,
          readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot)
        = sq rowSlot * sq colSlot
          * (((tightBasisColumns data.tightDir data.basisLabel)ᵀ
              * tightBasisColumns data.tightDir data.basisLabel)
            * data.coeff) rowSlot colSlot := by
    intro rowSlot colSlot
    have hterm : ∀ atomIndex : Fin 6,
        readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot
          = ∑ midSlot, (sq rowSlot * sq colSlot
              * data.coeff midSlot colSlot)
            * (data.tightDir (data.basisLabel rowSlot) atomIndex
              * data.tightDir (data.basisLabel midSlot) atomIndex) := by
      intro atomIndex
      have hmul : (S *ᵥ readVecs atomIndex) colSlot
          = ∑ midSlot, S colSlot midSlot * readVecs atomIndex midSlot := rfl
      rw [hmul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun midSlot _ => ?_
      have hv := hSval colSlot midSlot
      show (sq rowSlot * data.tightDir (data.basisLabel rowSlot) atomIndex)
          * (S colSlot midSlot
            * (sq midSlot
              * data.tightDir (data.basisLabel midSlot) atomIndex))
        = (sq rowSlot * sq colSlot * data.coeff midSlot colSlot)
          * (data.tightDir (data.basisLabel rowSlot) atomIndex
            * data.tightDir (data.basisLabel midSlot) atomIndex)
      linear_combination (sq rowSlot
        * data.tightDir (data.basisLabel rowSlot) atomIndex
        * data.tightDir (data.basisLabel midSlot) atomIndex) * hv
    have hinner : ∀ midSlot : Fin data.basisCount,
        (∑ atomIndex : Fin 6, (sq rowSlot * sq colSlot
            * data.coeff midSlot colSlot)
          * (data.tightDir (data.basisLabel rowSlot) atomIndex
            * data.tightDir (data.basisLabel midSlot) atomIndex))
          = sq rowSlot * sq colSlot
            * (((tightBasisColumns data.tightDir data.basisLabel)ᵀ
                * tightBasisColumns data.tightDir data.basisLabel)
              rowSlot midSlot * data.coeff midSlot colSlot) := by
      intro midSlot
      rw [← Finset.mul_sum, ← hNentry rowSlot midSlot]
      ring
    rw [Finset.sum_congr rfl fun atomIndex _ => hterm atomIndex,
      Finset.sum_comm,
      Finset.sum_congr rfl fun midSlot _ => hinner midSlot,
      ← Finset.mul_sum, Matrix.mul_apply]
  have hexch := columnGram_exchange_of_representation
    data.hdata.isSymmetric data.hrepresentation
  have hNsymm : ((tightBasisColumns data.tightDir data.basisLabel)ᵀ
      * tightBasisColumns data.tightDir data.basisLabel)ᵀ
      = (tightBasisColumns data.tightDir data.basisLabel)ᵀ
        * tightBasisColumns data.tightDir data.basisLabel := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hNMsymm : ((((tightBasisColumns data.tightDir data.basisLabel)ᵀ
      * tightBasisColumns data.tightDir data.basisLabel)
        * data.coeff))ᵀ
      = ((tightBasisColumns data.tightDir data.basisLabel)ᵀ
          * tightBasisColumns data.tightDir data.basisLabel)
        * data.coeff := by
    rw [Matrix.transpose_mul, hNsymm, ← hexch]
  have hcommute : ∀ rowSlot colSlot : Fin data.basisCount,
      (∑ atomIndex : Fin 6,
          readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot)
        = ∑ atomIndex : Fin 6,
          (S *ᵥ readVecs atomIndex) rowSlot
            * readVecs atomIndex colSlot := by
    intro rowSlot colSlot
    have hswap : (∑ atomIndex : Fin 6,
        (S *ᵥ readVecs atomIndex) rowSlot * readVecs atomIndex colSlot)
        = ∑ atomIndex : Fin 6,
          readVecs atomIndex colSlot * (S *ᵥ readVecs atomIndex) rowSlot :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hentry := congrFun (congrFun hNMsymm colSlot) rowSlot
    rw [Matrix.transpose_apply] at hentry
    rw [hswap, hkey rowSlot colSlot, hkey colSlot rowSlot, hentry]
    ring
  exact ⟨S, readVecs, hSsymm, hSidem, hStrace, hsupp, hread, hnorm, hnz,
    hboundary, hcarrierNz, hspanLaw, hcommute⟩

set_option maxHeartbeats 1600000 in
/-- **THE DISJOINT-FAMILY KILL.**  At a diagonal Gram core, a family
of atoms with pairwise disjoint support carriers and one atom more
than the complement trace kills the datum.  The kernel parts of the
read vectors form a kernel-free Gram inside the kernel idempotent,
and the trace floor refuses the count. -/
theorem SharedPrivateData.false_of_disjoint_support_family
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (T : Finset (Fin 6))
    (hdisjoint : ∀ y ∈ T, ∀ y' ∈ T, y ≠ y' →
      ∀ slot : Fin data.basisCount,
        y ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
        y' ∉ datumTightSupport data.tightDir (data.basisLabel slot))
    (hcount : (data.basisCount : ℝ)
      < Matrix.trace data.coeff + T.card) : False := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsupp, hread, hnorm, hnz,
    _hboundary, _hcarrierNz, _hspan, _hcommute⟩ :=
    data.exists_kernel_read_frame hdiag
  set chartValue := chartObjective (chartPointOfDesign crux.design)
    with hchartValue
  set atomWeight := (chartPointOfDesign crux.design).weight with hatomWeight
  set shifted : Fin 6 → ℝ := fun atomIndex =>
    chartValue + atomWeight atomIndex with hshifted
  -- the per-atom carrier data
  set car : Fin 6 → Finset (Fin data.basisCount) := fun atomIndex =>
    Finset.univ.filter fun slot =>
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)
    with hcar
  have hcarSupp : ∀ atomIndex : Fin 6, ∀ slot ∉ car atomIndex,
      readVecs atomIndex slot = 0 := by
    intro atomIndex slot hslot
    refine hsupp atomIndex slot ?_
    intro hmem
    exact hslot (Finset.mem_filter.mpr ⟨Finset.mem_univ slot, hmem⟩)
  have hcarRead : ∀ atomIndex : Fin 6, ∀ slot ∈ car atomIndex,
      (S *ᵥ readVecs atomIndex) slot
        = shifted atomIndex * readVecs atomIndex slot := by
    intro atomIndex slot hslot
    have hmem := (Finset.mem_filter.mp hslot).2
    have hmemActive : data.basisLabel slot ∈ data.activeSet := by
      have hmemPos := data.hmem slot
      simp only [positiveActiveSet, Finset.mem_filter] at hmemPos
      exact hmemPos.1
    exact hread atomIndex slot
      (datumTightSupport_subset data.hdata hmemActive hmem)
  -- the shifted weights are nonnegative and sum below one
  have hdnonneg : ∀ atomIndex : Fin 6, 0 ≤ shifted atomIndex :=
    fun atomIndex =>
      capture_diagonal_nonneg_of_isChartStationaryData data.hdata atomIndex
  have hneg : chartValue < 0 := data.hvalueNeg
  have hsum_univ : ∑ atomIndex : Fin 6, shifted atomIndex
      = 6 * chartValue + 1 := by
    have hexpand : ∑ atomIndex : Fin 6, shifted atomIndex
        = ∑ atomIndex : Fin 6, (chartValue + atomWeight atomIndex) := rfl
    rw [hexpand, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, data.hdata.weight_sum_one,
      nsmul_eq_mul]
    norm_num
  -- the enumerated kernel family
  set count := T.card with hcount_def
  set enum := T.orderIsoOfFin (rfl : T.card = count) with henum
  set V : Fin count → Fin data.basisCount → ℝ := fun i =>
    readVecs ((enum i : {x // x ∈ T}) : Fin 6)
      - S *ᵥ readVecs ((enum i : {x // x ∈ T}) : Fin 6) with hV
  have henum_mem : ∀ i : Fin count, ((enum i : {x // x ∈ T}) : Fin 6) ∈ T :=
    fun i => (enum i).2
  have henum_ne : ∀ i j : Fin count, i ≠ j →
      ((enum i : {x // x ∈ T}) : Fin 6)
        ≠ ((enum j : {x // x ∈ T}) : Fin 6) := by
    intro i j hne hcontra
    exact hne (enum.toEquiv.injective (Subtype.coe_injective hcontra))
  -- the kernel family is fixed by the complement idempotent
  have hcomplSymm : (1 - S)ᵀ = 1 - S := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hSsymm]
  have hcomplIdem : (1 - S) * (1 - S) = 1 - S := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hSidem]
    abel
  have hfix : ∀ i : Fin count, (1 - S) *ᵥ V i = V i := by
    intro i
    set z := readVecs ((enum i : {x // x ∈ T}) : Fin 6) with hz
    show (1 - S) *ᵥ (z - S *ᵥ z) = z - S *ᵥ z
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec, hSidem]
    abel
  -- the Gram data of the kernel family
  have hself : ∀ i : Fin count, V i ⬝ᵥ V i
      = (1 - shifted ((enum i : {x // x ∈ T}) : Fin 6)) * (6 : ℝ)⁻¹ := by
    intro i
    have henergy := kernel_part_energy hSsymm hSidem
      (hcarSupp ((enum i : {x // x ∈ T}) : Fin 6))
      (hcarRead ((enum i : {x // x ∈ T}) : Fin 6))
    rw [hnorm ((enum i : {x // x ∈ T}) : Fin 6)] at henergy
    exact henergy
  have hcross : ∀ i j : Fin count, i ≠ j →
      (V i ⬝ᵥ V j) ^ 2
        ≤ shifted ((enum i : {x // x ∈ T}) : Fin 6) * (6 : ℝ)⁻¹
          * (shifted ((enum j : {x // x ∈ T}) : Fin 6) * (6 : ℝ)⁻¹) := by
    intro i j hne
    set yi := ((enum i : {x // x ∈ T}) : Fin 6) with hyi
    set yj := ((enum j : {x // x ∈ T}) : Fin 6) with hyj
    have hcrosslaw := kernel_cross_law hSsymm hSidem
      (readVecs yi) (readVecs yj)
    have hdot0 : readVecs yi ⬝ᵥ readVecs yj = 0 := by
      refine disjoint_support_dot (hcarSupp yi) (hcarSupp yj) ?_
      intro slot hslot
      have hmem := (Finset.mem_filter.mp hslot).2
      have hnotmem := hdisjoint yi (henum_mem i) yj (henum_mem j)
        (henum_ne i j hne) slot hmem
      intro hcontra
      exact hnotmem (Finset.mem_filter.mp hcontra).2
    have hVij : V i ⬝ᵥ V j
        = -((S *ᵥ readVecs yi) ⬝ᵥ (S *ᵥ readVecs yj)) := by
      show (readVecs yi - S *ᵥ readVecs yi)
          ⬝ᵥ (readVecs yj - S *ᵥ readVecs yj)
        = -((S *ᵥ readVecs yi) ⬝ᵥ (S *ᵥ readVecs yj))
      rw [hcrosslaw, hdot0]
      ring
    have hcs := dotProduct_sq_le_mul (S *ᵥ readVecs yi) (S *ᵥ readVecs yj)
    have hselfi := read_fixed_self_energy hSsymm hSidem
      (hcarSupp yi) (hcarRead yi)
    have hselfj := read_fixed_self_energy hSsymm hSidem
      (hcarSupp yj) (hcarRead yj)
    rw [hnorm yi] at hselfi
    rw [hnorm yj] at hselfj
    rw [hVij, neg_sq]
    rw [hselfi, hselfj] at hcs
    exact hcs
  have hsum_T : ∑ i : Fin count,
      shifted ((enum i : {x // x ∈ T}) : Fin 6) < 1 := by
    have hsum_eq : ∑ i : Fin count,
        shifted ((enum i : {x // x ∈ T}) : Fin 6)
        = ∑ y ∈ T, shifted y := by
      rw [← Finset.sum_coe_sort T shifted]
      exact Fintype.sum_equiv enum.toEquiv _ _ fun i => rfl
    have hle : ∑ y ∈ T, shifted y ≤ ∑ y : Fin 6, shifted y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
        fun y _ _ => hdnonneg y
    rw [hsum_eq]
    rw [hsum_univ] at hle
    linarith
  -- the kernel-free Gram
  have hker := gram_kernel_free_of_bounded_cross V
    (fun i => shifted ((enum i : {x // x ∈ T}) : Fin 6))
    (fun _ => (6 : ℝ)⁻¹) (fun _ => by norm_num)
    (fun i => hdnonneg _) hself hcross hsum_T
  -- the trace floor refuses the count
  have hfloor := trace_floor_of_fixed_family hcomplSymm hcomplIdem V hfix
    hker
  have htrace_compl : Matrix.trace ((1 : Matrix (Fin data.basisCount)
      (Fin data.basisCount) ℝ) - S)
      = (data.basisCount : ℝ) - Matrix.trace data.coeff := by
    rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, hStrace]
  rw [htrace_compl] at hfloor
  rw [hcount_def] at hfloor
  linarith

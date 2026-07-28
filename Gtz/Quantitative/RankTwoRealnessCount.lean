/-
# The dimension count that the rank-two adjugate-pairing step consumes

The rank-two proof of `GtzWeightedAll 2` closes its positive-definite branch with a
single sign: the adjugate-paired trace of

    Psi = Omega ^ 2 - zeta zetaᵀ - 2 Omega

must be nonnegative, where `Omega` is the second-moment operator of the traceless
parts of the atoms and `zeta` is their centred-leverage moment.  **That sign is a
DIMENSION COUNT.**  This file isolates it, states it at every rank over both fields,
and gives the three instances that matter.

## The step, exactly as it is shipped

The consumer is `Gtz.pd_contradiction` in `Gtz/Reduction/RankTwo.lean` (declared at
line 388 — note that `Gtz/Planar/RankTwo.lean`, cited in some campaign notes, does
not exist).  Three of its lines carry the whole count:

* line 458, `htrsig : sig = O00 + O11 - 4`.  Here `sig = Sum_c t_c z_c ^ 2` with
  `z_c = leverage_c - 2`, and `O00 + O11 = tr Omega = Sum_c t_c leverage_c ^ 2`, so
  `sig = tr Omega - 2 k (Sum t leverage) + k ^ 2 (Sum t) = tr Omega - k ^ 2`.
  **The `4` on that line is `k ^ 2`.**
* lines 534–538, the ring-checked `hT`:
  `O11 P00 - 2 O01 P01 + O00 P11 = (O00 O11 - O01 ^ 2) (O00 + O11 - 4) - zetaᵀ adj zeta`.
  This is `tr(adj Omega . Psi) = det Omega (tr Omega - 2 n) - zetaᵀ adj Omega zeta`
  at `n = 2`, the size of `Omega`.  **The `4` on line 535 is `2 n`.**
* line 539, `rw [hT, ← htrsig]`, which rewrites `O00 + O11 - 4` into `sig` and hands
  the goal to the Schur bound `hP1` of line 492.  **That single rewrite is where the
  two different fours are identified, i.e. where `2 n = k ^ 2` is consumed.**

`trace_adjugate_mul_adjugatePairingForm` proves the identity at every dimension, with
`2 * dimension` visible where the literal `4` sits;
`trace_adjugate_mul_adjugatePairingForm_atDimensionTwo` checks that its `dimension = 2`
instance is character-for-character the shipped `hT`, so the abstraction here is the
shipped step and not a lookalike.  Symmetry of `Omega` is nowhere needed and is
therefore nowhere assumed: `Matrix.adjugate_mul` alone carries the identity.

## What `n` is, and what it is not

`n` is the dimension of the AMBIENT traceless second-moment space — the space the
double-angle vectors `w_c` live in, hence the size of `Omega`.  Over the reals at
rank two the shipped `w_c = (x^2 - y^2, 2 x y)` is exactly `sqrt 2` times the
coordinate vector of the traceless part `g_c g_cᵀ - (leverage_c / k) I` in a
Frobenius-orthonormal basis, the factor being fixed by `|w_c| ^ 2 = leverage_c ^ 2`
(the `wlen_sq` of `Gtz/Reduction/RankTwo.lean:278`), which is what makes
`tr Omega = Sum_c t_c leverage_c ^ 2` and hence `sig = tr Omega - k ^ 2`.  Over `F`
at rank `k` the ambient space is the traceless self-adjoint `k`-by-`k` matrices over
`F`, viewed as a real vector space:

* `symmetricTracelessSubmodule k` over the reals, of dimension `k (k+1) / 2 - 1`;
* `hermitianTracelessSubmodule k` over the complexes, of dimension `k ^ 2 - 1`.

Both are proved here rather than assumed.  The real count goes through an explicit
linear injection of the upper triangle (`symmetrizeUpperTriangle`) whose range is the
symmetric matrices, plus `LinearMap.finrank_range_of_inj`; the complex count goes
through mathlib's `StarModule.decomposeProdAdjoint` together with
`skewAdjoint.negISMul`, which halves the real dimension `2 k ^ 2` of the complex
matrices.  The traceless hyperplane in each is cut by
`Submodule.finrank_sup_span_singleton` against the identity matrix.  No basis of
symmetric matrices is constructed and none is needed.

`n` is NOT the dimension of the span of any particular design's traceless moments,
which can be smaller.  The count is a property of the rank and the field alone, which
is exactly why it transports — and exactly why it cannot be improved by choosing a
better design.

## The three instances

    field     rank   n   2n   k^2   verdict
    reals      2     2    4    4    EQUALITY, with nothing to spare
    complexes  2     3    6    4    deficit 2
    reals      3     5   10    9    deficit exactly 1

`twiceFinrank_symmetricTracelessSubmodule_eq_sq_atRankTwo` is the equality — the
reason the rank-two argument closes over the reals at all, and it closes with zero
slack.  `twiceFinrank_hermitianTracelessSubmodule_eq_sq_add_two_atRankTwo` is the
complex deficit, the reason the same argument cannot close over the complexes — where
the conclusion is in any case false, by `Gtz.complexGtzWeighted_four_fails`.
`twiceFinrank_symmetricTracelessSubmodule_eq_sq_add_one_atRankThree` is the real
rank-three deficit, and it is exactly one.

`isWithinAdjugatePairingBudget_symmetricTracelessSubmodule_iff` and its Hermitian twin
state the full classification: over the reals the budget holds exactly at `k <= 2`,
over the complexes exactly at `k <= 1`.

`trace_adjugate_mul_adjugatePairingForm_complexSicBlochMoment` exhibits the failure as
a number.  At the complex SIC in dimension two the Bloch second-moment operator is
`(4/3) I_3` and the centred-leverage moment vanishes (every leverage equals the rank),
so `sig = 0`, the Schur bound is tight at zero, and the paired trace is
`det (tr - 2n) = (64/27)(4 - 6) = -128/27 < 0`.  All of the failure is the deficit.

## NOT AN IMPOSSIBILITY RESULT — said plainly, because the names could be misread

Every theorem below is a dimension count and a sign it implies.  Together they say:
*the adjugate-pairing step, in the form written at `Gtz/Reduction/RankTwo.lean:533`,
is available exactly when `2 n <= k ^ 2`.*  They do NOT say, and nothing here proves:

* that no rank-three proof of `GtzWeighted m 3` exists.  The pairing step is one step
  of several; its first step — trading `lambda_min (S_C) >= 1` for the single scalar
  `det (S_C - I)` — has no rank-three analogue at all, since a Hermitian 3-by-3 matrix
  with positive trace and positive determinant need not be positive semidefinite.  A
  budget for a transport that already fails earlier is a budget and not an obstruction.
* that `2 n <= k ^ 2` is NECESSARY for the conclusion `0 <= tr(adj Omega . Psi)` at a
  given `Omega` and `zeta`.  It is sufficient given the Schur bound, and that is all
  `trace_adjugate_mul_adjugatePairingForm_nonneg_of_isWithinAdjugatePairingBudget`
  claims.  The complex-SIC witness shows the CONCLUSION fails at one point outside the
  budget; it does not show it fails at every such point.
* anything about `GtzWeighted 6 3` or `GtzWeighted 7 3`, which are untouched.

The complex SIC data enters here as a numeral, `(4/3) I_3` with `zeta = 0`.  That this
numeral is the Bloch second-moment operator of the four SIC lines in `C ^ 2` is
arithmetic recorded in the docstring and NOT mechanized; the theorem is about the
matrix, and its name says `blochMoment` rather than `sic` wherever the distinction
matters.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Complex.ComplexWitness

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The adjugate pairing form and its trace -/

/-- **The pairing form** `Psi = Omega ^ 2 - zeta zetaᵀ - 2 Omega` of a second-moment
operator `Omega` and a centred moment vector `zeta`.  At `dimension = 2` its three
distinct entries are the `P00`, `P01`, `P11` set at `Gtz/Reduction/RankTwo.lean:529`. -/
noncomputable def adjugatePairingForm {dimension : ℕ}
    (moment : Matrix (Fin dimension) (Fin dimension) ℝ) (centre : Fin dimension → ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℝ :=
  moment * moment - Matrix.vecMulVec centre centre - (2 : ℝ) • moment

/-- Pairing a matrix against a rank-one outer product reads off a quadratic form. -/
theorem trace_mul_vecMulVec {dimension : ℕ}
    (matrix : Matrix (Fin dimension) (Fin dimension) ℝ) (centre : Fin dimension → ℝ) :
    Matrix.trace (matrix * Matrix.vecMulVec centre centre) = centre ⬝ᵥ (matrix *ᵥ centre) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun rowIndex _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun colIndex _ => by ring

/-- **The adjugate pairing identity**, at every dimension and for every square
`moment`: the size of the matrix enters as `2 * dimension`.  Two lines from
`Matrix.adjugate_mul`, and symmetry of `moment` is not used. -/
theorem trace_adjugate_mul_adjugatePairingForm {dimension : ℕ}
    (moment : Matrix (Fin dimension) (Fin dimension) ℝ) (centre : Fin dimension → ℝ) :
    Matrix.trace (moment.adjugate * adjugatePairingForm moment centre)
      = moment.det * (Matrix.trace moment - 2 * dimension)
        - centre ⬝ᵥ (moment.adjugate *ᵥ centre) := by
  have hsquare : Matrix.trace (moment.adjugate * (moment * moment))
      = moment.det * Matrix.trace moment := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_smul, smul_eq_mul]
  have hscaled : Matrix.trace (moment.adjugate * ((2 : ℝ) • moment))
      = 2 * dimension * moment.det := by
    rw [Matrix.mul_smul, Matrix.adjugate_mul, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_one, Fintype.card_fin, smul_eq_mul, smul_eq_mul]
    ring
  rw [adjugatePairingForm, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.trace_sub, hsquare, hscaled, trace_mul_vecMulVec]
  ring

/-- **The dimension-two instance is the shipped step.**  The right-hand side below is
character-for-character the left-hand side of the `hT` binding at
`Gtz/Reduction/RankTwo.lean:534`, with `P00`, `P01`, `P11` expanded from line 529, so
`trace_adjugate_mul_adjugatePairingForm` really does abstract that line and not a
lookalike. -/
theorem trace_adjugate_mul_adjugatePairingForm_atDimensionTwo
    (momentXX momentXY momentYY centreX centreY : ℝ) :
    Matrix.trace
        ((!![momentXX, momentXY; momentXY, momentYY] : Matrix (Fin 2) (Fin 2) ℝ).adjugate
          * adjugatePairingForm !![momentXX, momentXY; momentXY, momentYY]
              ![centreX, centreY])
      = momentYY * (momentXX ^ 2 + momentXY ^ 2 - centreX ^ 2 - 2 * momentXX)
        - 2 * momentXY * (momentXX * momentXY + momentXY * momentYY
            - centreX * centreY - 2 * momentXY)
        + momentXX * (momentXY ^ 2 + momentYY ^ 2 - centreY ^ 2 - 2 * momentYY) := by
  have hcentre : Matrix.vecMulVec ![centreX, centreY] ![centreX, centreY]
      = !![centreX * centreX, centreX * centreY; centreY * centreX, centreY * centreY] := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> simp [Matrix.vecMulVec_apply]
  rw [adjugatePairingForm, hcentre]
  simp [Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  ring

/-! ## The budget the step consumes -/

/-- **The adjugate-pairing budget** at ambient traceless dimension `dimension` and rank
`rank`: `2 * dimension <= rank ^ 2`.  The left side is the `2 n` of the pairing
identity, the right side the `rank ^ 2` of the centred-leverage identity
`sig = tr Omega - rank ^ 2`. -/
def IsWithinAdjugatePairingBudget (dimension rank : ℕ) : Prop :=
  2 * dimension ≤ rank ^ 2

/-- **The sign the rank-two argument needs, at every rank and dimension.**  Given the
centred-leverage identity `hspread`, the Schur bound `hschur` (the `hP1` of
`Gtz/Reduction/RankTwo.lean:492`), a nonnegative determinant, and the budget, the
adjugate-paired trace is nonnegative.  At the shipped parameters
`dimension = rank = 2` the budget is an equality and the conclusion is `hP1` itself. -/
theorem trace_adjugate_mul_adjugatePairingForm_nonneg_of_isWithinAdjugatePairingBudget
    {dimension rank : ℕ} (moment : Matrix (Fin dimension) (Fin dimension) ℝ)
    (centre : Fin dimension → ℝ) (spread : ℝ) (hdet : 0 ≤ moment.det)
    (hspread : spread = Matrix.trace moment - rank ^ 2)
    (hschur : centre ⬝ᵥ (moment.adjugate *ᵥ centre) ≤ moment.det * spread)
    (hbudget : IsWithinAdjugatePairingBudget dimension rank) :
    0 ≤ Matrix.trace (moment.adjugate * adjugatePairingForm moment centre) := by
  have hcast : (2 * dimension : ℝ) ≤ ((rank : ℝ)) ^ 2 := by
    have hnat := (Nat.cast_le (α := ℝ)).mpr hbudget
    push_cast at hnat
    exact hnat
  have hslack : 0 ≤ moment.det * (((rank : ℝ)) ^ 2 - 2 * dimension) :=
    mul_nonneg hdet (by linarith)
  have hexpand : moment.det * (Matrix.trace moment - 2 * dimension)
      = moment.det * spread + moment.det * (((rank : ℝ)) ^ 2 - 2 * dimension) := by
    rw [hspread]; ring
  rw [trace_adjugate_mul_adjugatePairingForm, hexpand]
  linarith

/-! ## The traceless self-adjoint space over each field -/

/-- **The symmetric matrices**, as a real submodule: the ambient second-moment space
over the reals before the trace is removed. -/
def symmetricSubmodule (rank : ℕ) : Submodule ℝ (Matrix (Fin rank) (Fin rank) ℝ) :=
  selfAdjoint.submodule ℝ (Matrix (Fin rank) (Fin rank) ℝ)

/-- **The Hermitian matrices**, as a REAL submodule (they are not a complex one): the
ambient second-moment space over the complexes before the trace is removed. -/
noncomputable def hermitianSubmodule (rank : ℕ) :
    Submodule ℝ (Matrix (Fin rank) (Fin rank) ℂ) :=
  selfAdjoint.submodule ℝ (Matrix (Fin rank) (Fin rank) ℂ)

/-- **The traceless second-moment space over the reals** at rank `rank`. -/
noncomputable def symmetricTracelessSubmodule (rank : ℕ) :
    Submodule ℝ (Matrix (Fin rank) (Fin rank) ℝ) :=
  symmetricSubmodule rank ⊓ LinearMap.ker (Matrix.traceLinearMap (Fin rank) ℝ ℝ)

/-- **The traceless second-moment space over the complexes** at rank `rank`. -/
noncomputable def hermitianTracelessSubmodule (rank : ℕ) :
    Submodule ℝ (Matrix (Fin rank) (Fin rank) ℂ) :=
  hermitianSubmodule rank ⊓ LinearMap.ker (Matrix.traceLinearMap (Fin rank) ℝ ℂ)

theorem mem_symmetricSubmodule_iff (rank : ℕ) (matrix : Matrix (Fin rank) (Fin rank) ℝ) :
    matrix ∈ symmetricSubmodule rank ↔ matrixᵀ = matrix := by
  show matrixᴴ = matrix ↔ matrixᵀ = matrix
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]

theorem mem_hermitianSubmodule_iff (rank : ℕ) (matrix : Matrix (Fin rank) (Fin rank) ℂ) :
    matrix ∈ hermitianSubmodule rank ↔ matrixᴴ = matrix :=
  Iff.rfl

theorem mem_symmetricTracelessSubmodule_iff (rank : ℕ)
    (matrix : Matrix (Fin rank) (Fin rank) ℝ) :
    matrix ∈ symmetricTracelessSubmodule rank ↔ matrixᵀ = matrix ∧ Matrix.trace matrix = 0 := by
  rw [symmetricTracelessSubmodule, Submodule.mem_inf, LinearMap.mem_ker,
    Matrix.traceLinearMap_apply]
  exact and_congr_left' (mem_symmetricSubmodule_iff rank matrix)

theorem mem_hermitianTracelessSubmodule_iff (rank : ℕ)
    (matrix : Matrix (Fin rank) (Fin rank) ℂ) :
    matrix ∈ hermitianTracelessSubmodule rank ↔ matrixᴴ = matrix ∧ Matrix.trace matrix = 0 := by
  rw [hermitianTracelessSubmodule, Submodule.mem_inf, LinearMap.mem_ker,
    Matrix.traceLinearMap_apply]
  exact Iff.rfl

/-! ## Design second moments live in that space -/

/-- Removing the trace of a symmetric matrix lands it in the traceless space. -/
theorem sub_smul_one_mem_symmetricTracelessSubmodule (rank : ℕ) (hrank : 1 ≤ rank)
    (matrix : Matrix (Fin rank) (Fin rank) ℝ) (hsymm : matrixᵀ = matrix) :
    matrix - (Matrix.trace matrix / rank) • 1 ∈ symmetricTracelessSubmodule rank := by
  have hrankne : (rank : ℝ) ≠ 0 := by
    have hpos : 0 < rank := hrank
    positivity
  rw [mem_symmetricTracelessSubmodule_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hsymm]
  · rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      smul_eq_mul, div_mul_cancel₀ _ hrankne, sub_self]

/-- The trace of a Hermitian matrix is real; the coercion of its real part returns it. -/
theorem ofReal_re_trace_eq_trace_of_hermitian (rank : ℕ)
    (matrix : Matrix (Fin rank) (Fin rank) ℂ) (hherm : matrixᴴ = matrix) :
    (((Matrix.trace matrix).re : ℝ) : ℂ) = Matrix.trace matrix := by
  have hstar : star (Matrix.trace matrix) = Matrix.trace matrix := by
    rw [← Matrix.trace_conjTranspose, hherm]
  refine Complex.conj_eq_iff_re.mp ?_
  rw [starRingEnd_apply]
  exact hstar

/-- Removing the (real) trace of a Hermitian matrix lands it in the traceless space.
The scalar is real, as it must be: the space is a real submodule. -/
theorem sub_smul_one_mem_hermitianTracelessSubmodule (rank : ℕ) (hrank : 1 ≤ rank)
    (matrix : Matrix (Fin rank) (Fin rank) ℂ) (hherm : matrixᴴ = matrix) :
    matrix - ((Matrix.trace matrix).re / rank : ℝ) • 1 ∈ hermitianTracelessSubmodule rank := by
  have hrankne : ((rank : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [mem_hermitianTracelessSubmodule_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      hherm, star_trivial]
  · rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      Complex.real_smul]
    push_cast
    rw [div_mul_cancel₀ _ hrankne, ofReal_re_trace_eq_trace_of_hermitian rank matrix hherm,
      sub_self]

/-- **The traceless second moment of a real atom** lies in the real traceless space, so
that space deserves its name.  The subtracted scalar is `leverage / rank`. -/
theorem atomMatrix_sub_smul_one_mem_symmetricTracelessSubmodule (rank : ℕ)
    (hrank : 1 ≤ rank) (atom : Fin rank → ℝ) :
    atomMatrix atom - (leverageOf atom / rank) • 1 ∈ symmetricTracelessSubmodule rank := by
  have hsymm : (atomMatrix atom)ᵀ = atomMatrix atom := by
    rw [atomMatrix, Matrix.transpose_vecMulVec]
  have hmem := sub_smul_one_mem_symmetricTracelessSubmodule rank hrank _ hsymm
  rwa [trace_atomMatrix] at hmem

theorem conjTranspose_complexAtom (rank : ℕ) (atom : Fin rank → ℂ) :
    (complexAtom atom)ᴴ = complexAtom atom := by
  ext rowIndex colIndex
  simp only [complexAtom, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, star_mul', star_star]
  ring

/-- **The traceless second moment of a complex atom** lies in the complex traceless
space.  Same statement as the real one, one field over — and it is the change of that
space's dimension, not of this membership, that decides the rank-two argument. -/
theorem complexAtom_sub_smul_one_mem_hermitianTracelessSubmodule (rank : ℕ)
    (hrank : 1 ≤ rank) (atom : Fin rank → ℂ) :
    complexAtom atom - ((Matrix.trace (complexAtom atom)).re / rank : ℝ) • 1
      ∈ hermitianTracelessSubmodule rank :=
  sub_smul_one_mem_hermitianTracelessSubmodule rank hrank _ (conjTranspose_complexAtom rank atom)

/-! ## The real count: symmetric traceless has dimension `rank (rank+1) / 2 - 1` -/

/-- The upper triangle, as an index type. -/
abbrev upperTriangleIndex (rank : ℕ) : Type := {pair : Fin rank × Fin rank // pair.1 ≤ pair.2}

/-- Twice the size of the upper triangle is `rank ^ 2 + rank`: the diagonal is counted
twice when the triangle is reflected, and reflection is a bijection.  Division-free, so
no natural-subtraction bookkeeping enters the dimension theorems. -/
theorem two_mul_card_upperTriangleIndex (rank : ℕ) :
    2 * Fintype.card (upperTriangleIndex rank) = rank ^ 2 + rank := by
  classical
  rw [Fintype.card_subtype]
  set upper := Finset.univ.filter (fun pair : Fin rank × Fin rank => pair.1 ≤ pair.2)
    with hupper
  set lower := Finset.univ.filter (fun pair : Fin rank × Fin rank => pair.2 ≤ pair.1)
    with hlower
  have hswap : lower = upper.image Prod.swap := by
    ext pair
    simp only [hupper, hlower, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    refine ⟨fun hpair => ⟨pair.swap, hpair, by simp⟩, ?_⟩
    rintro ⟨other, hother, rfl⟩
    exact hother
  have hcards : lower.card = upper.card := by
    rw [hswap, Finset.card_image_of_injective _ Prod.swap_injective]
  have hunion : upper ∪ lower = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro pair
    simp only [hupper, hlower, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact le_total pair.1 pair.2
  have hinter : (upper ∩ lower).card = rank := by
    have hdiag : upper ∩ lower
        = Finset.univ.image (fun index : Fin rank => (index, index)) := by
      ext pair
      simp only [hupper, hlower, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_image]
      refine ⟨fun hpair => ⟨pair.1, ?_⟩, ?_⟩
      · rw [Prod.ext_iff]
        exact ⟨rfl, le_antisymm hpair.1 hpair.2⟩
      · rintro ⟨index, rfl⟩
        exact ⟨le_refl _, le_refl _⟩
    rw [hdiag, Finset.card_image_of_injective _ (fun first second heq =>
      (Prod.ext_iff.mp heq).1), Finset.card_univ, Fintype.card_fin]
  have hkey := Finset.card_union_add_card_inter upper lower
  rw [hunion, hinter, hcards, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hkey
  rw [pow_two]
  omega

/-- Reflecting upper-triangle coefficients across the diagonal. -/
def symmetrizeUpperTriangle (rank : ℕ) :
    (upperTriangleIndex rank → ℝ) →ₗ[ℝ] Matrix (Fin rank) (Fin rank) ℝ where
  toFun coeff := Matrix.of fun rowIndex colIndex =>
    if hle : rowIndex ≤ colIndex then coeff ⟨(rowIndex, colIndex), hle⟩
    else coeff ⟨(colIndex, rowIndex), (not_le.mp hle).le⟩
  map_add' first second := by
    ext rowIndex colIndex
    by_cases hle : rowIndex ≤ colIndex <;> simp [hle]
  map_smul' scalar coeff := by
    ext rowIndex colIndex
    by_cases hle : rowIndex ≤ colIndex <;> simp [hle]

theorem symmetrizeUpperTriangle_apply (rank : ℕ) (coeff : upperTriangleIndex rank → ℝ)
    (entryIndex : upperTriangleIndex rank) :
    symmetrizeUpperTriangle rank coeff entryIndex.1.1 entryIndex.1.2 = coeff entryIndex := by
  obtain ⟨⟨rowIndex, colIndex⟩, hle⟩ := entryIndex
  simp only [symmetrizeUpperTriangle, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  rw [dif_pos hle]

theorem injective_symmetrizeUpperTriangle (rank : ℕ) :
    Function.Injective (symmetrizeUpperTriangle rank) := by
  intro first second heq
  funext entryIndex
  rw [← symmetrizeUpperTriangle_apply rank first entryIndex,
    ← symmetrizeUpperTriangle_apply rank second entryIndex, heq]

theorem range_symmetrizeUpperTriangle_eq_symmetricSubmodule (rank : ℕ) :
    LinearMap.range (symmetrizeUpperTriangle rank) = symmetricSubmodule rank := by
  apply le_antisymm
  · rintro matrix ⟨coeff, rfl⟩
    rw [mem_symmetricSubmodule_iff]
    ext rowIndex colIndex
    simp only [Matrix.transpose_apply, symmetrizeUpperTriangle, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.of_apply]
    rcases le_total rowIndex colIndex with hle | hge
    · rcases eq_or_lt_of_le hle with rfl | hlt
      · rfl
      · rw [dif_pos hle, dif_neg (not_le_of_gt hlt)]
    · rcases eq_or_lt_of_le hge with rfl | hlt
      · rfl
      · rw [dif_pos hge, dif_neg (not_le_of_gt hlt)]
  · intro matrix hmember
    have hsymm : matrixᵀ = matrix := (mem_symmetricSubmodule_iff rank matrix).mp hmember
    refine ⟨fun entryIndex => matrix entryIndex.1.1 entryIndex.1.2, ?_⟩
    ext rowIndex colIndex
    simp only [symmetrizeUpperTriangle, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
    by_cases hle : rowIndex ≤ colIndex
    · rw [dif_pos hle]
    · rw [dif_neg hle]
      exact congrFun (congrFun hsymm rowIndex) colIndex

/-- **The real symmetric dimension**, division-free: `2 dim = rank ^ 2 + rank`. -/
theorem two_mul_finrank_symmetricSubmodule (rank : ℕ) :
    2 * Module.finrank ℝ (symmetricSubmodule rank) = rank ^ 2 + rank := by
  have hrange : Module.finrank ℝ (LinearMap.range (symmetrizeUpperTriangle rank))
      = Module.finrank ℝ (upperTriangleIndex rank → ℝ) :=
    LinearMap.finrank_range_of_inj (injective_symmetrizeUpperTriangle rank)
  rw [range_symmetrizeUpperTriangle_eq_symmetricSubmodule] at hrange
  rw [hrange, Module.finrank_fintype_fun_eq_card, two_mul_card_upperTriangleIndex]

/-! ## The complex count: Hermitian has dimension `rank ^ 2` -/

/-- Multiplication by `-i` is a real-linear bijection from skew-adjoint to self-adjoint
matrices, so the two halves of the star decomposition have equal real dimension. -/
theorem finrank_skewAdjoint_eq_finrank_selfAdjoint (rank : ℕ) :
    Module.finrank ℝ (skewAdjoint (Matrix (Fin rank) (Fin rank) ℂ))
      = Module.finrank ℝ (selfAdjoint (Matrix (Fin rank) (Fin rank) ℂ)) := by
  have hinj : Function.Injective
      (skewAdjoint.negISMul (A := Matrix (Fin rank) (Fin rank) ℂ)) := by
    intro first second heq
    have hcoe : Complex.I • (skewAdjoint.negISMul first : Matrix (Fin rank) (Fin rank) ℂ)
        = Complex.I • (skewAdjoint.negISMul second : Matrix (Fin rank) (Fin rank) ℂ) := by
      rw [heq]
    rw [skewAdjoint.I_smul_neg_I, skewAdjoint.I_smul_neg_I] at hcoe
    exact Subtype.ext hcoe
  have hsurj : Function.Surjective
      (skewAdjoint.negISMul (A := Matrix (Fin rank) (Fin rank) ℂ)) := by
    intro target
    refine ⟨⟨Complex.I • (target : Matrix (Fin rank) (Fin rank) ℂ), ?_⟩, ?_⟩
    · rw [Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint]
      exact target.2
    · apply Subtype.ext
      show -Complex.I • Complex.I • (target : Matrix (Fin rank) (Fin rank) ℂ) = target
      rw [smul_smul]
      norm_num
  exact (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).finrank_eq

/-- **The complex Hermitian dimension**: `rank ^ 2`, half of the real dimension
`2 rank ^ 2` of the complex matrices. -/
theorem finrank_hermitianSubmodule (rank : ℕ) :
    Module.finrank ℝ (hermitianSubmodule rank) = rank ^ 2 := by
  haveI : FiniteDimensional ℝ (selfAdjoint (Matrix (Fin rank) (Fin rank) ℂ)) :=
    inferInstanceAs
      (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix (Fin rank) (Fin rank) ℂ)))
  haveI : FiniteDimensional ℝ (skewAdjoint (Matrix (Fin rank) (Fin rank) ℂ)) :=
    inferInstanceAs
      (FiniteDimensional ℝ (skewAdjoint.submodule ℝ (Matrix (Fin rank) (Fin rank) ℂ)))
  have hsplit : Module.finrank ℝ (Matrix (Fin rank) (Fin rank) ℂ)
      = Module.finrank ℝ (selfAdjoint (Matrix (Fin rank) (Fin rank) ℂ))
        + Module.finrank ℝ (skewAdjoint (Matrix (Fin rank) (Fin rank) ℂ)) := by
    rw [(StarModule.decomposeProdAdjoint ℝ (Matrix (Fin rank) (Fin rank) ℂ)).finrank_eq,
      Module.finrank_prod]
  have hambient : Module.finrank ℝ (Matrix (Fin rank) (Fin rank) ℂ) = rank * rank * 2 := by
    rw [Module.finrank_matrix, Complex.finrank_real_complex, Fintype.card_fin]
  have hself : Module.finrank ℝ (selfAdjoint (Matrix (Fin rank) (Fin rank) ℂ))
      = Module.finrank ℝ (hermitianSubmodule rank) := rfl
  rw [finrank_skewAdjoint_eq_finrank_selfAdjoint, hself, hambient] at hsplit
  rw [pow_two]
  omega

/-! ## Removing the trace costs exactly one dimension -/

theorem sup_span_one_symmetricTracelessSubmodule (rank : ℕ) (hrank : 1 ≤ rank) :
    symmetricTracelessSubmodule rank
        ⊔ Submodule.span ℝ {(1 : Matrix (Fin rank) (Fin rank) ℝ)}
      = symmetricSubmodule rank := by
  apply le_antisymm
  · rw [sup_le_iff]
    refine ⟨inf_le_left, ?_⟩
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      mem_symmetricSubmodule_iff]
    exact Matrix.transpose_one
  · intro matrix hmember
    have hsymm : matrixᵀ = matrix := (mem_symmetricSubmodule_iff rank matrix).mp hmember
    rw [Submodule.mem_sup]
    exact ⟨matrix - (Matrix.trace matrix / rank) • 1,
      sub_smul_one_mem_symmetricTracelessSubmodule rank hrank matrix hsymm,
      (Matrix.trace matrix / rank) • 1,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), by abel⟩

theorem sup_span_one_hermitianTracelessSubmodule (rank : ℕ) (hrank : 1 ≤ rank) :
    hermitianTracelessSubmodule rank
        ⊔ Submodule.span ℝ {(1 : Matrix (Fin rank) (Fin rank) ℂ)}
      = hermitianSubmodule rank := by
  apply le_antisymm
  · rw [sup_le_iff]
    refine ⟨inf_le_left, ?_⟩
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      mem_hermitianSubmodule_iff]
    exact Matrix.conjTranspose_one
  · intro matrix hmember
    have hherm : matrixᴴ = matrix := (mem_hermitianSubmodule_iff rank matrix).mp hmember
    rw [Submodule.mem_sup]
    exact ⟨matrix - ((Matrix.trace matrix).re / rank : ℝ) • 1,
      sub_smul_one_mem_hermitianTracelessSubmodule rank hrank matrix hherm,
      ((Matrix.trace matrix).re / rank : ℝ) • 1,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), by abel⟩

/-- **The real traceless dimension**, division-free and subtraction-free. -/
theorem two_mul_finrank_symmetricTracelessSubmodule_add_two (rank : ℕ) (hrank : 1 ≤ rank) :
    2 * Module.finrank ℝ (symmetricTracelessSubmodule rank) + 2 = rank ^ 2 + rank := by
  have hnotmem : (1 : Matrix (Fin rank) (Fin rank) ℝ) ∉ symmetricTracelessSubmodule rank := by
    rw [mem_symmetricTracelessSubmodule_iff]
    intro hcontra
    have hzero : (rank : ℝ) = 0 := by
      have htrace := hcontra.2
      rwa [Matrix.trace_one, Fintype.card_fin] at htrace
    have hpos : 0 < rank := hrank
    exact absurd hzero (by positivity)
  have hstep : Module.finrank ℝ (symmetricTracelessSubmodule rank) + 1
      = Module.finrank ℝ (symmetricSubmodule rank) := by
    rw [← sup_span_one_symmetricTracelessSubmodule rank hrank,
      Submodule.finrank_sup_span_singleton hnotmem]
  have hfull := two_mul_finrank_symmetricSubmodule rank
  omega

/-- **The complex traceless dimension**, subtraction-free. -/
theorem finrank_hermitianTracelessSubmodule_add_one (rank : ℕ) (hrank : 1 ≤ rank) :
    Module.finrank ℝ (hermitianTracelessSubmodule rank) + 1 = rank ^ 2 := by
  have hnotmem : (1 : Matrix (Fin rank) (Fin rank) ℂ) ∉ hermitianTracelessSubmodule rank := by
    rw [mem_hermitianTracelessSubmodule_iff]
    intro hcontra
    have hzero : ((rank : ℂ)) = 0 := by
      have htrace := hcontra.2
      rwa [Matrix.trace_one, Fintype.card_fin] at htrace
    exact absurd hzero (Nat.cast_ne_zero.mpr (by omega))
  have hstep : Module.finrank ℝ (hermitianTracelessSubmodule rank) + 1
      = Module.finrank ℝ (hermitianSubmodule rank) := by
    rw [← sup_span_one_hermitianTracelessSubmodule rank hrank,
      Submodule.finrank_sup_span_singleton hnotmem]
  rw [hstep, finrank_hermitianSubmodule]

/-- The real traceless dimension in the paper's closed form. -/
theorem finrank_symmetricTracelessSubmodule (rank : ℕ) (hrank : 1 ≤ rank) :
    Module.finrank ℝ (symmetricTracelessSubmodule rank) = rank * (rank + 1) / 2 - 1 := by
  have hkey := two_mul_finrank_symmetricTracelessSubmodule_add_two rank hrank
  have hprod : rank * (rank + 1) = rank ^ 2 + rank := by ring
  rw [hprod]
  omega

/-- The complex traceless dimension in the paper's closed form. -/
theorem finrank_hermitianTracelessSubmodule (rank : ℕ) (hrank : 1 ≤ rank) :
    Module.finrank ℝ (hermitianTracelessSubmodule rank) = rank ^ 2 - 1 := by
  have hkey := finrank_hermitianTracelessSubmodule_add_one rank hrank
  omega

/-! ## The three instances -/

/-- `n = 2` over the reals at rank two. -/
theorem finrank_symmetricTracelessSubmodule_atRankTwo :
    Module.finrank ℝ (symmetricTracelessSubmodule 2) = 2 := by
  have hkey := two_mul_finrank_symmetricTracelessSubmodule_add_two 2 (by norm_num)
  norm_num at hkey
  omega

/-- `n = 3` over the complexes at rank two — the Bloch sphere. -/
theorem finrank_hermitianTracelessSubmodule_atRankTwo :
    Module.finrank ℝ (hermitianTracelessSubmodule 2) = 3 := by
  have hkey := finrank_hermitianTracelessSubmodule_add_one 2 (by norm_num)
  norm_num at hkey
  omega

/-- `n = 5` over the reals at rank three. -/
theorem finrank_symmetricTracelessSubmodule_atRankThree :
    Module.finrank ℝ (symmetricTracelessSubmodule 3) = 5 := by
  have hkey := two_mul_finrank_symmetricTracelessSubmodule_add_two 3 (by norm_num)
  norm_num at hkey
  omega

/-- **The reals at rank two: an EQUALITY.**  `2 n = 4 = k ^ 2`, with nothing to spare.
This is the coincidence the shipped `rw [hT, ← htrsig]` of
`Gtz/Reduction/RankTwo.lean:539` rests on. -/
theorem twiceFinrank_symmetricTracelessSubmodule_eq_sq_atRankTwo :
    2 * Module.finrank ℝ (symmetricTracelessSubmodule 2) = 2 ^ 2 := by
  rw [finrank_symmetricTracelessSubmodule_atRankTwo]
  norm_num

/-- **The complexes at rank two: a deficit of exactly two.** -/
theorem twiceFinrank_hermitianTracelessSubmodule_eq_sq_add_two_atRankTwo :
    2 * Module.finrank ℝ (hermitianTracelessSubmodule 2) = 2 ^ 2 + 2 := by
  rw [finrank_hermitianTracelessSubmodule_atRankTwo]
  norm_num

/-- **The reals at rank three: a deficit of exactly one.**  The narrowest possible
failure of the budget, and the reason the transported step misses by one dimension. -/
theorem twiceFinrank_symmetricTracelessSubmodule_eq_sq_add_one_atRankThree :
    2 * Module.finrank ℝ (symmetricTracelessSubmodule 3) = 3 ^ 2 + 1 := by
  rw [finrank_symmetricTracelessSubmodule_atRankThree]
  norm_num

theorem isWithinAdjugatePairingBudget_symmetricTracelessSubmodule_atRankTwo :
    IsWithinAdjugatePairingBudget (Module.finrank ℝ (symmetricTracelessSubmodule 2)) 2 := by
  rw [IsWithinAdjugatePairingBudget, twiceFinrank_symmetricTracelessSubmodule_eq_sq_atRankTwo]

theorem not_isWithinAdjugatePairingBudget_hermitianTracelessSubmodule_atRankTwo :
    ¬ IsWithinAdjugatePairingBudget
        (Module.finrank ℝ (hermitianTracelessSubmodule 2)) 2 := by
  rw [IsWithinAdjugatePairingBudget,
    twiceFinrank_hermitianTracelessSubmodule_eq_sq_add_two_atRankTwo]
  norm_num

theorem not_isWithinAdjugatePairingBudget_symmetricTracelessSubmodule_atRankThree :
    ¬ IsWithinAdjugatePairingBudget
        (Module.finrank ℝ (symmetricTracelessSubmodule 3)) 3 := by
  rw [IsWithinAdjugatePairingBudget,
    twiceFinrank_symmetricTracelessSubmodule_eq_sq_add_one_atRankThree]
  norm_num

/-- **The full real classification**: over the reals the adjugate-pairing budget holds
exactly at ranks one and two. -/
theorem isWithinAdjugatePairingBudget_symmetricTracelessSubmodule_iff (rank : ℕ)
    (hrank : 1 ≤ rank) :
    IsWithinAdjugatePairingBudget
        (Module.finrank ℝ (symmetricTracelessSubmodule rank)) rank ↔ rank ≤ 2 := by
  have hkey := two_mul_finrank_symmetricTracelessSubmodule_add_two rank hrank
  rw [IsWithinAdjugatePairingBudget]
  omega

/-- **The full complex classification**: over the complexes the budget holds only at
rank one, where the problem is empty. -/
theorem isWithinAdjugatePairingBudget_hermitianTracelessSubmodule_iff (rank : ℕ)
    (hrank : 1 ≤ rank) :
    IsWithinAdjugatePairingBudget
        (Module.finrank ℝ (hermitianTracelessSubmodule rank)) rank ↔ rank ≤ 1 := by
  have hkey := finrank_hermitianTracelessSubmodule_add_one rank hrank
  have hsquare : rank ^ 2 ≤ 2 ↔ rank ≤ 1 := by
    constructor
    · intro hle
      by_contra hgt
      have htwo : 2 ≤ rank := by omega
      have hpow : 2 ^ 2 ≤ rank ^ 2 := Nat.pow_le_pow_left htwo 2
      omega
    · intro hle
      have hpow : rank ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left hle 2
      omega
  rw [IsWithinAdjugatePairingBudget]
  omega

/-! ## The complex SIC, as a number -/

/-- **The Bloch second-moment operator of the complex SIC in dimension two.**  The four
SIC lines of `Gtz.sicAtom` carry uniform weight `1/4`, hence equal leverage `2`; their
traceless parts `g_c g_cᴴ - I` have squared Frobenius norm `2` and their directions are
a regular tetrahedron, so `Sum_c t_c M_c M_cᵀ = (2/3) I_3` in a Frobenius-orthonormal
basis of the three-dimensional traceless Hermitian space.  Under the double-angle
normalization `|w_c| ^ 2 = leverage_c ^ 2` — `w_c = sqrt 2 . M_c`, the same convention
the shipped rank-two argument uses — the operator is `(4/3) I_3`, and `tr Omega = 4`
agrees with `Sum_c t_c leverage_c ^ 2 = 4`.  That the numeral below IS that operator is
arithmetic recorded here and NOT mechanized; the theorems are about the matrix. -/
noncomputable def complexSicBlochMoment : Matrix (Fin 3) (Fin 3) ℝ := (4 / 3 : ℝ) • 1

theorem det_complexSicBlochMoment : complexSicBlochMoment.det = 64 / 27 := by
  rw [complexSicBlochMoment, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
  norm_num

theorem trace_complexSicBlochMoment : Matrix.trace complexSicBlochMoment = 4 := by
  rw [complexSicBlochMoment, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul]
  norm_num

/-- **The step fails at the complex SIC, with an exact value.**  Every leverage equals
the rank, so the centred moment vanishes and the Schur bound is tight at zero; what is
left is `det (tr - 2 n) = (64/27)(4 - 6) = -128/27`, entirely the dimension deficit of
`twiceFinrank_hermitianTracelessSubmodule_eq_sq_add_two_atRankTwo`.  This exhibits one
point at which the conclusion of
`trace_adjugate_mul_adjugatePairingForm_nonneg_of_isWithinAdjugatePairingBudget` fails
outside the budget; it does not claim the conclusion fails at every such point. -/
theorem trace_adjugate_mul_adjugatePairingForm_complexSicBlochMoment :
    Matrix.trace
        (complexSicBlochMoment.adjugate * adjugatePairingForm complexSicBlochMoment 0)
      = -128 / 27 := by
  rw [trace_adjugate_mul_adjugatePairingForm, det_complexSicBlochMoment,
    trace_complexSicBlochMoment, zero_dotProduct]
  norm_num

theorem trace_adjugate_mul_adjugatePairingForm_complexSicBlochMoment_neg :
    Matrix.trace
        (complexSicBlochMoment.adjugate * adjugatePairingForm complexSicBlochMoment 0) < 0 := by
  rw [trace_adjugate_mul_adjugatePairingForm_complexSicBlochMoment]
  norm_num

end Gtz

/-
# GTZ over ℂ, per rank: the two-sided ledger

Over ℝ the Goreinov–Tyrtyshnikov–Zamarashkin problem is a yes/no question: does
every weighted `(m,k)`-design have a `k`-subset `C` with `Σ_{c ∈ C} g_c g_c* ⪰ I`?
Over ℂ the answer is NO from rank two on, so the right object is not a Boolean
but a NUMBER, one per rank:

  `alpha_k := inf over complex weighted (m,k)-designs, over all m,
              of  max over k-subsets C of  lambda_min (Σ_{c ∈ C} g_c g_c*)`.

Real GTZ says the real analogue is `1`.  This file gives `alpha_k` two-sided
bounds, and the ledger below states exactly which end of which rank is a theorem.

## THE LEDGER

Tags: PROVED-LOWER / PROVED-UPPER = kernel-checked in THIS file.  CITED = a
published theorem, not mechanized.  MEASURED = a floating-point optimum.  OPEN =
nobody knows.

* **rank k, every k** — PROVED-LOWER `alpha_k ≥ 1/k`
  (`complexRankConstantAtLeast_rankInverse`).  Maximal volume: pick the `k`-subset
  of maximal `|det|` on the conjugated atom rows, bound its solve coefficients by
  Cramer's rule, apply Parseval.  Field-blind, weight-free, independent of `m`.
  Prior art: Goreinov–Tyrtyshnikov pseudoskeleton theory; the real mechanism is
  in `Gtz/Reduction/MaximalVolume.lean` and never used realness.

* **rank 1** — CLOSED.  PROVED-LOWER `1` (`complexGtzWeighted_rankOne`: Parseval
  in `ℂ¹` is a weighted average, so one atom already dominates) and PROVED-UPPER
  `1` (`unitRankOneDesign`, the single unit atom).  So `alpha_1 = 1`, and the
  rank-inverse bound is SHARP at `k = 1` and only there.

* **rank 2** — PROVED-LOWER `1/2`; PROVED-UPPER `2 - 2/sqrt 3 = 0.8452994616…`,
  witnessed by the `ℂ²` SIC at `m = 4` (`sicDesign`, uniform weight `1/4`, every
  leverage exactly `2`, cap `κ = 1`), via `complexRankConstantAtMost_two_sic`.
  Gap: a factor `1.6906`.  CITED: that upper end is EXACT — Nesterenko,
  arXiv:2604.24087, Proposition 1, with equality iff `4 ∣ m` and the rows' Hopf
  images cluster at the vertices of a regular tetrahedron, i.e. the `ℂ²` SIC.
  The real analogue `alpha_2^ℝ = 1` is Sengupta–Pautov, arXiv:2604.05944, in the
  orthonormal-columns form; the weighted form is this campaign's own reduction,
  not the paper's statement.  Neither citation is mechanized, so the PROVED
  content at rank two is the window, not the constant.

* **rank 3** — PROVED-LOWER `1/3`; PROVED-UPPER `3(1 - cos 2 pi / 9) =
  0.7018666706…`, the least root of `8x³ - 72x² + 162x - 81`, witnessed by the
  Hesse SIC at `m = 9` (`hesseDesign`: nine equiangular lines in `ℂ³`, uniform
  weight `1/9`, every leverage exactly `3`, cap `κ = 1`, all Gram data in
  `ℤ[ω]`), via `complexRankConstantAtMost_three_hesse`.  Gap: a factor `2.1056`.
  The shared-axis trine of `Gtz/Complex/SharpConstantLedger.lean` sits strictly
  ABOVE at `3 - sqrt 5 = 0.7639320225…` (`hesseMargin_lt_trineMargin`, margin
  `0.0621`), so the trine is not the rank-3 record; its value IS pinned exactly,
  in Loewner form (`trineMargin_isGreatest`), which the ledger there carried only
  as an audited reading.  MEASURED: no design below `0.701867` was found at any
  `m ≤ 13`, so `3(1 - cos 2 pi / 9)` is the record, not a proved infimum.

* **ranks ≥ 4** — PROVED-LOWER `1/k` and NOTHING ELSE HERE.  No rank-4 or rank-5
  design is mechanized anywhere in this repository; the constants recorded in
  `Gtz/Complex/SharpConstantLedger.lean` are MEASURED.  Upper bounds at these
  ranks are OPEN in this file.

* **the real side, rank ≥ 3** — OPEN in the literature.  Sengupta–Pautov state
  their own problem as open for all `1 < k < n - 1` except `(n,k) = (4,2)`.

Nothing here computes `alpha_k` for any `k ≥ 2`.  The single smallest hole is
stated at the end, in the SCOPE NOTE.

## Provenance of the three parts

This file merges three audited deliverables, each with its adversarial-audit
defects applied.

**Part A — the lower bound.**  Let `A` be the `m × k` matrix of CONJUGATED atom
rows and `D = diag t`.  Parseval is exactly `Aᴴ D A = 1`, the projection
coefficient `⟨g_c, x⟩` is the `c`-th entry of `A x`, and the subset atom sum
along an injective pick is `MᴴM` for `M = A_pick`.  At the pick of maximal
`|det M|`, Cramer's rule forces every entry of `B = A M⁻¹` to have modulus at
most one; Cauchy–Schwarz then gives `|(B u)_c|² ≤ k |u|²`, and substituting
`u = M x` plus Parseval gives `|x|² ≤ k |M x|²`.  Splitting the weighted total
over the selected atoms and the rest sharpens `k` to `k - (k-1) w`.

**Part B — the trine, exactly.**  At the shift `3 - sqrt 5` a mixed triple's
excess is a nonnegative combination of exactly two rank-one atoms, so it is
positive semidefinite; above that shift all twenty triples fail, and the argument
NEEDS TWO REGIONS — the mixed characteristic polynomial `(3-z)(z²-6z+4)` is
POSITIVE on `(3, 3+sqrt 5)`, where the matrix nevertheless has two negative
eigenvalues, so a determinant certificate alone does not establish the claim.

**Part C — the Hesse SIC.**  Every distinct pairing of the nine Eisenstein
directions is a cube root of `-1`, so every atom overlap cubes to `-27/8`; the
modulus `9/4` follows because a nonnegative real is pinned by its cube, and the
Bargmann triangle invariant cubes to `-(27/8)³`, forcing `Re T ≤ 27/16`.  That
single bound kills all eighty-four triples at once through the repo's own
`gramTripleExcess_det_split`.  At shift `1` the cubic is `17`, so weighted
`(9,3)` is FALSE over ℂ.

## Landing note

This module SUPERSEDES the untracked working file
`Gtz/Complex/TrineLeastness.lean`, with which it shares seventeen declaration
names.  Wiring both breaks the build; wire this one.
-/

import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Complex.ComplexWitness
import Gtz.Complex.ComplexPadding
import Gtz.Complex.SharpConstantLedger

namespace Gtz

open Matrix Complex
open scoped ComplexOrder

set_option maxHeartbeats 1000000

/-! # Part A. The field-blind lower bound: every design reaches `1/k`

The complex ledger of this repository was entirely UPPER bounds — witnesses
showing the constant cannot be raised.  This part supplies the other side, at
every rank and with no hypothesis at all.  Nothing in the argument sees that the
scalars are complex. -/

section RankInverseLowerBound

variable {m k : ℕ}

/-! ## Parseval as a weighted average of squared projections -/

/-- Conjugating the dot product swaps its arguments. -/
theorem starDot_swap (leftVec rightVec : Fin k → ℂ) :
    star leftVec ⬝ᵥ rightVec = (starRingEnd ℂ) (star rightVec ⬝ᵥ leftVec) := by
  simp only [dotProduct, Pi.star_apply, map_sum, map_mul, RCLike.star_def,
    Complex.conj_conj]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- A rank-one atom acts on a direction by scaling the atom vector by the
projection coefficient. -/
theorem complexAtom_mulVec (atomVector direction : Fin k → ℂ) :
    complexAtom atomVector *ᵥ direction
      = (star atomVector ⬝ᵥ direction) • atomVector := by
  funext coord
  simp only [complexAtom, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
    Pi.star_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **The quadratic form of a complex rank-one atom** is the squared modulus of
the projection on that atom. -/
theorem quadForm_complexAtom (atomVector direction : Fin k → ℂ) :
    star direction ⬝ᵥ (complexAtom atomVector *ᵥ direction)
      = ((Complex.normSq (star atomVector ⬝ᵥ direction) : ℝ) : ℂ) := by
  rw [complexAtom_mulVec, dotProduct_smul, smul_eq_mul,
    starDot_swap direction atomVector]
  exact Complex.mul_conj _

/-- **Complex Parseval in quadratic-form shape**: the weighted squared moduli of
the projections on the atoms total the squared length of the direction. -/
theorem complexParseval_quadForm (design : ComplexWeightedDesign m k)
    (direction : Fin k → ℂ) :
    (Finset.univ.sum fun atomLabel => ((design.weight atomLabel : ℝ) : ℂ)
        * ((Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction) : ℝ) : ℂ))
      = star direction ⬝ᵥ direction := by
  have hstep : star direction ⬝ᵥ
        ((Finset.univ.sum fun atomLabel => ((design.weight atomLabel : ℝ) : ℂ)
          • complexAtom (design.atom atomLabel)) *ᵥ direction)
      = star direction ⬝ᵥ ((1 : Matrix (Fin k) (Fin k) ℂ) *ᵥ direction) := by
    rw [design.isParseval]
  rw [Matrix.one_mulVec] at hstep
  rw [← hstep, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun atomLabel _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, quadForm_complexAtom]

/-- The same statement over the reals: `∑ t_c |<g_c, x>|^2 = |x|^2`. -/
theorem complexParseval_normSq (design : ComplexWeightedDesign m k)
    (direction : Fin k → ℂ) :
    (Finset.univ.sum fun atomLabel =>
        design.weight atomLabel * Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction))
      = Finset.univ.sum fun coord => Complex.normSq (direction coord) := by
  have hcomplex := complexParseval_quadForm design direction
  have hright : star direction ⬝ᵥ direction
      = (((Finset.univ.sum fun coord => Complex.normSq (direction coord)) : ℝ)
        : ℂ) := by
    push_cast
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
    exact Finset.sum_congr rfl fun coord _ => by
      rw [mul_comm]; exact Complex.mul_conj _
  rw [hright] at hcomplex
  have hleft : (((Finset.univ.sum fun atomLabel => design.weight atomLabel
        * Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction)) : ℝ) : ℂ)
      = Finset.univ.sum fun atomLabel => ((design.weight atomLabel : ℝ) : ℂ)
        * ((Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [← hleft] at hcomplex
  exact_mod_cast hcomplex

/-- The squared length of a direction, as a real cast. -/
theorem starDot_self_eq_sumNormSq (direction : Fin k → ℂ) :
    star direction ⬝ᵥ direction
      = (((∑ coord, Complex.normSq (direction coord)) : ℝ) : ℂ) := by
  push_cast
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  exact Finset.sum_congr rfl fun coord _ => by
    rw [mul_comm]; exact Complex.mul_conj _

/-! ## From a projection inequality to a Loewner bound -/

/-- A complex rank-one atom is positive semidefinite. -/
theorem complexAtom_posSemidef (atomVector : Fin k → ℂ) :
    (complexAtom atomVector).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star atomVector

/-- An atom sum is positive semidefinite. -/
theorem posSemidef_atomSum (design : ComplexWeightedDesign m k) (selection : Finset (Fin m)) :
    (∑ atomLabel ∈ selection, complexAtom (design.atom atomLabel)).PosSemidef := by
  classical
  refine Finset.sum_induction _ _ (fun left right hleft hright => hleft.add hright)
    Matrix.PosSemidef.zero ?_
  intro atomLabel _
  exact complexAtom_posSemidef (design.atom atomLabel)

/-- **The packaging lemma.** A subset's atom sum dominates `level · I` exactly
when the squared projections on the subset's atoms cover `level` times the
squared length of every direction. This is the only place positive
semidefiniteness is unfolded; everything downstream is a real inequality on
projection coefficients. -/
theorem posSemidef_atomSum_sub_smul_one (design : ComplexWeightedDesign m k)
    (selection : Finset (Fin m)) (level : ℝ)
    (hcovers : ∀ direction : Fin k → ℂ,
      level * (∑ coord, Complex.normSq (direction coord))
        ≤ ∑ atomLabel ∈ selection, Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction)) :
    ((∑ atomLabel ∈ selection, complexAtom (design.atom atomLabel)) - ((level : ℝ) : ℂ)
      • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun direction => ?_⟩
  · exact (posSemidef_atomSum design selection).isHermitian.sub
      (Matrix.isHermitian_one.smul (isSelfAdjoint_iff.mpr (by simp)))
  · rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum,
      Matrix.smul_mulVec, dotProduct_smul, Matrix.one_mulVec, smul_eq_mul,
      starDot_self_eq_sumNormSq]
    have hterms : (∑ atomLabel ∈ selection,
          star direction ⬝ᵥ (complexAtom (design.atom atomLabel) *ᵥ direction))
        = (((∑ atomLabel ∈ selection,
            Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction)) : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun atomLabel _ =>
        quadForm_complexAtom (design.atom atomLabel) direction
    rw [hterms]
    have hreal : (((∑ atomLabel ∈ selection,
            Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction)) : ℝ) : ℂ)
        - ((level : ℝ) : ℂ) * (((∑ coord, Complex.normSq (direction coord)) : ℝ) : ℂ)
        = (((∑ atomLabel ∈ selection,
              Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction))
            - level * (∑ coord, Complex.normSq (direction coord)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hreal, Complex.zero_le_real]
    linarith [hcovers direction]

/-! ## Rank one: the sharp constant is `1` -/

/-- A complex weighted design has at least one atom: the weights sum to one,
which is impossible over an empty index. -/
theorem complexSize_pos (design : ComplexWeightedDesign m k) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with hzero | hpos
  · exfalso
    subst hzero
    have hsum := design.weight_sum_one
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact absurd hsum (by norm_num)
  · exact hpos

/-- **The caps cover every direction, over ℂ.** The field-blind port of
`exists_atom_covering_direction`: Parseval makes `∑_c t_c |⟨g_c, x⟩|² = |x|²` a
genuine weighted average of the squared projections, and a weighted average
never lies strictly below every one of its terms. No convex separation, no
spectral theory, and all-heaviness is never used. -/
theorem exists_atom_covering_direction_complex (design : ComplexWeightedDesign m k)
    (direction : Fin k → ℂ) :
    ∃ coveringAtom : Fin m,
      (∑ coord, Complex.normSq (direction coord))
        ≤ Complex.normSq (star (design.atom coveringAtom) ⬝ᵥ direction) := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (complexSize_pos design)
  by_contra hnoCover
  rw [not_exists] at hnoCover
  simp only [not_le] at hnoCover
  have hstrict :
      (∑ atomLabel, design.weight atomLabel
          * Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction))
        < ∑ _unused : Fin m,
            design.weight _unused * (∑ coord, Complex.normSq (direction coord)) := by
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty ?_
    intro atomLabel _
    exact mul_lt_mul_of_pos_left (hnoCover atomLabel) (design.weight_pos atomLabel)
  rw [← Finset.sum_mul, design.weight_sum_one, one_mul,
    complexParseval_normSq design direction] at hstrict
  exact lt_irrefl _ hstrict

/-- **`α₁ = 1` over ℂ, and the maximal-volume constant `1/k` is sharp at `k = 1`.**
In `ℂ¹` Parseval makes `|g_c|²` a weighted average of value one, so some single
atom already has `|g_c|² ≥ 1` and its rank-one projector dominates the identity.
Vacuous at `m = 0`, where the weights cannot sum to one. -/
theorem complexGtzWeighted_rankOne (size : ℕ) : ComplexGtzWeighted size 1 := by
  intro design
  obtain ⟨coveringAtom, hcovers⟩ :=
    exists_atom_covering_direction_complex design (fun _ => (1 : ℂ))
  rw [Fin.sum_univ_one] at hcovers
  simp only [Complex.normSq_one] at hcovers
  have hleverage : (1 : ℝ) ≤ Complex.normSq (design.atom coveringAtom 0) := by
    have hvalue : star (design.atom coveringAtom) ⬝ᵥ (fun _ => (1 : ℂ))
        = (starRingEnd ℂ) (design.atom coveringAtom 0) := by
      simp [dotProduct, RCLike.star_def]
    rwa [hvalue, Complex.normSq_conj] at hcovers
  refine ⟨{coveringAtom}, Finset.card_singleton _, ?_⟩
  have hpsd := posSemidef_atomSum_sub_smul_one design {coveringAtom} 1 ?_
  · rw [Complex.ofReal_one, one_smul] at hpsd
    exact hpsd
  · intro direction
    have hproject : Complex.normSq (star (design.atom coveringAtom) ⬝ᵥ direction)
        = Complex.normSq (design.atom coveringAtom 0) * Complex.normSq (direction 0) := by
      have hvalue : star (design.atom coveringAtom) ⬝ᵥ direction
          = (starRingEnd ℂ) (design.atom coveringAtom 0) * direction 0 := by
        simp [dotProduct, RCLike.star_def]
      rw [hvalue, Complex.normSq_mul, Complex.normSq_conj]
    rw [Finset.sum_singleton, hproject, Fin.sum_univ_one, one_mul]
    nlinarith [Complex.normSq_nonneg (direction 0), hleverage]

/-! ## The design as a frame on the index space -/

/-- **The conjugated atom rows.** The `m × k` matrix whose `(c, i)` entry is
`conj (g_c i)`. Parseval becomes `Aᴴ · diag t · A = 1` and the projection
coefficient `⟨g_c, x⟩` becomes the `c`-th entry of `A x`, so no transpose ever
appears on the atom side. -/
def conjugateAtomRows (design : ComplexWeightedDesign m k) : Matrix (Fin m) (Fin k) ℂ :=
  Matrix.of fun atomIndex coord => (starRingEnd ℂ) (design.atom atomIndex coord)

/-- The weights on the diagonal of the index space. -/
noncomputable def weightDiagonal (design : ComplexWeightedDesign m k) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.diagonal fun atomIndex => ((design.weight atomIndex : ℝ) : ℂ)

/-- Applying the conjugated atom rows to a direction reads off the projection
coefficients. -/
theorem conjugateAtomRows_mulVec (design : ComplexWeightedDesign m k)
    (direction : Fin k → ℂ) (atomIndex : Fin m) :
    (conjugateAtomRows design *ᵥ direction) atomIndex
      = star (design.atom atomIndex) ⬝ᵥ direction := rfl

/-- **Parseval in matrix shape**: `Aᴴ · diag t · A = 1`. -/
theorem conjTranspose_mul_weightDiagonal_mul_conjugateAtomRows
    (design : ComplexWeightedDesign m k) :
    (conjugateAtomRows design)ᴴ * weightDiagonal design * conjugateAtomRows design = 1 := by
  have hparseval := design.isParseval
  ext leftCoord rightCoord
  have hentry := congrFun (congrFun hparseval leftCoord) rightCoord
  rw [Matrix.sum_apply] at hentry
  simp only [Matrix.smul_apply, complexAtom, Matrix.vecMulVec_apply, Pi.star_apply,
    smul_eq_mul, RCLike.star_def] at hentry
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, conjugateAtomRows, Matrix.of_apply,
    RCLike.star_def, Complex.conj_conj, weightDiagonal, Matrix.diagonal_mul]
  rw [← hentry]
  exact Finset.sum_congr rfl fun atomLabel _ => by ring

/-- The shadow of a design on the index space: `A · Aᴴ · diag t`, a rank-`k`
idempotent-like factor whose principal `k`-minors are the squared volumes of the
row selections, rescaled by the selected weights. -/
noncomputable def indexShadow (design : ComplexWeightedDesign m k) :
    Matrix (Fin m) (Fin m) ℂ :=
  conjugateAtomRows design * ((conjugateAtomRows design)ᴴ * weightDiagonal design)

/-- The Weinstein–Aronszajn identity in the shape needed here: a product with a
one-sided inverse has the binomial minor generating function. -/
theorem det_one_add_smul_mul_of_leftInverse {Ring : Type*} [CommRing Ring]
    {rows cols : ℕ} (leftFactor : Matrix (Fin rows) (Fin cols) Ring)
    (rightFactor : Matrix (Fin cols) (Fin rows) Ring)
    (hinverse : rightFactor * leftFactor = 1) (scalar : Ring) :
    (1 + scalar • (leftFactor * rightFactor)).det = (1 + scalar) ^ cols := by
  rw [show scalar • (leftFactor * rightFactor) = (scalar • leftFactor) * rightFactor from
      (Matrix.smul_mul scalar leftFactor rightFactor).symm,
    Matrix.det_one_add_mul_comm, Matrix.mul_smul, hinverse,
    ← one_smul Ring (1 : Matrix (Fin cols) (Fin cols) Ring), smul_smul, mul_one,
    ← add_smul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]

/-- **Pythagoras for a complex design's shadows.** The `k`-subset principal
minors of the index shadow sum to one. Sylvester's identity plus Mathlib's
principal-minor expansion of `det(1 + X·P)`; no Cauchy–Binet, no spectral
theorem. -/
theorem sum_det_indexShadowMinors_rank (design : ComplexWeightedDesign m k) :
    ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        ((indexShadow design).submatrix (Subtype.val : { member // member ∈ selected } → Fin m)
          (Subtype.val : { member // member ∈ selected } → Fin m)).det
      = 1 := by
  have hmappedInverse :
      (((conjugateAtomRows design)ᴴ * weightDiagonal design).map Polynomial.C)
          * ((conjugateAtomRows design).map Polynomial.C) = 1 := by
    rw [← Matrix.map_mul (f := (Polynomial.C : ℂ →+* Polynomial ℂ)),
      conjTranspose_mul_weightDiagonal_mul_conjugateAtomRows]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hmappedShadow : (indexShadow design).map Polynomial.C
      = ((conjugateAtomRows design).map Polynomial.C)
        * (((conjugateAtomRows design)ᴴ * weightDiagonal design).map Polynomial.C) := by
    rw [indexShadow, Matrix.map_mul (f := (Polynomial.C : ℂ →+* Polynomial ℂ))]
  rw [← Matrix.coeff_det_one_add_X_smul_eq_sum_minors (indexShadow design) k, hmappedShadow,
    det_one_add_smul_mul_of_leftInverse _ _ hmappedInverse Polynomial.X,
    Polynomial.coeff_one_add_X_pow, Nat.choose_self, Nat.cast_one]

/-! ## Maximal volume for a complex frame -/

/-- The square block a pick selects out of a complex frame. -/
def selectedComplexRows {rows cols : ℕ} (frame : Matrix (Fin rows) (Fin cols) ℂ)
    (pick : Fin cols → Fin rows) : Matrix (Fin cols) (Fin cols) ℂ :=
  frame.submatrix pick id

/-- A principal block of a product with a diagonal factors the selected diagonal
entries out on the right. -/
theorem submatrix_mul_diagonal {size : ℕ} (form : Matrix (Fin m) (Fin m) ℂ)
    (diagonalEntries : Fin m → ℂ) (pick : Fin size → Fin m) :
    (form * Matrix.diagonal diagonalEntries).submatrix pick pick
      = form.submatrix pick pick
        * Matrix.diagonal fun selectedIndex => diagonalEntries (pick selectedIndex) := by
  ext leftIndex rightIndex
  simp [Matrix.mul_diagonal]

/-- A principal block of `A Aᴴ` is the selected block's own Gram. -/
theorem submatrix_mul_conjTranspose {rows cols size : ℕ}
    (frame : Matrix (Fin rows) (Fin cols) ℂ) (pick : Fin size → Fin rows) :
    (frame * frameᴴ).submatrix pick pick
      = frame.submatrix pick id * (frame.submatrix pick id)ᴴ := by
  ext leftIndex rightIndex
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- **The shadow minor is the squared volume, rescaled by the selected weights.** -/
theorem det_indexShadow_submatrix (design : ComplexWeightedDesign m k)
    (pick : Fin k → Fin m) :
    ((indexShadow design).submatrix pick pick).det
      = (selectedComplexRows (conjugateAtomRows design) pick).det
          * star (selectedComplexRows (conjugateAtomRows design) pick).det
        * ∏ selectedIndex, ((design.weight (pick selectedIndex) : ℝ) : ℂ) := by
  rw [indexShadow, ← Matrix.mul_assoc, weightDiagonal, submatrix_mul_diagonal,
    Matrix.det_mul, Matrix.det_diagonal, submatrix_mul_conjTranspose, Matrix.det_mul,
    Matrix.det_conjTranspose, selectedComplexRows]

/-- Reindexing a subset's principal block along its order embedding. -/
theorem det_indexShadow_subtypeSubmatrix (design : ComplexWeightedDesign m k)
    {selected : Finset (Fin m)} (hcard : selected.card = k) :
    ((indexShadow design).submatrix (Subtype.val : { member // member ∈ selected } → Fin m)
        (Subtype.val : { member // member ∈ selected } → Fin m)).det
      = ((indexShadow design).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard)).det := by
  rw [← Matrix.det_submatrix_equiv_self (selected.orderIsoOfFin hcard).toEquiv
    ((indexShadow design).submatrix (Subtype.val : { member // member ∈ selected } → Fin m)
      (Subtype.val : { member // member ∈ selected } → Fin m))]
  rfl

/-- **Some row selection is nonsingular.** If every `k`-element pick had zero
volume, every shadow minor would vanish, contradicting Pythagoras. -/
theorem exists_pick_det_ne_zero (design : ComplexWeightedDesign m k) :
    ∃ pick : Fin k → Fin m,
      (selectedComplexRows (conjugateAtomRows design) pick).det ≠ 0 := by
  by_contra hnone
  rw [not_exists] at hnone
  simp only [not_not] at hnone
  have hallZero : ∀ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      ((indexShadow design).submatrix (Subtype.val : { member // member ∈ selected } → Fin m)
        (Subtype.val : { member // member ∈ selected } → Fin m)).det = 0 := by
    intro selected hmem
    have hcard : selected.card = k := (Finset.mem_powersetCard.mp hmem).2
    rw [det_indexShadow_subtypeSubmatrix design hcard, det_indexShadow_submatrix,
      hnone (selected.orderEmbOfFin hcard)]
    simp
  have hsum := sum_det_indexShadowMinors_rank design
  rw [Finset.sum_congr rfl hallZero, Finset.sum_const_zero] at hsum
  exact absurd hsum (by norm_num)

/-- **The maximal-volume selection.** Among the finitely many picks one maximizes
`‖det‖`, and it is nonsingular because some pick is. The maximum is taken over
ALL picks, not only the injective ones — a repeated row has zero determinant, so
the maximizer is injective for free. -/
theorem exists_maximalVolume_pick_complex (design : ComplexWeightedDesign m k) :
    ∃ pick : Fin k → Fin m,
      (selectedComplexRows (conjugateAtomRows design) pick).det ≠ 0 ∧
      ∀ other : Fin k → Fin m,
        ‖(selectedComplexRows (conjugateAtomRows design) other).det‖
          ≤ ‖(selectedComplexRows (conjugateAtomRows design) pick).det‖ := by
  classical
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (complexSize_pos design)
  obtain ⟨witnessPick, hwitness⟩ := exists_pick_det_ne_zero design
  obtain ⟨bestPick, _, hbest⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin k → Fin m))
      (fun pick => ‖(selectedComplexRows (conjugateAtomRows design) pick).det‖)
      ⟨witnessPick, Finset.mem_univ _⟩
  refine ⟨bestPick, ?_, fun other => hbest other (Finset.mem_univ _)⟩
  intro hzero
  have hle := hbest witnessPick (Finset.mem_univ _)
  rw [hzero, norm_zero] at hle
  exact hwitness (norm_le_zero_iff.mp hle)

/-- The solve matrix `B = F · (F_pick)⁻¹` re-expresses every row of the frame in
the basis formed by the selected rows. -/
noncomputable def complexSolveMatrix {rows cols : ℕ}
    (frame : Matrix (Fin rows) (Fin cols) ℂ) (pick : Fin cols → Fin rows) :
    Matrix (Fin rows) (Fin cols) ℂ :=
  frame * (selectedComplexRows frame pick)⁻¹

theorem complexSolveMatrix_mul_selected {rows cols : ℕ}
    (frame : Matrix (Fin rows) (Fin cols) ℂ) (pick : Fin cols → Fin rows)
    (hunit : IsUnit (selectedComplexRows frame pick).det) :
    complexSolveMatrix frame pick * selectedComplexRows frame pick = frame := by
  rw [complexSolveMatrix, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit,
    Matrix.mul_one]

/-- Every frame row is the solve-matrix combination of the selected rows. -/
theorem complexRow_eq_solveCombination {rows cols : ℕ}
    (frame : Matrix (Fin rows) (Fin cols) ℂ) (pick : Fin cols → Fin rows)
    (hunit : IsUnit (selectedComplexRows frame pick).det) (rowIndex : Fin rows) :
    frame rowIndex
      = ∑ coord, complexSolveMatrix frame pick rowIndex coord
          • selectedComplexRows frame pick coord := by
  have hmul := complexSolveMatrix_mul_selected frame pick hunit
  funext outCoord
  have hentry :
      (complexSolveMatrix frame pick * selectedComplexRows frame pick) rowIndex outCoord
        = frame rowIndex outCoord := by rw [hmul]
  rw [← hentry, Matrix.mul_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Replacing one selected row by an arbitrary frame row is exactly a
one-element swap of the pick. -/
theorem updateRow_selectedComplexRows {rows cols : ℕ}
    (frame : Matrix (Fin rows) (Fin cols) ℂ) (pick : Fin cols → Fin rows)
    (colIndex : Fin cols) (rowIndex : Fin rows) :
    (selectedComplexRows frame pick).updateRow colIndex (frame rowIndex)
      = selectedComplexRows frame (Function.update pick colIndex rowIndex) := by
  ext outIndex coord
  rcases eq_or_ne outIndex colIndex with rfl | hne
  · rw [Matrix.updateRow_self]
    simp [selectedComplexRows]
  · rw [Matrix.updateRow_ne hne]
    simp [selectedComplexRows, Function.update_of_ne hne]

/-- **The maximality identity.** The volume of the swapped pick is the solve
coefficient times the volume of the original. One step from
`Matrix.det_updateRow_sum`, because the inserted row IS the solve
combination. -/
theorem det_selectedComplexRows_update {rows cols : ℕ}
    (frame : Matrix (Fin rows) (Fin cols) ℂ) (pick : Fin cols → Fin rows)
    (hunit : IsUnit (selectedComplexRows frame pick).det) (colIndex : Fin cols)
    (rowIndex : Fin rows) :
    (selectedComplexRows frame (Function.update pick colIndex rowIndex)).det
      = complexSolveMatrix frame pick rowIndex colIndex
        * (selectedComplexRows frame pick).det := by
  rw [← updateRow_selectedComplexRows frame pick colIndex rowIndex,
    complexRow_eq_solveCombination frame pick hunit rowIndex,
    Matrix.det_updateRow_sum, smul_eq_mul]

/-- **MAXIMALITY BOUNDS THE SOLVE MATRIX.** At a pick of maximal volume every
solve coefficient of every row has modulus at most one: a coefficient of larger
modulus would name a swap of strictly larger volume. Because the maximum ranges
over ALL picks — not only injective ones — the bound needs no side condition,
and in particular holds on the selected rows too. -/
theorem norm_complexSolveMatrix_le_one_of_maximalVolume {rows cols : ℕ}
    (frame : Matrix (Fin rows) (Fin cols) ℂ) (pick : Fin cols → Fin rows)
    (hunit : IsUnit (selectedComplexRows frame pick).det)
    (hmax : ∀ other : Fin cols → Fin rows,
      ‖(selectedComplexRows frame other).det‖ ≤ ‖(selectedComplexRows frame pick).det‖)
    (rowIndex : Fin rows) (colIndex : Fin cols) :
    ‖complexSolveMatrix frame pick rowIndex colIndex‖ ≤ 1 := by
  have hswap := hmax (Function.update pick colIndex rowIndex)
  rw [det_selectedComplexRows_update frame pick hunit colIndex rowIndex,
    norm_mul] at hswap
  have hvolumePos : 0 < ‖(selectedComplexRows frame pick).det‖ :=
    norm_pos_iff.mpr hunit.ne_zero
  nlinarith [hswap, hvolumePos]

/-! ## The rank-inverse lower bound -/

/-- **Cauchy–Schwarz on the solve combination.** A vector all of whose solve
coefficients have modulus at most one spreads a coefficient vector over at most
`cols` times its squared length. -/
theorem normSq_solveCombination_le {rows cols : ℕ}
    (solve : Matrix (Fin rows) (Fin cols) ℂ)
    (hbounded : ∀ rowIndex colIndex, ‖solve rowIndex colIndex‖ ≤ 1)
    (coefficients : Fin cols → ℂ) (rowIndex : Fin rows) :
    Complex.normSq ((solve *ᵥ coefficients) rowIndex)
      ≤ (cols : ℝ) * ∑ coord, Complex.normSq (coefficients coord) := by
  have hexpand : (solve *ᵥ coefficients) rowIndex
      = ∑ coord, solve rowIndex coord * coefficients coord := by
    simp only [Matrix.mulVec, dotProduct]
  have htriangle : ‖(solve *ᵥ coefficients) rowIndex‖
      ≤ ∑ coord, ‖coefficients coord‖ := by
    rw [hexpand]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun coord _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hbounded rowIndex coord)
  have hchebyshev : (∑ coord, ‖coefficients coord‖) ^ 2
      ≤ (cols : ℝ) * ∑ coord, ‖coefficients coord‖ ^ 2 := by
    have hraw := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin cols)))
      (f := fun coord => ‖coefficients coord‖)
    simpa using hraw
  have hconvert : ∑ coord, ‖coefficients coord‖ ^ 2
      = ∑ coord, Complex.normSq (coefficients coord) :=
    Finset.sum_congr rfl fun coord _ => (Complex.normSq_eq_norm_sq _).symm
  rw [Complex.normSq_eq_norm_sq, ← hconvert]
  nlinarith [norm_nonneg ((solve *ᵥ coefficients) rowIndex), htriangle, hchebyshev,
    Finset.sum_nonneg (fun coord (_ : coord ∈ Finset.univ) =>
      norm_nonneg (coefficients coord))]

/-- The selected block acts on a direction by reading the projection
coefficients along the pick. -/
theorem selectedComplexRows_mulVec {rows cols : ℕ}
    (frame : Matrix (Fin rows) (Fin cols) ℂ) (pick : Fin cols → Fin rows)
    (direction : Fin cols → ℂ) (selectedIndex : Fin cols) :
    (selectedComplexRows frame pick *ᵥ direction) selectedIndex
      = (frame *ᵥ direction) (pick selectedIndex) := rfl

/-- **THE MAXIMAL-VOLUME COVERING BOUND, weight-aware.** Every complex weighted
design has an injective pick whose `k` selected atoms cover every direction to
within the factor `k − (k−1)·w`, where `w` is the total weight carried by the
selected atoms:

  `|x|² ≤ (k − (k−1)·w) · Σ_{c ∈ T} |⟨g_c, x⟩|²`.

The pick is the one of maximal `|det|` on the conjugated atom rows. Its content
is Cramer's rule — a solve coefficient above one would name a swap of larger
volume — and Parseval. The estimate is independent of the number of atoms, and
it is field-blind: nothing in the argument sees that the scalars are complex.
The selected atoms contribute their own share `w` at factor one and the rest at
factor `k`, which is where the weight refinement comes from. -/
theorem exists_maximalVolume_covering (design : ComplexWeightedDesign m k) :
    ∃ pick : Fin k → Fin m, Function.Injective pick ∧
      ∀ direction : Fin k → ℂ,
        (∑ coord, Complex.normSq (direction coord))
          ≤ ((k : ℝ) - ((k : ℝ) - 1) * ∑ selectedIndex, design.weight (pick selectedIndex))
            * ∑ selectedIndex,
                Complex.normSq (star (design.atom (pick selectedIndex)) ⬝ᵥ direction) := by
  classical
  obtain ⟨pick, hdet, hmax⟩ := exists_maximalVolume_pick_complex design
  have hunit : IsUnit (selectedComplexRows (conjugateAtomRows design) pick).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hinjective : Function.Injective pick := by
    intro leftIndex rightIndex hsame
    by_contra hne
    refine hdet (Matrix.det_zero_of_row_eq hne ?_)
    funext coord
    show conjugateAtomRows design (pick leftIndex) coord
      = conjugateAtomRows design (pick rightIndex) coord
    rw [hsame]
  refine ⟨pick, hinjective, fun direction => ?_⟩
  set selectedDirection : Fin k → ℂ :=
    selectedComplexRows (conjugateAtomRows design) pick *ᵥ direction with hselectedDef
  have hbounded : ∀ (rowIndex : Fin m) (colIndex : Fin k),
      ‖complexSolveMatrix (conjugateAtomRows design) pick rowIndex colIndex‖ ≤ 1 :=
    fun rowIndex colIndex =>
      norm_complexSolveMatrix_le_one_of_maximalVolume _ pick hunit hmax rowIndex colIndex
  have hrecover : complexSolveMatrix (conjugateAtomRows design) pick *ᵥ selectedDirection
      = conjugateAtomRows design *ᵥ direction := by
    rw [hselectedDef, Matrix.mulVec_mulVec,
      complexSolveMatrix_mul_selected _ pick hunit]
  have hselectedValue : ∀ selectedIndex : Fin k,
      selectedDirection selectedIndex
        = star (design.atom (pick selectedIndex)) ⬝ᵥ direction := by
    intro selectedIndex
    rw [hselectedDef, selectedComplexRows_mulVec, conjugateAtomRows_mulVec]
  set selectedTotal : ℝ :=
    ∑ selectedIndex, Complex.normSq (selectedDirection selectedIndex)
    with hselectedTotalDef
  have hspread : ∀ atomIndex : Fin m,
      Complex.normSq (star (design.atom atomIndex) ⬝ᵥ direction)
        ≤ (k : ℝ) * selectedTotal := by
    intro atomIndex
    have hstep := normSq_solveCombination_le (complexSolveMatrix (conjugateAtomRows design) pick)
      hbounded selectedDirection atomIndex
    rwa [hrecover, conjugateAtomRows_mulVec] at hstep
  set selectedWeight : ℝ := ∑ selectedIndex, design.weight (pick selectedIndex)
    with hselectedWeightDef
  set selectedSet : Finset (Fin m) := Finset.image pick Finset.univ with hselectedSetDef
  have hsumImage : ∀ term : Fin m → ℝ,
      ∑ atomLabel ∈ selectedSet, term atomLabel = ∑ selectedIndex, term (pick selectedIndex) := by
    intro term
    rw [hselectedSetDef, Finset.sum_image fun left _ right _ hlr => hinjective hlr]
  have hinsideBound :
      (∑ atomLabel ∈ selectedSet, design.weight atomLabel
          * Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction))
        ≤ selectedWeight * selectedTotal := by
    rw [hsumImage, hselectedWeightDef, Finset.sum_mul]
    refine Finset.sum_le_sum fun selectedIndex _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (design.weight_pos (pick selectedIndex)).le
    rw [← hselectedValue selectedIndex, hselectedTotalDef]
    exact Finset.single_le_sum (f := fun idx => Complex.normSq (selectedDirection idx))
      (fun idx _ => Complex.normSq_nonneg _) (Finset.mem_univ selectedIndex)
  have houtsideWeight :
      (∑ atomLabel ∈ Finset.univ \ selectedSet, design.weight atomLabel) = 1 - selectedWeight := by
    have hsplit := Finset.sum_sdiff (f := design.weight) (Finset.subset_univ selectedSet)
    rw [design.weight_sum_one] at hsplit
    have hinside : (∑ atomLabel ∈ selectedSet, design.weight atomLabel) = selectedWeight :=
      (hsumImage design.weight).trans hselectedWeightDef.symm
    linarith [hsplit, hinside]
  have houtsideBound :
      (∑ atomLabel ∈ Finset.univ \ selectedSet,
          design.weight atomLabel * Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction))
        ≤ (1 - selectedWeight) * ((k : ℝ) * selectedTotal) := by
    rw [← houtsideWeight, Finset.sum_mul]
    exact Finset.sum_le_sum fun atomLabel _ =>
      mul_le_mul_of_nonneg_left (hspread atomLabel) (design.weight_pos atomLabel).le
  have hsplitTotal :
      (∑ atomLabel ∈ Finset.univ \ selectedSet,
          design.weight atomLabel * Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction))
        + ∑ atomLabel ∈ selectedSet, design.weight atomLabel
            * Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction)
      = ∑ atomLabel, design.weight atomLabel
          * Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction) :=
    Finset.sum_sdiff (Finset.subset_univ selectedSet)
  rw [complexParseval_normSq design direction] at hsplitTotal
  have hexpand : selectedWeight * selectedTotal
      + (1 - selectedWeight) * ((k : ℝ) * selectedTotal)
      = ((k : ℝ) - ((k : ℝ) - 1) * selectedWeight) * selectedTotal := by ring
  have htotalValue : selectedTotal
      = ∑ selectedIndex,
          Complex.normSq (star (design.atom (pick selectedIndex)) ⬝ᵥ direction) := by
    rw [hselectedTotalDef]
    exact Finset.sum_congr rfl fun selectedIndex _ => by rw [hselectedValue selectedIndex]
  rw [← htotalValue]
  linarith [hinsideBound, houtsideBound, hsplitTotal, hexpand]

/-! ## The headlines -/

/-- Weighted complex GTZ at a level: every design has a `k`-subset whose atom sum
dominates `level · I`. At `level = 1` this is `ComplexGtzWeighted`; the point of
the file is that the level `1/k` is always reachable. -/
def ComplexGtzWeightedAtLevel (size rank : ℕ) (level : ℝ) : Prop :=
  ∀ design : ComplexWeightedDesign size rank,
    ∃ selection : Finset (Fin size), selection.card = rank ∧
      ((∑ atomLabel ∈ selection, complexAtom (design.atom atomLabel)) - ((level : ℝ) : ℂ)
        • (1 : Matrix (Fin rank) (Fin rank) ℂ)).PosSemidef

/-- Level one is exactly the complex GTZ statement. -/
theorem complexGtzWeightedAtLevel_one_iff (size rank : ℕ) :
    ComplexGtzWeightedAtLevel size rank 1 ↔ ComplexGtzWeighted size rank := by
  constructor
  · intro hlevel design
    obtain ⟨selection, hcard, hpsd⟩ := hlevel design
    rw [Complex.ofReal_one, one_smul] at hpsd
    exact ⟨selection, hcard, hpsd⟩
  · intro hgtz design
    obtain ⟨selection, hcard, hdom⟩ := hgtz design
    refine ⟨selection, hcard, ?_⟩
    rw [Complex.ofReal_one, one_smul]
    exact hdom

/-- **G2, THE HEADLINE: `α_k ≥ 1/k` over ℂ.** Every complex weighted
`(m, k)`-design has a `k`-subset whose atom sum dominates `(1/k)·I`. The subset
is the maximal-volume one; the proof is Cramer's rule plus Parseval, and it is
field-blind, weight-free and independent of the number of atoms.

This is the first proved positive lower bound over ℂ at any rank above one. It
is consistent with — and strictly weaker than — the refutations at level one
(`complexGtzWeighted_four_fails`, `complexGtzWeighted_six_three_fails`), which
say the level cannot be raised all the way to `1`. -/
theorem exists_subset_atomSum_sub_rankInverse_posSemidef (design : ComplexWeightedDesign m k) :
    ∃ selection : Finset (Fin m), selection.card = k ∧
      ((∑ atomLabel ∈ selection, complexAtom (design.atom atomLabel)) - (((k : ℝ)⁻¹ : ℝ) : ℂ)
        • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef := by
  classical
  obtain ⟨pick, hinjective, hcovering⟩ := exists_maximalVolume_covering design
  refine ⟨Finset.image pick Finset.univ, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinjective, Finset.card_univ, Fintype.card_fin]
  · refine posSemidef_atomSum_sub_smul_one design _ ((k : ℝ)⁻¹) fun direction => ?_
    rw [Finset.sum_image fun left _ right _ hlr => hinjective hlr]
    rcases Nat.eq_zero_or_pos k with hzero | hpos
    · subst hzero
      simp
    · have hrankPos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hpos
      have hrankOne : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hpos
      have hweightNonneg : 0 ≤ ∑ selectedIndex, design.weight (pick selectedIndex) :=
        Finset.sum_nonneg fun selectedIndex _ => (design.weight_pos (pick selectedIndex)).le
      have htotalNonneg : 0 ≤ ∑ selectedIndex,
          Complex.normSq (star (design.atom (pick selectedIndex)) ⬝ᵥ direction) :=
        Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
      have hslack : 0 ≤ ((k : ℝ) - 1) * (∑ selectedIndex, design.weight (pick selectedIndex))
          * ∑ selectedIndex,
              Complex.normSq (star (design.atom (pick selectedIndex)) ⬝ᵥ direction) :=
        mul_nonneg (mul_nonneg (by linarith) hweightNonneg) htotalNonneg
      have hcrude : (∑ coord, Complex.normSq (direction coord))
          ≤ (k : ℝ) * ∑ selectedIndex,
              Complex.normSq (star (design.atom (pick selectedIndex)) ⬝ᵥ direction) := by
        nlinarith [hcovering direction, hslack]
      have hscaled := mul_le_mul_of_nonneg_left hcrude (le_of_lt (inv_pos.mpr hrankPos))
      rwa [← mul_assoc, inv_mul_cancel₀ hrankPos.ne', one_mul] at hscaled

/-- **G2, the weight-aware form.** The maximal-volume subset dominates
`(k − (k−1)·w)⁻¹ · I`, where `w` is the total weight it carries. Since
`0 < w ≤ 1` and `k ≥ 1` the level lies in `[1/k, 1]`, so this refines the
`1/k` bound at every design and is exactly `1` when a single atom carries all
the weight. -/
theorem exists_subset_atomSum_sub_maximalVolumeLevel_posSemidef
    (hrank : 0 < k) (design : ComplexWeightedDesign m k) :
    ∃ selection : Finset (Fin m), selection.card = k ∧
      ((∑ atomLabel ∈ selection, complexAtom (design.atom atomLabel))
        - ((((k : ℝ) - ((k : ℝ) - 1) * ∑ atomLabel ∈ selection, design.weight atomLabel)⁻¹ : ℝ) : ℂ)
          • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef := by
  classical
  obtain ⟨pick, hinjective, hcovering⟩ := exists_maximalVolume_covering design
  have hsumImage : ∀ term : Fin m → ℝ,
      (∑ atomLabel ∈ Finset.image pick Finset.univ, term atomLabel)
        = ∑ selectedIndex, term (pick selectedIndex) :=
    fun term => Finset.sum_image fun left _ right _ hlr => hinjective hlr
  have hrankPos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
  have hrankOne : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrank
  have hweightNonneg : 0 ≤ ∑ selectedIndex, design.weight (pick selectedIndex) :=
    Finset.sum_nonneg fun selectedIndex _ => (design.weight_pos (pick selectedIndex)).le
  have hweightLeOne : (∑ selectedIndex, design.weight (pick selectedIndex)) ≤ 1 := by
    rw [← hsumImage design.weight, ← design.weight_sum_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun atomLabel _ _ => (design.weight_pos atomLabel).le
  have hlevelPos :
      0 < (k : ℝ) - ((k : ℝ) - 1) * ∑ selectedIndex, design.weight (pick selectedIndex) := by
    nlinarith [hweightLeOne, hweightNonneg, hrankOne]
  refine ⟨Finset.image pick Finset.univ, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinjective, Finset.card_univ, Fintype.card_fin]
  · rw [hsumImage design.weight]
    refine posSemidef_atomSum_sub_smul_one design _ _ fun direction => ?_
    rw [hsumImage fun atomLabel => Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction)]
    have hscaled := mul_le_mul_of_nonneg_left (hcovering direction)
      (le_of_lt (inv_pos.mpr hlevelPos))
    rwa [← mul_assoc, inv_mul_cancel₀ hlevelPos.ne', one_mul] at hscaled

/-- The level form of the headline. -/
theorem complexGtzWeightedAtLevel_rankInverse (size rank : ℕ) :
    ComplexGtzWeightedAtLevel size rank ((rank : ℝ)⁻¹) :=
  fun design => exists_subset_atomSum_sub_rankInverse_posSemidef design

/-- **The rank-three corollary: `α₃ ≥ 1/3` over ℂ.** -/
theorem exists_subset_atomSum_sub_third_posSemidef (design : ComplexWeightedDesign m 3) :
    ∃ selection : Finset (Fin m), selection.card = 3 ∧
      ((∑ atomLabel ∈ selection, complexAtom (design.atom atomLabel)) - ((1 / 3 : ℝ) : ℂ)
        • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
  obtain ⟨selection, hcard, hpsd⟩ := exists_subset_atomSum_sub_rankInverse_posSemidef design
  refine ⟨selection, hcard, ?_⟩
  have hlevel : ((1 / 3 : ℝ) : ℂ) = ((((3 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by norm_num
  rw [hlevel]
  exact hpsd

/-! ## Route (b): the complex volume-sampling measure -/

/-- The volume-sampling weight of a row selection: the squared volume of the
selected block times the product of the selected weights. -/
noncomputable def shadowVolume (design : ComplexWeightedDesign m k) (pick : Fin k → Fin m) : ℝ :=
  Complex.normSq (selectedComplexRows (conjugateAtomRows design) pick).det
    * ∏ selectedIndex, design.weight (pick selectedIndex)

theorem shadowVolume_nonneg (design : ComplexWeightedDesign m k) (pick : Fin k → Fin m) :
    0 ≤ shadowVolume design pick :=
  mul_nonneg (Complex.normSq_nonneg _)
    (Finset.prod_nonneg fun selectedIndex _ => (design.weight_pos (pick selectedIndex)).le)

/-- **Every shadow minor is a nonnegative real: the volume-sampling weight.** -/
theorem det_indexShadow_submatrix_real (design : ComplexWeightedDesign m k)
    (pick : Fin k → Fin m) :
    ((indexShadow design).submatrix pick pick).det = ((shadowVolume design pick : ℝ) : ℂ) := by
  rw [det_indexShadow_submatrix, shadowVolume]
  push_cast
  congr 1
  rw [RCLike.star_def]
  exact Complex.mul_conj _

/-- **Route (b): some selection carries at least the average shadow volume.**
The `k`-subset shadow volumes are nonnegative and sum to one over the `C(m, k)`
subsets, so one of them is at least `1 / C(m, k)`. This is the whole complex
Cauchy–Binet content and it is exponentially weaker than the maximal-volume
bound above. Converting a shadow volume into a Loewner bound needs
`λ_min ≥ det` on a sub-identity block — a spectral step NOT mechanized here. -/
theorem exists_pick_shadowVolume_ge_average (design : ComplexWeightedDesign m k)
    (hsize : k ≤ m) :
    ∃ pick : Fin k → Fin m,
      Function.Injective pick ∧ ((m.choose k : ℝ))⁻¹ ≤ shadowVolume design pick := by
  classical
  by_contra hnone
  simp only [not_exists, not_and, not_le] at hnone
  have hfamilyNonempty :
      ((Finset.univ : Finset (Fin m)).powersetCard k).Nonempty := by
    refine Finset.powersetCard_nonempty.mpr ?_
    simpa using hsize
  have hchoosePos : 0 < (m.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hsize
  have hsum := sum_det_indexShadowMinors_rank design
  have hrealSum :
      ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (((indexShadow design).submatrix (Subtype.val : { member // member ∈ selected } → Fin m)
            (Subtype.val : { member // member ∈ selected } → Fin m)).det).re = 1 := by
    rw [← Complex.re_sum, hsum, Complex.one_re]
  have hstrict :
      ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (((indexShadow design).submatrix (Subtype.val : { member // member ∈ selected } → Fin m)
            (Subtype.val : { member // member ∈ selected } → Fin m)).det).re
        < ∑ _selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
            ((m.choose k : ℝ))⁻¹ := by
    refine Finset.sum_lt_sum_of_nonempty hfamilyNonempty fun selected hmem => ?_
    have hcard : selected.card = k := (Finset.mem_powersetCard.mp hmem).2
    rw [det_indexShadow_subtypeSubmatrix design hcard,
      det_indexShadow_submatrix_real, Complex.ofReal_re]
    exact hnone _ (selected.orderEmbOfFin hcard).injective
  rw [hrealSum, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hstrict
  rw [mul_inv_cancel₀ hchoosePos.ne'] at hstrict
  exact lt_irrefl _ hstrict

/-- **Restricted invertibility, as a named hypothesis — CITED, never assumed.**
Bourgain–Tzafriri and Spielman–Srivastava select a subset of a Parseval frame
whose Gram is bounded below by an absolute constant. This file does not prove
any such statement and does not axiomatize it; the Prop is recorded so the
implication can be stated. Nothing below depends on it. -/
def ComplexUniformLevel (level : ℝ) : Prop :=
  ∀ (size rank : ℕ), ComplexGtzWeightedAtLevel size rank level

/-- **The named hypothesis is FALSE at level one**, by the padded SIC. So any
citable absolute constant over ℂ is strictly below one, and the proved `1/k`
sits strictly inside the surviving window. -/
theorem not_complexUniformLevel_one :
    ¬ ComplexUniformLevel 1 := by
  intro hlevel
  exact complexGtzWeighted_six_three_fails
    ((complexGtzWeightedAtLevel_one_iff 6 3).mp (hlevel 6 3))

end RankInverseLowerBound

/-! # Part B. The shared-axis trine: `3 - sqrt 5` is LEAST, ATTAINED and an EIGENVALUE

`Gtz/Complex/SharpConstantLedger.lean` proves that no `3`-subset of `trineDesign`
dominates and names the binding root `3 - sqrt 5`; its SCOPE NOTE disclaims that
the root is the LEAST eigenvalue and that the exhibited subset is the BEST one.
This part closes both, in the Loewner form the ledger actually needs, plus the
eigenvalue form for the binding triple.

**Orbit structure**, which is why twenty cases collapse to two.  The unitary
automorphism group of the design, ACTING ON THE RANK-ONE ATOMS (i.e. up to a
unimodular phase per atom — the diagonal generators do NOT fix the atom vectors),
is `(Z/3 x Z/3) semidirect Z/2` of order 18: independent `Z/3` phase rotations on
the two trines, `diag(w^a, w^b, 1)`, plus the axis swap.  It acts with exactly two
orbits on the `3`-subsets: the two coplanar triples, and all eighteen mixed ones
in a single orbit.  The proofs below do NOT invoke the symmetry; they enumerate
all twenty subsets the way the ledger already does, so a reader who distrusts the
group theory loses nothing. -/

/-! ## Part 1: the margin is ATTAINED -/

theorem rootFiveC_conj : (starRingEnd ℂ) rootFiveC = rootFiveC :=
  Complex.conj_ofReal _

/-- **Abstract binding decomposition, pair on the first axis.** Two atoms
`(t,0,p)`, `(t,0,q)` with `t^2 = 2` and distinct unit phases, plus one atom
`(0,t,r)`: at the shift `3 - sqrt5` the excess is a nonnegative combination of
exactly two rank-one atoms. The nested radicals cancel through
`(sqrt5 - 1)(sqrt5 + 1) = 4`, so no square root of a square root appears. -/
theorem splitPairLeft_binding_decomp
    (legAmp firstPhase secondPhase thirdPhase rootFive : ℂ)
    (hlegReal : (starRingEnd ℂ) legAmp = legAmp) (hlegSq : legAmp * legAmp = 2)
    (hrootReal : (starRingEnd ℂ) rootFive = rootFive)
    (hrootSq : rootFive * rootFive = 5)
    (hunitFirst : (starRingEnd ℂ) firstPhase * firstPhase = 1)
    (hunitSecond : (starRingEnd ℂ) secondPhase * secondPhase = 1)
    (hunitThird : (starRingEnd ℂ) thirdPhase * thirdPhase = 1)
    (hcross : (starRingEnd ℂ) firstPhase * secondPhase
      + (starRingEnd ℂ) secondPhase * firstPhase = -1) :
    complexAtom ![legAmp, 0, firstPhase]
        + (complexAtom ![legAmp, 0, secondPhase] + complexAtom ![0, legAmp, thirdPhase])
        - (3 - rootFive) • (1 : Matrix (Fin 3) (Fin 3) ℂ)
      = ((rootFive - 1) / 4)
          • complexAtom ![1 + rootFive, 0, legAmp * (firstPhase + secondPhase)]
        + ((rootFive + 1) / 4) • complexAtom ![0, rootFive - 1, legAmp * thirdPhase] := by
  ext rowIndex colIndex
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    complexAtom_apply, Matrix.one_apply]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [hlegReal, hrootReal]
  · linear_combination 2 * hlegSq - ((rootFive + 1) / 4) * hrootSq
  · linear_combination
      (-(legAmp * ((starRingEnd ℂ) firstPhase + (starRingEnd ℂ) secondPhase)) / 4) * hrootSq
  · linear_combination hlegSq - ((rootFive - 1) / 4) * hrootSq
  · linear_combination (-(legAmp * (starRingEnd ℂ) thirdPhase) / 4) * hrootSq
  · linear_combination (-(legAmp * (firstPhase + secondPhase)) / 4) * hrootSq
  · linear_combination (-(legAmp * thirdPhase) / 4) * hrootSq
  · linear_combination (1 - (rootFive - 1) / 2) * hunitFirst
      + (1 - (rootFive - 1) / 2) * hunitSecond
      + (1 - (rootFive + 1) / 2) * hunitThird
      - ((rootFive - 1) / 2) * hcross
      + (-((rootFive - 1) / 4) * ((firstPhase + secondPhase)
            * ((starRingEnd ℂ) firstPhase + (starRingEnd ℂ) secondPhase))
         - ((rootFive + 1) / 4) * (thirdPhase * (starRingEnd ℂ) thirdPhase)) * hlegSq

/-- **Abstract binding decomposition, pair on the second axis** — the axis-swap
image of the previous lemma. -/
theorem splitPairRight_binding_decomp
    (legAmp firstPhase secondPhase thirdPhase rootFive : ℂ)
    (hlegReal : (starRingEnd ℂ) legAmp = legAmp) (hlegSq : legAmp * legAmp = 2)
    (hrootReal : (starRingEnd ℂ) rootFive = rootFive)
    (hrootSq : rootFive * rootFive = 5)
    (hunitFirst : (starRingEnd ℂ) firstPhase * firstPhase = 1)
    (hunitSecond : (starRingEnd ℂ) secondPhase * secondPhase = 1)
    (hunitThird : (starRingEnd ℂ) thirdPhase * thirdPhase = 1)
    (hcross : (starRingEnd ℂ) secondPhase * thirdPhase
      + (starRingEnd ℂ) thirdPhase * secondPhase = -1) :
    complexAtom ![legAmp, 0, firstPhase]
        + (complexAtom ![0, legAmp, secondPhase] + complexAtom ![0, legAmp, thirdPhase])
        - (3 - rootFive) • (1 : Matrix (Fin 3) (Fin 3) ℂ)
      = ((rootFive - 1) / 4)
          • complexAtom ![0, 1 + rootFive, legAmp * (secondPhase + thirdPhase)]
        + ((rootFive + 1) / 4) • complexAtom ![rootFive - 1, 0, legAmp * firstPhase] := by
  ext rowIndex colIndex
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    complexAtom_apply, Matrix.one_apply]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [hlegReal, hrootReal]
  · linear_combination hlegSq - ((rootFive - 1) / 4) * hrootSq
  · linear_combination (-(legAmp * (starRingEnd ℂ) firstPhase) / 4) * hrootSq
  · linear_combination 2 * hlegSq - ((rootFive + 1) / 4) * hrootSq
  · linear_combination
      (-(legAmp * ((starRingEnd ℂ) secondPhase + (starRingEnd ℂ) thirdPhase)) / 4) * hrootSq
  · linear_combination (-(legAmp * firstPhase) / 4) * hrootSq
  · linear_combination (-(legAmp * (secondPhase + thirdPhase)) / 4) * hrootSq
  · linear_combination (1 - (rootFive + 1) / 2) * hunitFirst
      + (1 - (rootFive - 1) / 2) * hunitSecond
      + (1 - (rootFive - 1) / 2) * hunitThird
      - ((rootFive - 1) / 2) * hcross
      + (-((rootFive - 1) / 4) * ((secondPhase + thirdPhase)
            * ((starRingEnd ℂ) secondPhase + (starRingEnd ℂ) thirdPhase))
         - ((rootFive + 1) / 4) * (firstPhase * (starRingEnd ℂ) firstPhase)) * hlegSq

/-! ### Concrete instantiation at the trine -/

theorem trineMargin_cast : ((trineMarginRankThree : ℝ) : ℂ) = 3 - rootFiveC := by
  rw [trineMarginRankThree, rootFiveC]
  push_cast
  ring

/-- The weight carried by the two-phase atom of the binding decomposition,
`(sqrt5 - 1)/4`, is nonnegative. -/
theorem bindingWeightPair_nonneg : (0 : ℂ) ≤ (rootFiveC - 1) / 4 := by
  have hcast : (rootFiveC - 1) / 4 = (((Real.sqrt 5 - 1) / 4 : ℝ) : ℂ) := by
    rw [rootFiveC]; push_cast; ring
  rw [hcast]
  refine Complex.zero_le_real.mpr ?_
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [hsq, hpos]

/-- The weight carried by the single-phase atom of the binding decomposition,
`(sqrt5 + 1)/4`, is nonnegative. -/
theorem bindingWeightSingle_nonneg : (0 : ℂ) ≤ (rootFiveC + 1) / 4 := by
  have hcast : (rootFiveC + 1) / 4 = (((Real.sqrt 5 + 1) / 4 : ℝ) : ℂ) := by
    rw [rootFiveC]; push_cast; ring
  rw [hcast]
  refine Complex.zero_le_real.mpr ?_
  have hpos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [hpos]

/-- **The binding triple IS positive semidefinite at the margin**, pair on the
first axis: the excess is a nonnegative combination of two rank-one atoms. -/
theorem trineMixedLeftPair_psd_at_margin (firstPhase secondPhase thirdPhase : Fin 3)
    (hne : firstPhase ≠ secondPhase) :
    (complexAtom (trineLeft firstPhase)
        + (complexAtom (trineLeft secondPhase) + complexAtom (trineRight thirdPhase))
        - ((trineMarginRankThree : ℝ) : ℂ)
          • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
  rw [trineMargin_cast]
  rw [show (trineLeft firstPhase) = ![topAmpC, 0, omegaPow firstPhase] from rfl,
    show (trineLeft secondPhase) = ![topAmpC, 0, omegaPow secondPhase] from rfl,
    show (trineRight thirdPhase) = ![0, topAmpC, omegaPow thirdPhase] from rfl,
    splitPairLeft_binding_decomp topAmpC (omegaPow firstPhase) (omegaPow secondPhase)
      (omegaPow thirdPhase) rootFiveC topAmpC_conj topAmpC_sq rootFiveC_conj
      rootFiveC_sq (omegaPow_unit _) (omegaPow_unit _) (omegaPow_unit _)
      (omegaPow_cross hne)]
  exact ((complexAtom_posSemidef _).smul bindingWeightPair_nonneg).add
    ((complexAtom_posSemidef _).smul bindingWeightSingle_nonneg)

/-- The same, pair on the second axis. -/
theorem trineMixedRightPair_psd_at_margin (firstPhase secondPhase thirdPhase : Fin 3)
    (hne : secondPhase ≠ thirdPhase) :
    (complexAtom (trineLeft firstPhase)
        + (complexAtom (trineRight secondPhase) + complexAtom (trineRight thirdPhase))
        - ((trineMarginRankThree : ℝ) : ℂ)
          • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
  rw [trineMargin_cast]
  rw [show (trineLeft firstPhase) = ![topAmpC, 0, omegaPow firstPhase] from rfl,
    show (trineRight secondPhase) = ![0, topAmpC, omegaPow secondPhase] from rfl,
    show (trineRight thirdPhase) = ![0, topAmpC, omegaPow thirdPhase] from rfl,
    splitPairRight_binding_decomp topAmpC (omegaPow firstPhase) (omegaPow secondPhase)
      (omegaPow thirdPhase) rootFiveC topAmpC_conj topAmpC_sq rootFiveC_conj
      rootFiveC_sq (omegaPow_unit _) (omegaPow_unit _) (omegaPow_unit _)
      (omegaPow_cross hne)]
  exact ((complexAtom_posSemidef _).smul bindingWeightPair_nonneg).add
    ((complexAtom_posSemidef _).smul bindingWeightSingle_nonneg)

/-! ## Part 2: above the margin every triple fails -/

theorem trineMargin_pos : 0 < trineMarginRankThree := by
  have hwindow := trineMargin_window
  linarith [hwindow.1]

/-- Below `5/2` the determinant certificate fires: `(3 - z)(z^2 - 6z + 4) < 0` on
`(3 - sqrt5, 5/2]`. It does NOT fire on `(3, 3 + sqrt5)`, where the same
polynomial is positive — hence the second region. -/
theorem trineMixedDet_neg_of_le {shift : ℝ}
    (habove : trineMarginRankThree < shift) (hle : shift ≤ 5 / 2) :
    (3 - shift) * (shift ^ 2 - 6 * shift + 4) < 0 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rw [trineMarginRankThree] at habove
  have hlow : 0 < shift - 3 + Real.sqrt 5 := by linarith
  have hhigh : shift - 3 - Real.sqrt 5 < 0 := by linarith
  have hprod : (shift - 3 - Real.sqrt 5) * (shift - 3 + Real.sqrt 5) < 0 :=
    mul_neg_of_neg_of_pos hhigh hlow
  have hquad : shift ^ 2 - 6 * shift + 4 < 0 := by nlinarith [hsq, hprod]
  have hlin : (0 : ℝ) < 3 - shift := by linarith
  exact mul_neg_of_pos_of_neg hlin hquad

/-- **No mixed triple dominates above the margin**, pair on the first axis. Two
regions: determinant below `5/2`, the empty second axis above it. -/
theorem trineMixedLeftPair_not_psd_above (firstPhase secondPhase thirdPhase : Fin 3)
    (hne : firstPhase ≠ secondPhase) (shift : ℝ)
    (habove : trineMarginRankThree < shift) :
    ¬ (complexAtom (trineLeft firstPhase)
        + (complexAtom (trineLeft secondPhase) + complexAtom (trineRight thirdPhase))
        - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
  rcases le_or_gt shift (5 / 2) with hle | hgt
  · refine not_posSemidef_of_det_re_neg_gen ?_
    rw [trineMixedLeftPair_charpoly hne]
    have hcast : (3 - ((shift : ℝ) : ℂ))
        * (((shift : ℝ) : ℂ) ^ 2 - 6 * ((shift : ℝ) : ℂ) + 4)
        = (((3 - shift) * (shift ^ 2 - 6 * shift + 4) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.ofReal_re]
    exact trineMixedDet_neg_of_le habove hle
  · refine not_posSemidef_of_diag_re_neg 1 ?_
    have hentry := tripleGap_apply (trineLeft firstPhase) (trineLeft secondPhase)
      (trineRight thirdPhase) ((shift : ℝ) : ℂ) 1 1
    have hvalue : (complexAtom (trineLeft firstPhase)
        + (complexAtom (trineLeft secondPhase) + complexAtom (trineRight thirdPhase))
        - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) 1 1
        = (((2 - shift : ℝ)) : ℂ) := by
      rw [hentry]
      simp only [trineLeft, trineRight, Matrix.cons_val_one,
        Matrix.cons_val_zero, if_true]
      push_cast
      linear_combination topAmpC_sq + topAmpC * topAmpC_conj
    rw [hvalue, Complex.ofReal_re]
    linarith

/-- The same, pair on the second axis. -/
theorem trineMixedRightPair_not_psd_above (firstPhase secondPhase thirdPhase : Fin 3)
    (hne : secondPhase ≠ thirdPhase) (shift : ℝ)
    (habove : trineMarginRankThree < shift) :
    ¬ (complexAtom (trineLeft firstPhase)
        + (complexAtom (trineRight secondPhase) + complexAtom (trineRight thirdPhase))
        - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
  rcases le_or_gt shift (5 / 2) with hle | hgt
  · refine not_posSemidef_of_det_re_neg_gen ?_
    rw [trineMixedRightPair_charpoly hne]
    have hcast : (3 - ((shift : ℝ) : ℂ))
        * (((shift : ℝ) : ℂ) ^ 2 - 6 * ((shift : ℝ) : ℂ) + 4)
        = (((3 - shift) * (shift ^ 2 - 6 * shift + 4) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.ofReal_re]
    exact trineMixedDet_neg_of_le habove hle
  · refine not_posSemidef_of_diag_re_neg 0 ?_
    have hentry := tripleGap_apply (trineLeft firstPhase) (trineRight secondPhase)
      (trineRight thirdPhase) ((shift : ℝ) : ℂ) 0 0
    have hvalue : (complexAtom (trineLeft firstPhase)
        + (complexAtom (trineRight secondPhase) + complexAtom (trineRight thirdPhase))
        - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) 0 0
        = (((2 - shift : ℝ)) : ℂ) := by
      rw [hentry]
      simp only [trineLeft, trineRight, Matrix.cons_val_zero, if_true]
      push_cast
      linear_combination topAmpC_sq + topAmpC * topAmpC_conj
    rw [hvalue, Complex.ofReal_re]
    linarith

/-- The coplanar triples miss an axis, so they fail at every positive shift. -/
theorem trinePureLeft_not_psd_above (shift : ℝ) (hpos : 0 < shift) :
    ¬ (complexAtom (trineLeft 0)
        + (complexAtom (trineLeft 1) + complexAtom (trineLeft 2))
        - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
  refine not_posSemidef_of_diag_re_neg 1 ?_
  have hvalue : (complexAtom (trineLeft 0)
      + (complexAtom (trineLeft 1) + complexAtom (trineLeft 2))
      - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) 1 1
      = (((-shift : ℝ)) : ℂ) := by
    rw [tripleGap_apply]
    simp [trineLeft]
  rw [hvalue, Complex.ofReal_re]
  linarith

theorem trinePureRight_not_psd_above (shift : ℝ) (hpos : 0 < shift) :
    ¬ (complexAtom (trineRight 0)
        + (complexAtom (trineRight 1) + complexAtom (trineRight 2))
        - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
  refine not_posSemidef_of_diag_re_neg 0 ?_
  have hvalue : (complexAtom (trineRight 0)
      + (complexAtom (trineRight 1) + complexAtom (trineRight 2))
      - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) 0 0
      = (((-shift : ℝ)) : ℂ) := by
    rw [tripleGap_apply]
    simp [trineRight]
  rw [hvalue, Complex.ofReal_re]
  linarith

/-! ### The assembled least-ness statement -/

/-- Expanding a three-element sum of distinct indices. -/
theorem tripleAtomSum_expand (firstIdx secondIdx thirdIdx : Fin 6)
    (hfirst : firstIdx ∉ ({secondIdx, thirdIdx} : Finset (Fin 6)))
    (hsecond : secondIdx ∉ ({thirdIdx} : Finset (Fin 6))) :
    ∑ c ∈ ({firstIdx, secondIdx, thirdIdx} : Finset (Fin 6)), complexAtom (trineAtom c)
      = complexAtom (trineAtom firstIdx)
        + (complexAtom (trineAtom secondIdx) + complexAtom (trineAtom thirdIdx)) := by
  rw [Finset.sum_insert hfirst, Finset.sum_insert hsecond, Finset.sum_singleton]

set_option maxHeartbeats 4000000 in
/-- **Above `3 - sqrt 5` NO triple of the trine survives.** All twenty cases:
the two coplanar triples on a negative diagonal entry, the eighteen mixed ones
on a negative determinant below `5/2` and on a negative diagonal entry above it.
The two-region split is FORCED: the mixed determinant is POSITIVE on
`(3, 3 + sqrt 5)`, so a determinant certificate alone does not cover the claim. -/
theorem trine_no_triple_above_margin (shift : ℝ)
    (habove : trineMarginRankThree < shift)
    (subset : Finset (Fin 6)) (hcard : subset.card = 3) :
    ¬ ((∑ c ∈ subset, complexAtom (trineDesign.atom c))
        - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
  intro hpsdRaw
  have hshiftPos : 0 < shift := lt_trans trineMargin_pos habove
  have hexpand := tripleAtomSum_expand
  rw [trineDesign_atom] at hpsdRaw
  have hpsd := hpsdRaw
  rcases tripleSubset_enumeration subset hcard with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h, hexpand 0 1 2 (by decide) (by decide), trineAtom_zero, trineAtom_one,
      trineAtom_two] at hpsd
    exact trinePureLeft_not_psd_above shift hshiftPos hpsd
  · rw [h, hexpand 0 1 3 (by decide) (by decide), trineAtom_zero, trineAtom_one,
      trineAtom_three] at hpsd
    exact trineMixedLeftPair_not_psd_above 0 1 0 (by decide) shift habove hpsd
  · rw [h, hexpand 0 1 4 (by decide) (by decide), trineAtom_zero, trineAtom_one,
      trineAtom_four] at hpsd
    exact trineMixedLeftPair_not_psd_above 0 1 1 (by decide) shift habove hpsd
  · rw [h, hexpand 0 1 5 (by decide) (by decide), trineAtom_zero, trineAtom_one,
      trineAtom_five] at hpsd
    exact trineMixedLeftPair_not_psd_above 0 1 2 (by decide) shift habove hpsd
  · rw [h, hexpand 0 2 3 (by decide) (by decide), trineAtom_zero, trineAtom_two,
      trineAtom_three] at hpsd
    exact trineMixedLeftPair_not_psd_above 0 2 0 (by decide) shift habove hpsd
  · rw [h, hexpand 0 2 4 (by decide) (by decide), trineAtom_zero, trineAtom_two,
      trineAtom_four] at hpsd
    exact trineMixedLeftPair_not_psd_above 0 2 1 (by decide) shift habove hpsd
  · rw [h, hexpand 0 2 5 (by decide) (by decide), trineAtom_zero, trineAtom_two,
      trineAtom_five] at hpsd
    exact trineMixedLeftPair_not_psd_above 0 2 2 (by decide) shift habove hpsd
  · rw [h, hexpand 1 2 3 (by decide) (by decide), trineAtom_one, trineAtom_two,
      trineAtom_three] at hpsd
    exact trineMixedLeftPair_not_psd_above 1 2 0 (by decide) shift habove hpsd
  · rw [h, hexpand 1 2 4 (by decide) (by decide), trineAtom_one, trineAtom_two,
      trineAtom_four] at hpsd
    exact trineMixedLeftPair_not_psd_above 1 2 1 (by decide) shift habove hpsd
  · rw [h, hexpand 1 2 5 (by decide) (by decide), trineAtom_one, trineAtom_two,
      trineAtom_five] at hpsd
    exact trineMixedLeftPair_not_psd_above 1 2 2 (by decide) shift habove hpsd
  · rw [h, hexpand 0 3 4 (by decide) (by decide), trineAtom_zero, trineAtom_three,
      trineAtom_four] at hpsd
    exact trineMixedRightPair_not_psd_above 0 0 1 (by decide) shift habove hpsd
  · rw [h, hexpand 0 3 5 (by decide) (by decide), trineAtom_zero, trineAtom_three,
      trineAtom_five] at hpsd
    exact trineMixedRightPair_not_psd_above 0 0 2 (by decide) shift habove hpsd
  · rw [h, hexpand 0 4 5 (by decide) (by decide), trineAtom_zero, trineAtom_four,
      trineAtom_five] at hpsd
    exact trineMixedRightPair_not_psd_above 0 1 2 (by decide) shift habove hpsd
  · rw [h, hexpand 1 3 4 (by decide) (by decide), trineAtom_one, trineAtom_three,
      trineAtom_four] at hpsd
    exact trineMixedRightPair_not_psd_above 1 0 1 (by decide) shift habove hpsd
  · rw [h, hexpand 1 3 5 (by decide) (by decide), trineAtom_one, trineAtom_three,
      trineAtom_five] at hpsd
    exact trineMixedRightPair_not_psd_above 1 0 2 (by decide) shift habove hpsd
  · rw [h, hexpand 1 4 5 (by decide) (by decide), trineAtom_one, trineAtom_four,
      trineAtom_five] at hpsd
    exact trineMixedRightPair_not_psd_above 1 1 2 (by decide) shift habove hpsd
  · rw [h, hexpand 2 3 4 (by decide) (by decide), trineAtom_two, trineAtom_three,
      trineAtom_four] at hpsd
    exact trineMixedRightPair_not_psd_above 2 0 1 (by decide) shift habove hpsd
  · rw [h, hexpand 2 3 5 (by decide) (by decide), trineAtom_two, trineAtom_three,
      trineAtom_five] at hpsd
    exact trineMixedRightPair_not_psd_above 2 0 2 (by decide) shift habove hpsd
  · rw [h, hexpand 2 4 5 (by decide) (by decide), trineAtom_two, trineAtom_four,
      trineAtom_five] at hpsd
    exact trineMixedRightPair_not_psd_above 2 1 2 (by decide) shift habove hpsd
  · rw [h, hexpand 3 4 5 (by decide) (by decide), trineAtom_three, trineAtom_four,
      trineAtom_five] at hpsd
    exact trinePureRight_not_psd_above shift hshiftPos hpsd

/-- **The margin is ATTAINED**: the triple `{L0, L1, R0}` has a positive
semidefinite excess exactly at `3 - sqrt 5`. -/
theorem trine_bindingTriple_psd_at_margin :
    ((∑ c ∈ ({0, 1, 3} : Finset (Fin 6)), complexAtom (trineDesign.atom c))
      - ((trineMarginRankThree : ℝ) : ℂ)
        • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
  rw [trineDesign_atom, tripleAtomSum_expand 0 1 3 (by decide) (by decide),
    trineAtom_zero, trineAtom_one, trineAtom_three]
  exact trineMixedLeftPair_psd_at_margin 0 1 0 (by decide)

/-- **The trine's value, in LOEWNER form.** The margin is attained by a triple,
and no triple survives any strictly larger shift, so the set of shifts at which
some `3`-subset dominates has greatest element `3 - sqrt 5`. That is the
Loewner reading of `max_{|subset| = 3} lambda_min = 3 - sqrt 5`, and it is what
`ComplexDominates` and the ledger actually need.

SCOPE, exactly. The eigenvalue reading follows from the Loewner one only through
`block - level . I ⪰ 0 ↔ lambda_min block ≥ level`, whose `←` direction needs the
spectral theorem and is NOT mechanized anywhere in this file. The eigenvalue form
is proved SEPARATELY, and only for the binding triple, by
`trineBinding_leastEigenvalue` below — which exhibits an eigenvector and bounds
the spectrum elementarily. So: Loewner form for EVERY `3`-subset; eigenvalue form
for ONE of them. -/
theorem trineMargin_isLeastAndAttained :
    ((∑ c ∈ ({0, 1, 3} : Finset (Fin 6)), complexAtom (trineDesign.atom c))
        - ((trineMarginRankThree : ℝ) : ℂ)
          • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef
      ∧ ∀ shift : ℝ, trineMarginRankThree < shift →
          ∀ subset : Finset (Fin 6), subset.card = 3 →
            ¬ ((∑ c ∈ subset, complexAtom (trineDesign.atom c))
                - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef :=
  ⟨trine_bindingTriple_psd_at_margin, trine_no_triple_above_margin⟩

/-! ## Part 3: the exact value, as a greatest element

Domination is monotone in the shift, so parts 1 and 2 pin the whole set of
achievable shifts, not merely its two ends. -/

/-- Loosening the shift preserves domination: the difference is a nonnegative
multiple of the identity. -/
theorem posSemidef_sub_smul_one_of_le {k : ℕ} {block : Matrix (Fin k) (Fin k) ℂ}
    {upperShift lowerShift : ℝ}
    (hpsd : (block - ((upperShift : ℝ) : ℂ)
      • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef)
    (hle : lowerShift ≤ upperShift) :
    (block - ((lowerShift : ℝ) : ℂ)
      • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef := by
  have hslack : (0 : ℂ) ≤ ((upperShift - lowerShift : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (by linarith)
  have hrewrite : block - ((lowerShift : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)
      = (block - ((upperShift : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ))
        + ((upperShift - lowerShift : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) := by
    ext rowIndex colIndex
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [hrewrite]
  exact hpsd.add (Matrix.PosSemidef.one.smul hslack)

/-- The shifts at which some `3`-subset of the trine still dominates. -/
def trineDominatedShifts : Set ℝ :=
  {shift : ℝ | ∃ subset : Finset (Fin 6), subset.card = 3 ∧
    ((∑ c ∈ subset, complexAtom (trineDesign.atom c))
      - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef}

/-- **The achievable shifts are exactly `(-inf, 3 - sqrt 5]`.** Below the margin
the binding triple still works, by monotonicity; above it nothing works, by the
twenty-case enumeration. -/
theorem trineDominatedShifts_eq_Iic :
    trineDominatedShifts = Set.Iic trineMarginRankThree := by
  ext shift
  constructor
  · rintro ⟨subset, hcard, hpsd⟩
    by_contra hcontra
    exact trine_no_triple_above_margin shift (lt_of_not_ge hcontra) subset hcard hpsd
  · intro hle
    exact ⟨{0, 1, 3}, by decide,
      posSemidef_sub_smul_one_of_le trine_bindingTriple_psd_at_margin hle⟩

/-- **G1, in the exact form the gap asks for**: `3 - sqrt 5` IS the largest shift
at which some `3`-subset of `trineDesign` still has a positive semidefinite gap.
Membership is the binding triple `{L0, L1, R0}`; the upper bound is the
twenty-case enumeration. -/
theorem trineMargin_isGreatest :
    IsGreatest trineDominatedShifts trineMarginRankThree := by
  rw [trineDominatedShifts_eq_Iic]
  exact isGreatest_Iic

/-! ### Which subsets are BEST, exactly

The ledger's SCOPE NOTE also disclaims "that a given subset is the BEST one".
The answer is sharp: the eighteen mixed triples are ALL best, and the two
coplanar ones are the only ones that are not. -/

set_option maxHeartbeats 4000000 in
/-- **The optimal subsets, characterised.** A `3`-subset of the trine dominates
at the margin `3 - sqrt 5` if and only if it is NOT one of the two coplanar
trines. So the maximum is attained by all eighteen mixed triples simultaneously —
which is the single orbit of the order-18 automorphism group acting on the
rank-one atoms — and by nothing else. -/
theorem trine_psd_at_margin_iff (subset : Finset (Fin 6)) (hcard : subset.card = 3) :
    ((∑ c ∈ subset, complexAtom (trineDesign.atom c))
        - ((trineMarginRankThree : ℝ) : ℂ)
          • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef
      ↔ subset ≠ {0, 1, 2} ∧ subset ≠ {3, 4, 5} := by
  constructor
  · intro hpsd
    rw [trineDesign_atom] at hpsd
    refine ⟨?_, ?_⟩
    · intro hcoplanar
      rw [hcoplanar, tripleAtomSum_expand 0 1 2 (by decide) (by decide),
        trineAtom_zero, trineAtom_one, trineAtom_two] at hpsd
      exact trinePureLeft_not_psd_above trineMarginRankThree trineMargin_pos hpsd
    · intro hcoplanar
      rw [hcoplanar, tripleAtomSum_expand 3 4 5 (by decide) (by decide),
        trineAtom_three, trineAtom_four, trineAtom_five] at hpsd
      exact trinePureRight_not_psd_above trineMarginRankThree trineMargin_pos hpsd
  · rintro ⟨hnotLeft, hnotRight⟩
    rw [trineDesign_atom]
    have hexpand := tripleAtomSum_expand
    rcases tripleSubset_enumeration subset hcard with
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact absurd h hnotLeft
    · rw [h, hexpand 0 1 3 (by decide) (by decide), trineAtom_zero, trineAtom_one,
        trineAtom_three]
      exact trineMixedLeftPair_psd_at_margin 0 1 0 (by decide)
    · rw [h, hexpand 0 1 4 (by decide) (by decide), trineAtom_zero, trineAtom_one,
        trineAtom_four]
      exact trineMixedLeftPair_psd_at_margin 0 1 1 (by decide)
    · rw [h, hexpand 0 1 5 (by decide) (by decide), trineAtom_zero, trineAtom_one,
        trineAtom_five]
      exact trineMixedLeftPair_psd_at_margin 0 1 2 (by decide)
    · rw [h, hexpand 0 2 3 (by decide) (by decide), trineAtom_zero, trineAtom_two,
        trineAtom_three]
      exact trineMixedLeftPair_psd_at_margin 0 2 0 (by decide)
    · rw [h, hexpand 0 2 4 (by decide) (by decide), trineAtom_zero, trineAtom_two,
        trineAtom_four]
      exact trineMixedLeftPair_psd_at_margin 0 2 1 (by decide)
    · rw [h, hexpand 0 2 5 (by decide) (by decide), trineAtom_zero, trineAtom_two,
        trineAtom_five]
      exact trineMixedLeftPair_psd_at_margin 0 2 2 (by decide)
    · rw [h, hexpand 1 2 3 (by decide) (by decide), trineAtom_one, trineAtom_two,
        trineAtom_three]
      exact trineMixedLeftPair_psd_at_margin 1 2 0 (by decide)
    · rw [h, hexpand 1 2 4 (by decide) (by decide), trineAtom_one, trineAtom_two,
        trineAtom_four]
      exact trineMixedLeftPair_psd_at_margin 1 2 1 (by decide)
    · rw [h, hexpand 1 2 5 (by decide) (by decide), trineAtom_one, trineAtom_two,
        trineAtom_five]
      exact trineMixedLeftPair_psd_at_margin 1 2 2 (by decide)
    · rw [h, hexpand 0 3 4 (by decide) (by decide), trineAtom_zero, trineAtom_three,
        trineAtom_four]
      exact trineMixedRightPair_psd_at_margin 0 0 1 (by decide)
    · rw [h, hexpand 0 3 5 (by decide) (by decide), trineAtom_zero, trineAtom_three,
        trineAtom_five]
      exact trineMixedRightPair_psd_at_margin 0 0 2 (by decide)
    · rw [h, hexpand 0 4 5 (by decide) (by decide), trineAtom_zero, trineAtom_four,
        trineAtom_five]
      exact trineMixedRightPair_psd_at_margin 0 1 2 (by decide)
    · rw [h, hexpand 1 3 4 (by decide) (by decide), trineAtom_one, trineAtom_three,
        trineAtom_four]
      exact trineMixedRightPair_psd_at_margin 1 0 1 (by decide)
    · rw [h, hexpand 1 3 5 (by decide) (by decide), trineAtom_one, trineAtom_three,
        trineAtom_five]
      exact trineMixedRightPair_psd_at_margin 1 0 2 (by decide)
    · rw [h, hexpand 1 4 5 (by decide) (by decide), trineAtom_one, trineAtom_four,
        trineAtom_five]
      exact trineMixedRightPair_psd_at_margin 1 1 2 (by decide)
    · rw [h, hexpand 2 3 4 (by decide) (by decide), trineAtom_two, trineAtom_three,
        trineAtom_four]
      exact trineMixedRightPair_psd_at_margin 2 0 1 (by decide)
    · rw [h, hexpand 2 3 5 (by decide) (by decide), trineAtom_two, trineAtom_three,
        trineAtom_five]
      exact trineMixedRightPair_psd_at_margin 2 0 2 (by decide)
    · rw [h, hexpand 2 4 5 (by decide) (by decide), trineAtom_two, trineAtom_four,
        trineAtom_five]
      exact trineMixedRightPair_psd_at_margin 2 1 2 (by decide)
    · exact absurd h hnotRight

set_option maxHeartbeats 4000000 in
/-- **The orbit count, kernel-checked and tied to the design.** Of the twenty
`3`-subsets of `Fin 6`, exactly two are the coplanar trines and exactly eighteen
are mixed; and a subset attains the margin precisely when it is mixed. The
eighteen are a single orbit of the order-18 unitary automorphism group
`(Z/3 x Z/3) semidirect Z/2` ACTING ON THE RANK-ONE ATOMS — the two independent
`Z/3` generators `diag(w^a, w^b, 1)` permute the atoms only up to a unimodular
phase, NOT the atom vectors themselves, so the vectorwise stabiliser is much
smaller. That group-theoretic reading is NOT mechanized and is not needed: the
count and the characterisation are both kernel-checked here without it. -/
theorem trine_optimalSubsets_count :
    (Finset.univ.powersetCard 3 : Finset (Finset (Fin 6))).card = 20
      ∧ ((Finset.univ.powersetCard 3 : Finset (Finset (Fin 6))).filter
          (fun subset => subset = {0, 1, 2} ∨ subset = {3, 4, 5})).card = 2
      ∧ ((Finset.univ.powersetCard 3 : Finset (Finset (Fin 6))).filter
          (fun subset => ¬ (subset = {0, 1, 2} ∨ subset = {3, 4, 5}))).card = 18
      ∧ ∀ subset ∈ (Finset.univ.powersetCard 3 : Finset (Finset (Fin 6))),
          (((∑ c ∈ subset, complexAtom (trineDesign.atom c))
              - ((trineMarginRankThree : ℝ) : ℂ)
                • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef
            ↔ ¬ (subset = {0, 1, 2} ∨ subset = {3, 4, 5})) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro subset hmem
  have hcard : subset.card = 3 := (Finset.mem_powersetCard.mp hmem).2
  rw [trine_psd_at_margin_iff subset hcard, not_or]

/-- **The coplanar class's value is exactly `0`.** A whole trine spans a plane,
so its atom block is singular: it dominates at shift `0` and at no positive
shift. Together with `trineMargin_isGreatest` this pins both spectral classes of
the twenty triples — `0` on the two coplanar ones, `3 - sqrt 5` on the eighteen
mixed ones. -/
theorem trinePureLeft_dominatedShifts_isGreatest_zero :
    IsGreatest {shift : ℝ |
        ((∑ c ∈ ({0, 1, 2} : Finset (Fin 6)), complexAtom (trineDesign.atom c))
          - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef} 0 := by
  constructor
  · show ((∑ c ∈ ({0, 1, 2} : Finset (Fin 6)), complexAtom (trineDesign.atom c))
      - (((0 : ℝ) : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef
    rw [trineDesign_atom, tripleAtomSum_expand 0 1 2 (by decide) (by decide),
      trineAtom_zero, trineAtom_one, trineAtom_two]
    simp only [Complex.ofReal_zero, zero_smul, sub_zero]
    exact (complexAtom_posSemidef _).add
      ((complexAtom_posSemidef _).add (complexAtom_posSemidef _))
  · intro shift hshift
    by_contra hcontra
    have hpos : 0 < shift := lt_of_not_ge hcontra
    have hpsd : (complexAtom (trineLeft 0)
        + (complexAtom (trineLeft 1) + complexAtom (trineLeft 2))
        - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
      have hmem := hshift
      rw [Set.mem_setOf_eq, trineDesign_atom,
        tripleAtomSum_expand 0 1 2 (by decide) (by decide),
        trineAtom_zero, trineAtom_one, trineAtom_two] at hmem
      exact hmem
    exact trinePureLeft_not_psd_above shift hpos hpsd

/-! ## Part 4: `3 - sqrt 5` really is an EIGENVALUE

Parts 1-3 are Loewner statements, which is exactly what `ComplexDominates` needs.
They do not by themselves assert that `3 - sqrt 5` belongs to the spectrum. This
part exhibits the kernel vector explicitly and proves the converse bound with no
spectral theorem: positive semidefiniteness of the shifted block already forces
every eigenvalue to be real and at least the shift. -/

/-- **Positive semidefiniteness of a shifted block bounds the whole spectrum**,
with no spectral theorem: if `block - level . I` is positive semidefinite and
`block v = mu v` with `v /= 0`, then `mu` is real and `mu >= level`, because
`0 <= <v, (block - level I) v> = (mu - level) |v|^2` and `|v|^2 > 0`. -/
theorem eigenvalue_real_and_ge_of_posSemidef_sub {k : ℕ}
    {block : Matrix (Fin k) (Fin k) ℂ} {level : ℝ}
    (hpsd : (block - ((level : ℝ) : ℂ)
      • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef)
    {eigenvalue : ℂ} {eigenvector : Fin k → ℂ} (hne : eigenvector ≠ 0)
    (heigen : block *ᵥ eigenvector = eigenvalue • eigenvector) :
    eigenvalue.im = 0 ∧ level ≤ eigenvalue.re := by
  have hnormPos : (0 : ℂ) < star eigenvector ⬝ᵥ eigenvector :=
    dotProduct_star_self_pos_iff.mpr hne
  have hshifted : (block - ((level : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ))
      *ᵥ eigenvector = (eigenvalue - ((level : ℝ) : ℂ)) • eigenvector := by
    rw [Matrix.sub_mulVec, heigen, smul_mulVec, Matrix.one_mulVec, sub_smul]
  have hquad := hpsd.dotProduct_mulVec_nonneg eigenvector
  rw [hshifted, dotProduct_smul, smul_eq_mul] at hquad
  obtain ⟨hreNonneg, hImZero⟩ := Complex.le_def.mp hquad
  obtain ⟨hnormRe, hnormIm⟩ := Complex.lt_def.mp hnormPos
  simp only [Complex.zero_re, Complex.zero_im] at hreNonneg hImZero hnormRe hnormIm
  rw [Complex.mul_re] at hreNonneg
  rw [Complex.mul_im] at hImZero
  rw [← hnormIm] at hreNonneg hImZero
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero, mul_zero, zero_add] at hreNonneg hImZero
  refine ⟨?_, ?_⟩
  · nlinarith [hreNonneg, hImZero, hnormRe]
  · nlinarith [hreNonneg, hImZero, hnormRe]

/-- The kernel vector of the binding excess, pair on the first axis:
`w = (-(sqrt5 - 1)(conj p + conj q), -(sqrt5 + 1) conj r, 2 t)`. It is orthogonal
to both atoms of the binding decomposition, hence annihilated by the excess. -/
noncomputable def splitPairLeftNullVector
    (legAmp firstPhase secondPhase thirdPhase rootFive : ℂ) : Fin 3 → ℂ :=
  ![-(rootFive - 1) * ((starRingEnd ℂ) firstPhase + (starRingEnd ℂ) secondPhase),
    -(rootFive + 1) * (starRingEnd ℂ) thirdPhase,
    2 * legAmp]

theorem splitPairLeftNullVector_orthogonal_pairAtom
    (legAmp firstPhase secondPhase thirdPhase rootFive : ℂ)
    (hlegReal : (starRingEnd ℂ) legAmp = legAmp) (hlegSq : legAmp * legAmp = 2)
    (hrootReal : (starRingEnd ℂ) rootFive = rootFive)
    (hrootSq : rootFive * rootFive = 5) :
    star (![1 + rootFive, 0, legAmp * (firstPhase + secondPhase)] : Fin 3 → ℂ)
        ⬝ᵥ splitPairLeftNullVector legAmp firstPhase secondPhase thirdPhase rootFive
      = 0 := by
  simp only [splitPairLeftNullVector, dotProduct, Fin.sum_univ_three, Pi.star_apply,
    RCLike.star_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, map_add, map_one, map_zero, map_mul, hlegReal,
    hrootReal]
  linear_combination (-((starRingEnd ℂ) firstPhase + (starRingEnd ℂ) secondPhase)) * hrootSq
    + (2 * ((starRingEnd ℂ) firstPhase + (starRingEnd ℂ) secondPhase)) * hlegSq

theorem splitPairLeftNullVector_orthogonal_singleAtom
    (legAmp firstPhase secondPhase thirdPhase rootFive : ℂ)
    (hlegReal : (starRingEnd ℂ) legAmp = legAmp) (hlegSq : legAmp * legAmp = 2)
    (hrootReal : (starRingEnd ℂ) rootFive = rootFive)
    (hrootSq : rootFive * rootFive = 5) :
    star (![0, rootFive - 1, legAmp * thirdPhase] : Fin 3 → ℂ)
        ⬝ᵥ splitPairLeftNullVector legAmp firstPhase secondPhase thirdPhase rootFive
      = 0 := by
  simp only [splitPairLeftNullVector, dotProduct, Fin.sum_univ_three, Pi.star_apply,
    RCLike.star_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, map_sub, map_one, map_zero, map_mul, hlegReal,
    hrootReal]
  linear_combination (-(starRingEnd ℂ) thirdPhase) * hrootSq
    + (2 * (starRingEnd ℂ) thirdPhase) * hlegSq

/-- The kernel vector is nonzero — its last entry is `2 t` and `t^2 = 2`. -/
theorem splitPairLeftNullVector_ne_zero
    (legAmp firstPhase secondPhase thirdPhase rootFive : ℂ)
    (hlegSq : legAmp * legAmp = 2) :
    splitPairLeftNullVector legAmp firstPhase secondPhase thirdPhase rootFive ≠ 0 := by
  intro hzero
  have hentry : splitPairLeftNullVector legAmp firstPhase secondPhase thirdPhase
      rootFive 2 = 0 := by rw [hzero]; rfl
  simp only [splitPairLeftNullVector, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hentry
  have hlegZero : legAmp = 0 := by
    rcases mul_eq_zero.mp hentry with hcontra | hgood
    · exact absurd hcontra (by norm_num)
    · exact hgood
  rw [hlegZero] at hlegSq
  norm_num at hlegSq

/-- The binding excess annihilates the kernel vector. -/
theorem splitPairLeft_binding_mulVec_zero
    (legAmp firstPhase secondPhase thirdPhase rootFive : ℂ)
    (hlegReal : (starRingEnd ℂ) legAmp = legAmp) (hlegSq : legAmp * legAmp = 2)
    (hrootReal : (starRingEnd ℂ) rootFive = rootFive)
    (hrootSq : rootFive * rootFive = 5)
    (hunitFirst : (starRingEnd ℂ) firstPhase * firstPhase = 1)
    (hunitSecond : (starRingEnd ℂ) secondPhase * secondPhase = 1)
    (hunitThird : (starRingEnd ℂ) thirdPhase * thirdPhase = 1)
    (hcross : (starRingEnd ℂ) firstPhase * secondPhase
      + (starRingEnd ℂ) secondPhase * firstPhase = -1) :
    (complexAtom ![legAmp, 0, firstPhase]
        + (complexAtom ![legAmp, 0, secondPhase] + complexAtom ![0, legAmp, thirdPhase])
        - (3 - rootFive) • (1 : Matrix (Fin 3) (Fin 3) ℂ))
      *ᵥ splitPairLeftNullVector legAmp firstPhase secondPhase thirdPhase rootFive
      = 0 := by
  rw [splitPairLeft_binding_decomp legAmp firstPhase secondPhase thirdPhase rootFive
      hlegReal hlegSq hrootReal hrootSq hunitFirst hunitSecond hunitThird hcross,
    Matrix.add_mulVec, smul_mulVec, smul_mulVec, complexAtom_mulVec, complexAtom_mulVec,
    splitPairLeftNullVector_orthogonal_pairAtom legAmp firstPhase secondPhase thirdPhase
      rootFive hlegReal hlegSq hrootReal hrootSq,
    splitPairLeftNullVector_orthogonal_singleAtom legAmp firstPhase secondPhase thirdPhase
      rootFive hlegReal hlegSq hrootReal hrootSq]
  simp

/-- **The kernel vector is an eigenvector at the binding shift**: the mixed
triple's atom block sends it to `(3 - sqrt5)` times itself. -/
theorem splitPairLeft_binding_mulVec
    (legAmp firstPhase secondPhase thirdPhase rootFive : ℂ)
    (hlegReal : (starRingEnd ℂ) legAmp = legAmp) (hlegSq : legAmp * legAmp = 2)
    (hrootReal : (starRingEnd ℂ) rootFive = rootFive)
    (hrootSq : rootFive * rootFive = 5)
    (hunitFirst : (starRingEnd ℂ) firstPhase * firstPhase = 1)
    (hunitSecond : (starRingEnd ℂ) secondPhase * secondPhase = 1)
    (hunitThird : (starRingEnd ℂ) thirdPhase * thirdPhase = 1)
    (hcross : (starRingEnd ℂ) firstPhase * secondPhase
      + (starRingEnd ℂ) secondPhase * firstPhase = -1) :
    (complexAtom ![legAmp, 0, firstPhase]
        + (complexAtom ![legAmp, 0, secondPhase] + complexAtom ![0, legAmp, thirdPhase]))
      *ᵥ splitPairLeftNullVector legAmp firstPhase secondPhase thirdPhase rootFive
      = (3 - rootFive)
        • splitPairLeftNullVector legAmp firstPhase secondPhase thirdPhase rootFive := by
  have hzero := splitPairLeft_binding_mulVec_zero legAmp firstPhase secondPhase thirdPhase
    rootFive hlegReal hlegSq hrootReal hrootSq hunitFirst hunitSecond hunitThird hcross
  rw [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hzero
  exact hzero

/-! ### The concrete eigenvector of the trine's binding triple -/

/-- The kernel vector of the trine's binding triple `{L0, L1, R0}`, written out:
`(-(sqrt5 - 1)(1 + w^2), -(sqrt5 + 1), 2 sqrt2)`, of squared length `20`. -/
noncomputable def trineBindingNullVector : Fin 3 → ℂ :=
  splitPairLeftNullVector topAmpC (omegaPow 0) (omegaPow 1) (omegaPow 0) rootFiveC

theorem trineBindingNullVector_ne_zero : trineBindingNullVector ≠ 0 :=
  splitPairLeftNullVector_ne_zero topAmpC (omegaPow 0) (omegaPow 1) (omegaPow 0)
    rootFiveC topAmpC_sq

/-- **The trine's binding triple sends its kernel vector to `(3 - sqrt5)` times
itself** — so `3 - sqrt 5` genuinely belongs to the spectrum, not merely to the
set of shifts that keep the excess positive semidefinite. -/
theorem trineBinding_mulVec_nullVector :
    (∑ c ∈ ({0, 1, 3} : Finset (Fin 6)), complexAtom (trineDesign.atom c))
        *ᵥ trineBindingNullVector
      = ((trineMarginRankThree : ℝ) : ℂ) • trineBindingNullVector := by
  rw [trineDesign_atom, tripleAtomSum_expand 0 1 3 (by decide) (by decide),
    trineAtom_zero, trineAtom_one, trineAtom_three, trineMargin_cast,
    show (trineLeft 0) = ![topAmpC, 0, omegaPow 0] from rfl,
    show (trineLeft 1) = ![topAmpC, 0, omegaPow 1] from rfl,
    show (trineRight 0) = ![0, topAmpC, omegaPow 0] from rfl]
  exact splitPairLeft_binding_mulVec topAmpC (omegaPow 0) (omegaPow 1) (omegaPow 0)
    rootFiveC topAmpC_conj topAmpC_sq rootFiveC_conj rootFiveC_sq (omegaPow_unit _)
    (omegaPow_unit _) (omegaPow_unit _) (omegaPow_cross (by decide))

/-- **Every eigenvalue of the binding triple's atom block is real and at least
`3 - sqrt 5`.** Elementary: the shifted block is positive semidefinite. -/
theorem trineBinding_spectrum_real_and_ge {eigenvalue : ℂ} {eigenvector : Fin 3 → ℂ}
    (hne : eigenvector ≠ 0)
    (heigen : (∑ c ∈ ({0, 1, 3} : Finset (Fin 6)), complexAtom (trineDesign.atom c))
      *ᵥ eigenvector = eigenvalue • eigenvector) :
    eigenvalue.im = 0 ∧ trineMarginRankThree ≤ eigenvalue.re :=
  eigenvalue_real_and_ge_of_posSemidef_sub trine_bindingTriple_psd_at_margin hne heigen

/-- **`3 - sqrt 5` IS the least eigenvalue of the trine's binding triple**, in the
ordinary sense of the words: it is an eigenvalue, and no eigenvalue is smaller.
This is the statement the ledger's SCOPE NOTE disclaimed. -/
theorem trineBinding_leastEigenvalue :
    IsLeast {eigenvalue : ℝ | ∃ eigenvector : Fin 3 → ℂ, eigenvector ≠ 0
      ∧ (∑ c ∈ ({0, 1, 3} : Finset (Fin 6)), complexAtom (trineDesign.atom c))
          *ᵥ eigenvector = ((eigenvalue : ℝ) : ℂ) • eigenvector}
      trineMarginRankThree := by
  constructor
  · exact ⟨trineBindingNullVector, trineBindingNullVector_ne_zero,
      trineBinding_mulVec_nullVector⟩
  · rintro candidate ⟨eigenvector, hne, heigen⟩
    have hbound := trineBinding_spectrum_real_and_ge hne heigen
    simpa using hbound.2

/-- **G1, ASSEMBLED.** Four statements about the shared-axis trine, all
kernel-checked, that together say `3 - sqrt 5` is the design's exact rank-3
value and identify the optimal subsets:

* the set of shifts at which SOME `3`-subset dominates is exactly
  `(-inf, 3 - sqrt 5]`, with `3 - sqrt 5` its greatest element;
* `3 - sqrt 5` is the LEAST EIGENVALUE of the binding triple's atom block, with
  an explicit eigenvector;
* the subsets that attain the margin are exactly the eighteen mixed triples —
  the single orbit of the order-18 automorphism group ACTING ON THE RANK-ONE
  ATOMS, i.e. up to a unimodular phase per atom (the diagonal generators do NOT
  fix the atom VECTORS) — the two coplanar trines being the only failures;
* hence the design's value is `3 - sqrt 5`.

The first and third items are the LOEWNER form of
`max_{|subset| = 3} lambda_min = 3 - sqrt 5`, holding for every `3`-subset; the
second is the EIGENVALUE form, holding for the binding triple only. The bridge
between the two readings needs the spectral theorem and is not mechanized here.
`Gtz/Complex/SharpConstantLedger.lean` carried both only as an audited reading
(its SCOPE NOTE, first two disclaimed items); that note is superseded by this
file for the Loewner form and for the binding triple's spectrum, and still
stands for `sigma_min(G_C) ^ 2 = lambda_min(S_C)`. The refutation
`complexGtzWeighted_six_three_fails_via_trine` is the special case `shift = 1`,
since `3 - sqrt 5 < 1`. -/
theorem trineMargin_isExactRankThreeValue :
    IsGreatest trineDominatedShifts trineMarginRankThree
      ∧ IsLeast {eigenvalue : ℝ | ∃ eigenvector : Fin 3 → ℂ, eigenvector ≠ 0
          ∧ (∑ c ∈ ({0, 1, 3} : Finset (Fin 6)), complexAtom (trineDesign.atom c))
              *ᵥ eigenvector = ((eigenvalue : ℝ) : ℂ) • eigenvector}
          trineMarginRankThree
      ∧ (∀ subset : Finset (Fin 6), subset.card = 3 →
          (((∑ c ∈ subset, complexAtom (trineDesign.atom c))
              - ((trineMarginRankThree : ℝ) : ℂ)
                • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef
            ↔ subset ≠ {0, 1, 2} ∧ subset ≠ {3, 4, 5}))
      ∧ trineDominatedShifts = Set.Iic trineMarginRankThree :=
  ⟨trineMargin_isGreatest, trineBinding_leastEigenvalue, trine_psd_at_margin_iff,
    trineDominatedShifts_eq_Iic⟩

/-! # Part C. The Hesse SIC: the rank-three record

`Gtz/Complex/SharpConstantLedger.lean` names two rank-3 candidates and does not
compare them: the shared-axis trine, whose margin `3 - sqrt 5` it proves, and a
"Hesse cubic" `8 x^3 - 72 x^2 + 162 x - 81` whose root it brackets in
`(0.70, 0.71)` while carrying the identification of that root with a Hesse-SIC
subset gap only as prose (EXACT ELSEWHERE, no design object anywhere in the
repository).  This part settles the comparison and mechanizes the missing object.

Note the correction is to the CONSTANT, not to SIC-extremality: the new record is
itself a SIC, in `ℂ³` rather than `ℂ²`. -/

/-! ## The nine Hesse directions, over the Eisenstein integers -/

/-- `conj (omega ^ 2) = omega`: conjugation keeps a cube root in degree one,
which is what keeps every overlap polynomial small. -/
theorem omegaRoot_conj_sq : (starRingEnd ℂ) (omegaRoot ^ 2) = omegaRoot := by
  rw [map_pow, omegaRoot_conj_eq]
  linear_combination omegaRoot * omegaRoot_cube

/-- The three-slot Hermitian pairing, written out. -/
theorem starDot_triple (firstZero firstOne firstTwo secondZero secondOne secondTwo : ℂ) :
    star ![firstZero, firstOne, firstTwo] ⬝ᵥ ![secondZero, secondOne, secondTwo]
      = (starRingEnd ℂ) firstZero * secondZero
        + (starRingEnd ℂ) firstOne * secondOne
        + (starRingEnd ℂ) firstTwo * secondTwo := by
  simp [dotProduct, Fin.sum_univ_three, Pi.star_apply, RCLike.star_def]

/-- Nine summands, expanded. -/
theorem sumUnivNine {carrier : Type*} [AddCommMonoid carrier] (entries : Fin 9 → carrier) :
    ∑ index, entries index
      = entries 0 + entries 1 + entries 2 + entries 3 + entries 4 + entries 5
        + entries 6 + entries 7 + entries 8 := by
  simp [Fin.sum_univ_succ, add_assoc]

/-- **The nine Hesse directions in `Z[omega]`.** Indexed by a zero slot `p` and a
phase `q`, the vector carries `0` in slot `p`, `omega ^ q` in slot `p + 1` and
`-omega ^ (2 q)` in slot `p + 2`. Every entry is an Eisenstein integer, every
squared length is `2`, and every distinct pairing is a cube root of `-1`. -/
noncomputable def hesseUnit : Fin 9 → Fin 3 → ℂ :=
  ![![0, 1, -1],
    ![0, omegaRoot, -omegaRoot ^ 2],
    ![0, omegaRoot ^ 2, -omegaRoot],
    ![-1, 0, 1],
    ![-omegaRoot ^ 2, 0, omegaRoot],
    ![-omegaRoot, 0, omegaRoot ^ 2],
    ![1, -1, 0],
    ![omegaRoot, -omegaRoot ^ 2, 0],
    ![omegaRoot ^ 2, -omegaRoot, 0]]

set_option maxHeartbeats 4000000 in
/-- Every Hesse direction has squared length exactly `2`. -/
theorem hesseUnit_leverage (index : Fin 9) :
    star (hesseUnit index) ⬝ᵥ hesseUnit index = 2 := by
  fin_cases index <;>
    simp only [Fin.reduceFinMk, hesseUnit, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, starDot_triple, map_zero, map_one, map_neg,
      omegaRoot_conj_eq, omegaRoot_conj_sq] <;>
    first
      | ring1
      | linear_combination (2 : ℂ) * omegaRoot_cube

set_option maxHeartbeats 4000000 in
/-- **Every distinct pairing of Hesse directions is a cube root of `-1`.** The
overlap is always `-omega ^ a` for some `a`, so its cube is `-1` with no
reference to which `a`. This single scalar identity carries the whole
thirty-six entry overlap table, and it is the only combinatorial input the
refutation below needs. -/
theorem hesseUnit_overlapCube {firstIndex secondIndex : Fin 9}
    (hne : firstIndex ≠ secondIndex) :
    (star (hesseUnit firstIndex) ⬝ᵥ hesseUnit secondIndex) ^ 3 = -1 := by
  fin_cases firstIndex <;> fin_cases secondIndex <;>
    simp only [Fin.reduceFinMk, hesseUnit, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, starDot_triple, map_zero, map_one, map_neg,
      omegaRoot_conj_eq, omegaRoot_conj_sq] <;>
    first
      | exact absurd rfl hne
      | ring1
      | linear_combination (-1 : ℂ) * omegaRoot_cube
      | linear_combination (-(omegaRoot ^ 3 + 1)) * omegaRoot_cube
      | linear_combination (-(omegaRoot ^ 6 + omegaRoot ^ 3 + 1)) * omegaRoot_cube
      | linear_combination (-(omegaRoot ^ 9 + omegaRoot ^ 6 + omegaRoot ^ 3 + 1))
          * omegaRoot_cube
      | linear_combination (omegaRoot ^ 3 + 3 * omegaRoot ^ 2 + 3 * omegaRoot + 2)
            * omegaRoot_cube + (3 : ℂ) * omegaRoot_sum
      | linear_combination (omegaRoot ^ 9 + 3 * omegaRoot ^ 7 + omegaRoot ^ 6
            + 3 * omegaRoot ^ 5 + 3 * omegaRoot ^ 4 + 2 * omegaRoot ^ 3
            + 3 * omegaRoot ^ 2 + 3 * omegaRoot + 2) * omegaRoot_cube
          + (3 : ℂ) * omegaRoot_sum

set_option maxHeartbeats 4000000 in
/-- The nine directions resolve `6 . I`: a tight frame, hence a design once
scaled. -/
theorem hesseUnit_parseval :
    ∑ index, complexAtom (hesseUnit index)
      = (6 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext rowIndex colIndex
  rw [Matrix.sum_apply, sumUnivNine]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, complexAtom_apply,
      hesseUnit, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, map_zero, map_one, map_neg,
      omegaRoot_conj_eq, omegaRoot_conj_sq, Fin.isValue, Fin.reduceEq, reduceIte] <;>
    first
      | linear_combination (4 : ℂ) * omegaRoot_cube
      | linear_combination (-omegaRoot) * omegaRoot_cube + (-1 : ℂ) * omegaRoot_sum

/-! ## The Hesse SIC as a complex weighted `(9,3)` design -/

/-- The amplitude that lifts a Hesse direction to leverage `3`. -/
noncomputable def hesseAmpC : ℂ := ((Real.sqrt (3 / 2) : ℝ) : ℂ)

theorem hesseAmpC_conj : (starRingEnd ℂ) hesseAmpC = hesseAmpC :=
  Complex.conj_ofReal _

theorem hesseAmpC_sq : hesseAmpC * hesseAmpC = 3 / 2 := by
  rw [hesseAmpC, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  norm_num

/-- The nine Hesse atoms: the directions scaled so that uniform weight `1/9`
resolves the identity. -/
noncomputable def hesseAtom (index : Fin 9) : Fin 3 → ℂ := hesseAmpC • hesseUnit index

/-- Scaling leaves the pairing as the squared amplitude times the direction
pairing. -/
theorem hesseAtom_starDot (firstIndex secondIndex : Fin 9) :
    star (hesseAtom firstIndex) ⬝ᵥ hesseAtom secondIndex
      = 3 / 2 * (star (hesseUnit firstIndex) ⬝ᵥ hesseUnit secondIndex) := by
  simp only [hesseAtom, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    RCLike.star_def, hesseAmpC_conj]
  linear_combination (star (hesseUnit firstIndex) ⬝ᵥ hesseUnit secondIndex) * hesseAmpC_sq

/-- Leverage exactly `3`: the design is a unit-norm tight frame, cap `1`. -/
theorem hesseAtom_leverage (index : Fin 9) :
    star (hesseAtom index) ⬝ᵥ hesseAtom index = 3 := by
  rw [hesseAtom_starDot, hesseUnit_leverage]
  norm_num

theorem hesseAtom_overlapCube {firstIndex secondIndex : Fin 9}
    (hne : firstIndex ≠ secondIndex) :
    (star (hesseAtom firstIndex) ⬝ᵥ hesseAtom secondIndex) ^ 3 = -(27 / 8) := by
  rw [hesseAtom_starDot, mul_pow, hesseUnit_overlapCube hne]
  norm_num

/-- A nonnegative real is pinned by its cube. -/
theorem eq_of_cube_eq_cube_of_nonneg {value target : ℝ}
    (hvalue : 0 ≤ value) (htarget : 0 ≤ target) (hcube : value ^ 3 = target ^ 3) :
    value = target := by
  have hfactor : (value - target) * (value ^ 2 + value * target + target ^ 2) = 0 := by
    linear_combination hcube
  rcases mul_eq_zero.mp hfactor with hzero | hquad
  · linarith
  · nlinarith [hquad, hvalue, htarget, sq_nonneg value, sq_nonneg target,
      mul_nonneg hvalue htarget]

/-- **Equiangularity, from the cube alone.** Every distinct pair of Hesse atoms
has overlap product exactly `9/4`: the product is the squared modulus, a
nonnegative real, and its cube is `(9/4) ^ 3`. -/
theorem hesseAtom_overlapModulus {firstIndex secondIndex : Fin 9}
    (hne : firstIndex ≠ secondIndex) :
    (star (hesseAtom firstIndex) ⬝ᵥ hesseAtom secondIndex)
      * (star (hesseAtom secondIndex) ⬝ᵥ hesseAtom firstIndex) = 9 / 4 := by
  have hconj : star (hesseAtom secondIndex) ⬝ᵥ hesseAtom firstIndex
      = (starRingEnd ℂ) (star (hesseAtom firstIndex) ⬝ᵥ hesseAtom secondIndex) :=
    (starDot_conj _ _).symm
  have hmapped : Complex.normSq
      ((star (hesseAtom firstIndex) ⬝ᵥ hesseAtom secondIndex) ^ 3)
      = Complex.normSq (star (hesseAtom firstIndex) ⬝ᵥ hesseAtom secondIndex) ^ 3 :=
    map_pow Complex.normSq _ 3
  rw [hesseAtom_overlapCube hne] at hmapped
  have hcube : Complex.normSq (star (hesseAtom firstIndex) ⬝ᵥ hesseAtom secondIndex) ^ 3
      = (9 / 4 : ℝ) ^ 3 := by
    rw [← hmapped, Complex.normSq_apply]
    norm_num
  have hnorm : Complex.normSq (star (hesseAtom firstIndex) ⬝ᵥ hesseAtom secondIndex)
      = 9 / 4 :=
    eq_of_cube_eq_cube_of_nonneg (Complex.normSq_nonneg _) (by norm_num) hcube
  rw [hconj, Complex.mul_conj, hnorm]
  norm_num

/-- **The phase quantization.** The triangle invariant of any three distinct
Hesse atoms cubes to `-(27/8) ^ 3`, because each of its three factors cubes to
`-27/8`. -/
theorem hesseTriple_bargmannCube {firstIndex secondIndex thirdIndex : Fin 9}
    (hfirstSecond : firstIndex ≠ secondIndex) (hsecondThird : secondIndex ≠ thirdIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) :
    triangleBargmann (hesseAtom firstIndex) (hesseAtom secondIndex)
        (hesseAtom thirdIndex) ^ 3
      = -((((27 : ℝ) / 8) ^ 3 : ℝ) : ℂ) := by
  rw [triangleBargmann, mul_pow, mul_pow, hesseAtom_overlapCube hfirstSecond,
    hesseAtom_overlapCube hsecondThird, hesseAtom_overlapCube (Ne.symm hfirstThird)]
  push_cast
  ring

/-- A cube root of a negative real has real part at most half the radius: the
three roots are `-r` and `r/2 +- i r sqrt 3 / 2`, and `r/2` is the largest. -/
theorem re_le_half_of_cube_eq_neg {value : ℂ} {radius : ℝ} (hradius : 0 < radius)
    (hcube : value ^ 3 = -((radius ^ 3 : ℝ) : ℂ)) : value.re ≤ radius / 2 := by
  have hrealPart : (value ^ 3).re = value.re ^ 3 - 3 * value.re * value.im ^ 2 := by
    simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im]
    ring
  have himagPart : (value ^ 3).im = 3 * value.re ^ 2 * value.im - value.im ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im]
    ring
  rw [hcube] at hrealPart himagPart
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
    neg_zero] at hrealPart himagPart
  by_contra hcontra
  rw [not_le] at hcontra
  have hpositive : 0 < value.re := by linarith
  have hfactor : value.im * (3 * value.re ^ 2 - value.im ^ 2) = 0 := by
    linear_combination -himagPart
  rcases mul_eq_zero.mp hfactor with hflat | hcone
  · rw [hflat] at hrealPart
    nlinarith [mul_pos (mul_pos hpositive hpositive) hpositive, pow_pos hradius 3,
      hrealPart]
  · have hpinned : 8 * value.re ^ 3 = radius ^ 3 := by
      linear_combination hrealPart + (3 * value.re) * hcone
    have hgap : 0 < 2 * value.re - radius := by linarith
    have hquad : 0 < 4 * value.re ^ 2 + 2 * value.re * radius + radius ^ 2 := by
      positivity
    nlinarith [mul_pos hgap hquad, hpinned]

/-- **`Re T <= 27/16` for every Hesse triple** — the one inequality that refutes
all eighty-four subsets at once. -/
theorem hesseTriple_bargmann_re_le {firstIndex secondIndex thirdIndex : Fin 9}
    (hfirstSecond : firstIndex ≠ secondIndex) (hsecondThird : secondIndex ≠ thirdIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) :
    (triangleBargmann (hesseAtom firstIndex) (hesseAtom secondIndex)
      (hesseAtom thirdIndex)).re ≤ 27 / 16 := by
  have hbound := re_le_half_of_cube_eq_neg (radius := (27 : ℝ) / 8) (by norm_num)
    (hesseTriple_bargmannCube hfirstSecond hsecondThird hfirstThird)
  linarith

/-! ## From the Gram block to the atom block -/

set_option maxHeartbeats 4000000 in
/-- **The atom block and the Gram block share a characteristic polynomial.** For
three vectors in `ℂ³` the atom sum is `A^H A` and the Gram matrix is `A A^H`
with `A` square, so the two shifted determinants agree — a polynomial identity in
the entries, with no positivity and no conjugation input. This is the bridge that
lets the Gram-side mechanism of `gramTripleExcess_det_split` decide subsets of a
design, whose domination test lives on the atom block. -/
theorem tripleAtomSum_shifted_det (firstVec secondVec thirdVec : Fin 3 → ℂ) (shift : ℂ) :
    (complexAtom firstVec + (complexAtom secondVec + complexAtom thirdVec)
        - shift • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det
      = (gramTriple firstVec secondVec thirdVec
        - shift • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det := by
  rw [gramTripleExcess_det_expand, Matrix.det_fin_three]
  simp only [tripleGap_apply, triangleBargmann, dotProduct, Fin.sum_univ_three,
    Pi.star_apply, RCLike.star_def, Fin.isValue, Fin.reduceEq, if_true, if_false]
  ring

/-! ## Every subset of the Hesse SIC fails wherever the Hesse cubic is positive -/

/-- The Hesse triple's shifted excess determinant in closed form: a phase-free
cubic in the shift, plus twice the triangle invariant's real part. -/
theorem hesseTriple_shifted_det {firstIndex secondIndex thirdIndex : Fin 9}
    (hfirstSecond : firstIndex ≠ secondIndex) (hsecondThird : secondIndex ≠ thirdIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) (shift : ℂ) :
    (complexAtom (hesseAtom firstIndex)
        + (complexAtom (hesseAtom secondIndex) + complexAtom (hesseAtom thirdIndex))
        - shift • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det
      = (3 - shift) ^ 3 - 27 / 4 * (3 - shift)
        + ((2 * (triangleBargmann (hesseAtom firstIndex) (hesseAtom secondIndex)
          (hesseAtom thirdIndex)).re : ℝ) : ℂ) := by
  rw [tripleAtomSum_shifted_det, gramTripleExcess_det_split,
    hesseAtom_leverage, hesseAtom_leverage, hesseAtom_leverage,
    hesseAtom_overlapModulus hsecondThird, hesseAtom_overlapModulus hfirstThird,
    hesseAtom_overlapModulus hfirstSecond]
  ring

/-- **No triple of the Hesse SIC survives a shift where the Hesse cubic is
positive.** The excess determinant is at most `-(1/8)` times
`8 s^3 - 72 s^2 + 162 s - 81`, uniformly over all eighty-four subsets, because
`Re T <= 27/16` uniformly. -/
theorem hesseTriple_not_posSemidef {firstIndex secondIndex thirdIndex : Fin 9}
    (hfirstSecond : firstIndex ≠ secondIndex) (hsecondThird : secondIndex ≠ thirdIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) (shift : ℝ)
    (hcubicPos : 0 < 8 * shift ^ 3 - 72 * shift ^ 2 + 162 * shift - 81) :
    ¬ (complexAtom (hesseAtom firstIndex)
        + (complexAtom (hesseAtom secondIndex) + complexAtom (hesseAtom thirdIndex))
        - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
  refine not_posSemidef_of_det_re_neg_gen ?_
  rw [hesseTriple_shifted_det hfirstSecond hsecondThird hfirstThird]
  have hcast : (3 - ((shift : ℝ) : ℂ)) ^ 3 - 27 / 4 * (3 - ((shift : ℝ) : ℂ))
      + ((2 * (triangleBargmann (hesseAtom firstIndex) (hesseAtom secondIndex)
          (hesseAtom thirdIndex)).re : ℝ) : ℂ)
      = (((3 - shift) ^ 3 - 27 / 4 * (3 - shift)
          + 2 * (triangleBargmann (hesseAtom firstIndex) (hesseAtom secondIndex)
            (hesseAtom thirdIndex)).re : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]
  have hphase := hesseTriple_bargmann_re_le hfirstSecond hsecondThird hfirstThird
  nlinarith [hcubicPos, hphase]

/-! ## The design -/

theorem complexAtom_hesseAtom (index : Fin 9) :
    complexAtom (hesseAtom index) = ((3 : ℂ) / 2) • complexAtom (hesseUnit index) := by
  ext rowIndex colIndex
  simp only [complexAtom_apply, hesseAtom, Pi.smul_apply, smul_eq_mul, map_mul,
    hesseAmpC_conj, Matrix.smul_apply]
  linear_combination
    (hesseUnit index rowIndex * (starRingEnd ℂ) (hesseUnit index colIndex)) * hesseAmpC_sq

/-- **The Hesse SIC is a weighted design over ℂ**: nine equiangular lines in
`ℂ³` at uniform weight `1/9`, every leverage exactly `3`, leverage cap `1`. -/
theorem hesseParseval :
    ∑ index, (((1 : ℝ) / 9 : ℝ) : ℂ) • complexAtom (hesseAtom index) = 1 := by
  have hterm : ∀ index : Fin 9,
      (((1 : ℝ) / 9 : ℝ) : ℂ) • complexAtom (hesseAtom index)
        = ((1 : ℂ) / 6) • complexAtom (hesseUnit index) := by
    intro index
    rw [complexAtom_hesseAtom, smul_smul]
    norm_num
  rw [Finset.sum_congr rfl fun index _ => hterm index, ← Finset.smul_sum,
    hesseUnit_parseval, smul_smul, show (1 : ℂ) / 6 * 6 = 1 by norm_num, one_smul]

/-- The Hesse SIC as a complex weighted `(9,3)` design. -/
noncomputable def hesseDesign : ComplexWeightedDesign 9 3 where
  atom := hesseAtom
  weight := fun _ => 1 / 9
  weight_pos := fun _ => by norm_num
  weight_sum_one := by
    rw [sumUnivNine]
    norm_num
  isParseval := hesseParseval

@[simp] theorem hesseDesign_atom : hesseDesign.atom = hesseAtom := rfl

/-- Expanding a three-element atom sum over distinct indices. -/
theorem hesseTripleSum_expand {firstIndex secondIndex thirdIndex : Fin 9}
    (hfirstSecond : firstIndex ≠ secondIndex) (hsecondThird : secondIndex ≠ thirdIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) :
    ∑ c ∈ ({firstIndex, secondIndex, thirdIndex} : Finset (Fin 9)),
        complexAtom (hesseAtom c)
      = complexAtom (hesseAtom firstIndex)
        + (complexAtom (hesseAtom secondIndex) + complexAtom (hesseAtom thirdIndex)) := by
  rw [Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
    Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton]

/-- **No `3`-subset of the Hesse SIC dominates any shift where the Hesse cubic is
positive.** All eighty-four subsets in one inequality: `Finset.card_eq_three`
names the three distinct atoms and the shape bound does the rest — no
enumeration OVER TRIPLES and no orbit analysis. (The overlap table underneath is
still established by an eighty-one-case `fin_cases` over PAIRS in
`hesseUnit_overlapCube`; the enumeration moves down a level, it does not
vanish.) -/
theorem hesse_no_triple_above (shift : ℝ)
    (hcubicPos : 0 < 8 * shift ^ 3 - 72 * shift ^ 2 + 162 * shift - 81)
    (subset : Finset (Fin 9)) (hcard : subset.card = 3) :
    ¬ ((∑ c ∈ subset, complexAtom (hesseDesign.atom c))
        - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
  obtain ⟨firstIndex, secondIndex, thirdIndex, hfirstSecond, hfirstThird, hsecondThird,
    hsubset⟩ := Finset.card_eq_three.mp hcard
  rw [hesseDesign_atom, hsubset,
    hesseTripleSum_expand hfirstSecond hsecondThird hfirstThird]
  exact hesseTriple_not_posSemidef hfirstSecond hsecondThird hfirstThird shift hcubicPos

/-- **Complex weighted `(9,3)` is FALSE, on the Hesse SIC.** The Hesse cubic at
`1` is `17 > 0`, so every one of the eighty-four triples has excess determinant
at most `-17/8`. -/
theorem complexGtzWeighted_nine_three_fails_via_hesse : ¬ ComplexGtzWeighted 9 3 := by
  intro hcontra
  obtain ⟨subset, hcard, hdom⟩ := hcontra hesseDesign
  rw [ComplexDominates] at hdom
  refine hesse_no_triple_above 1 (by norm_num) subset hcard ?_
  rw [Complex.ofReal_one, one_smul]
  exact hdom

/-! ## G3: the Hesse margin, and the comparison with the trine -/

/-- The Hesse SIC's margin at rank three: the least root of the ledger's Hesse
cubic `8 x^3 - 72 x^2 + 162 x - 81`, in closed form. -/
noncomputable def hesseMarginRankThree : ℝ := 3 * (1 - Real.cos (2 * Real.pi / 9))

/-- `cos (2 pi / 9)` satisfies `8 c^3 - 6 c + 1 = 0`, from the triplication
formula at `3 (2 pi / 9) = pi - pi / 3`. -/
theorem cosTwoPiNinth_isRoot :
    8 * Real.cos (2 * Real.pi / 9) ^ 3 - 6 * Real.cos (2 * Real.pi / 9) + 1 = 0 := by
  have htripled : Real.cos (3 * (2 * Real.pi / 9)) = -(1 / 2) := by
    have hangle : (3 : ℝ) * (2 * Real.pi / 9) = Real.pi - Real.pi / 3 := by ring
    rw [hangle, Real.cos_pi_sub, Real.cos_pi_div_three]
  rw [Real.cos_three_mul] at htripled
  linear_combination 2 * htripled

/-- **The Hesse margin is a root of the Hesse cubic.** -/
theorem hesseMargin_isRoot :
    8 * hesseMarginRankThree ^ 3 - 72 * hesseMarginRankThree ^ 2
      + 162 * hesseMarginRankThree - 81 = 0 := by
  rw [hesseMarginRankThree]
  linear_combination (-27 : ℝ) * cosTwoPiNinth_isRoot

theorem cosTwoPiNinth_gt_half : (1 : ℝ) / 2 < Real.cos (2 * Real.pi / 9) := by
  have hpi := Real.pi_pos
  have hcompare : Real.cos (Real.pi / 3) < Real.cos (2 * Real.pi / 9) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  rw [Real.cos_pi_div_three] at hcompare
  linarith

theorem hesseMargin_nonneg : 0 ≤ hesseMarginRankThree := by
  have hupper := Real.cos_le_one (2 * Real.pi / 9)
  rw [hesseMarginRankThree]
  linarith

theorem hesseMargin_lt_threeHalves : hesseMarginRankThree < 3 / 2 := by
  have hhalf := cosTwoPiNinth_gt_half
  rw [hesseMarginRankThree]
  linarith

/-- **The Hesse margin in a rational window**: `7/10 < h < 71/100`, the same
bracket the ledger's `hesseCubic_hasRootIn` produces — so that existential root
IS this closed form. -/
theorem hesseMargin_window :
    7 / 10 < hesseMarginRankThree ∧ hesseMarginRankThree < 71 / 100 := by
  have hroot := hesseMargin_isRoot
  have hlow := hesseMargin_nonneg
  have hhigh := hesseMargin_lt_threeHalves
  constructor
  · nlinarith [hroot, hlow, hhigh, sq_nonneg (hesseMarginRankThree - 7 / 10)]
  · nlinarith [hroot, hlow, hhigh, sq_nonneg (hesseMarginRankThree - 71 / 100)]

/-- **The Hesse cubic is positive on all of `(hesseMarginRankThree, 2]`.** The
factor `8 s^2 + 8 s h + 8 h^2 - 72 s - 72 h + 162` stays positive there. This
says the cubic has NO further root up to `2`; it does not by itself say the
bracketed root is the least of the three (that would also need "no root below
it", which nothing here proves and nothing here uses). -/
theorem hesseCubic_pos_above_margin (shift : ℝ)
    (habove : hesseMarginRankThree < shift) (hbelow : shift ≤ 2) :
    0 < 8 * shift ^ 3 - 72 * shift ^ 2 + 162 * shift - 81 := by
  obtain ⟨hmarginLow, hmarginHigh⟩ := hesseMargin_window
  have hroot := hesseMargin_isRoot
  have hfactored : 8 * shift ^ 3 - 72 * shift ^ 2 + 162 * shift - 81
      = (shift - hesseMarginRankThree)
        * (8 * shift ^ 2 + 8 * shift * hesseMarginRankThree
          + 8 * hesseMarginRankThree ^ 2 - 72 * shift
          - 72 * hesseMarginRankThree + 162) := by
    linear_combination hroot
  have hquadPos : 0 < 8 * shift ^ 2 + 8 * shift * hesseMarginRankThree
      + 8 * hesseMarginRankThree ^ 2 - 72 * shift - 72 * hesseMarginRankThree + 162 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbelow) (by linarith : (0 : ℝ) ≤ 7 - shift),
      mul_lt_mul_of_pos_right habove (by linarith : (0 : ℝ) < hesseMarginRankThree),
      sq_nonneg hesseMarginRankThree, hmarginLow, hmarginHigh]
  rw [hfactored]
  exact mul_pos (sub_pos.mpr habove) hquadPos

/-- **The ledger's bracketed root IS this closed form.** `hesseCubic_hasRootIn`
produces some root in `[7/10, 71/100]`; the cubic's slope factor is bounded below
by `71` on that interval, so the root there is unique. -/
theorem hesseCubicRoot_eq_hesseMargin (margin : ℝ)
    (hmem : margin ∈ Set.Icc (7 / 10 : ℝ) (71 / 100))
    (hroot : 8 * margin ^ 3 - 72 * margin ^ 2 + 162 * margin - 81 = 0) :
    margin = hesseMarginRankThree := by
  obtain ⟨hlow, hhigh⟩ := hmem
  obtain ⟨hmarginLow, hmarginHigh⟩ := hesseMargin_window
  have hdifference : (margin - hesseMarginRankThree)
      * (8 * (margin ^ 2 + margin * hesseMarginRankThree + hesseMarginRankThree ^ 2)
        - 72 * (margin + hesseMarginRankThree) + 162) = 0 := by
    linear_combination hroot - hesseMargin_isRoot
  have hslopePos : 0 < 8 * (margin ^ 2 + margin * hesseMarginRankThree
      + hesseMarginRankThree ^ 2) - 72 * (margin + hesseMarginRankThree) + 162 := by
    nlinarith [hlow, hhigh, hmarginLow, hmarginHigh,
      mul_nonneg (by linarith : (0 : ℝ) ≤ margin - 7 / 10)
        (by linarith : (0 : ℝ) ≤ hesseMarginRankThree - 7 / 10)]
  rcases mul_eq_zero.mp hdifference with hzero | hcontradiction
  · linarith
  · linarith

/-- **The Hesse cubic at the trine margin is exactly `14 sqrt 5 - 27`.** Every
`sqrt 5` cancels but one, since `(3 - s)^2 = 14 - 6 s` and
`(3 - s)^3 = 72 - 32 s`. -/
theorem hesseCubic_at_trineMargin :
    8 * trineMarginRankThree ^ 3 - 72 * trineMarginRankThree ^ 2
      + 162 * trineMarginRankThree - 81 = 14 * Real.sqrt 5 - 27 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [trineMarginRankThree]
  linear_combination (-8 * Real.sqrt 5) * hsq

/-- It is POSITIVE there: `14 sqrt 5 > 27` because `980 > 729`. -/
theorem hesseCubic_pos_at_trineMargin :
    0 < 8 * trineMarginRankThree ^ 3 - 72 * trineMarginRankThree ^ 2
      + 162 * trineMarginRankThree - 81 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rw [hesseCubic_at_trineMargin]
  nlinarith [hsq, hpos]

/-- **G3, settled: the Hesse SIC's margin is strictly below the trine's.**
`3 (1 - cos 2 pi / 9) < 3 - sqrt 5`, the two isolating windows separated by the
single rational `3/4`. -/
theorem hesseMargin_lt_trineMargin : hesseMarginRankThree < trineMarginRankThree := by
  have hhesse := hesseMargin_window
  have htrine := trineMargin_window
  linarith [hhesse.2, htrine.1]

/-- The radical-free form of the same comparison: `cos (2 pi / 9) > sqrt 5 / 3`. -/
theorem cosTwoPiNinth_gt_rootFive_div_three :
    Real.sqrt 5 / 3 < Real.cos (2 * Real.pi / 9) := by
  have hcompare := hesseMargin_lt_trineMargin
  rw [hesseMarginRankThree, trineMarginRankThree] at hcompare
  linarith

/-- Anything in the ledger's bracket `[7/10, 71/100]` lies below the trine
margin — rootness is not used, only the window, which already sits left of
`3/4`. In particular whatever root `hesseCubic_hasRootIn` produces is below the
trine margin. -/
theorem hesseWindowMember_lt_trineMargin (margin : ℝ)
    (hmem : margin ∈ Set.Icc (7 / 10 : ℝ) (71 / 100)) :
    margin < trineMarginRankThree := by
  have htrine := trineMargin_window
  linarith [hmem.2, htrine.1]

/-- **The rank-3 complex ledger, reordered.** The Hesse SIC is the record, the
trine is second, `alpha_2` is a rank-2 statement, the padded SIC is last. The
ledger's own `ledger_ordering` opens at the trine and so omits the record. -/
theorem rankThree_recordOrdering :
    hesseMarginRankThree < trineMarginRankThree
      ∧ trineMarginRankThree < alphaRankTwo
      ∧ alphaRankTwo < paddedMarginRankThree := by
  have halpha := alphaRankTwo_window
  have hpadded := paddedMargin_window
  exact ⟨hesseMargin_lt_trineMargin, trineMargin_lt_alphaRankTwo,
    by linarith [halpha.2, hpadded.1]⟩

/-! ## The Hesse SIC is a strictly better rank-3 witness than the trine -/

/-- **The Hesse design's value is at most its margin.** Above
`hesseMarginRankThree` NO `3`-subset is positive semidefinite at ANY shift: below
`2` the Hesse cubic is positive, and above `2` positive semidefiniteness would
descend to the shift `2`, where the cubic is `19`. -/
theorem hesse_no_triple_above_margin (shift : ℝ)
    (habove : hesseMarginRankThree < shift)
    (subset : Finset (Fin 9)) (hcard : subset.card = 3) :
    ¬ ((∑ c ∈ subset, complexAtom (hesseDesign.atom c))
        - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
  intro hpsd
  rcases le_or_gt shift 2 with hle | hgt
  · exact hesse_no_triple_above shift
      (hesseCubic_pos_above_margin shift habove hle) subset hcard hpsd
  · exact hesse_no_triple_above 2 (by norm_num) subset hcard
      (posSemidef_sub_smul_one_of_le hpsd (by linarith))

/-- **At the trine's own margin, NO triple of the Hesse SIC is positive
semidefinite.** Together with `trineMargin_isLeastAndAttained` — which shows the
trine DOES attain `3 - sqrt 5` — this is the mechanized statement that the Hesse
design's value is strictly smaller, hence that the trine is not the rank-3
extremal. -/
theorem hesse_no_triple_at_trineMargin (subset : Finset (Fin 9)) (hcard : subset.card = 3) :
    ¬ ((∑ c ∈ subset, complexAtom (hesseDesign.atom c))
        - ((trineMarginRankThree : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef :=
  hesse_no_triple_above trineMarginRankThree hesseCubic_pos_at_trineMargin subset hcard

/-- **G3, assembled.** Four kernel-checked facts: the Hesse SIC refutes complex
weighted `(9,3)`; no `3`-subset of it survives any shift strictly above
`hesseMarginRankThree`, so its value is at most that margin; that margin is
strictly below the trine's `3 - sqrt 5`; and in particular no subset survives the
trine's own margin. Since `trineMargin_isLeastAndAttained` shows the trine ATTAINS
`3 - sqrt 5`, the trine is not the rank-3 complex record — the Hesse SIC is. -/
theorem hesseBeatsTrine :
    ¬ ComplexGtzWeighted 9 3
      ∧ (∀ shift : ℝ, hesseMarginRankThree < shift →
          ∀ subset : Finset (Fin 9), subset.card = 3 →
            ¬ ((∑ c ∈ subset, complexAtom (hesseDesign.atom c))
              - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef)
      ∧ hesseMarginRankThree < trineMarginRankThree
      ∧ (∀ subset : Finset (Fin 9), subset.card = 3 →
          ¬ ((∑ c ∈ subset, complexAtom (hesseDesign.atom c))
            - ((trineMarginRankThree : ℝ) : ℂ)
              • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef) :=
  ⟨complexGtzWeighted_nine_three_fails_via_hesse, hesse_no_triple_above_margin,
    hesseMargin_lt_trineMargin, hesse_no_triple_at_trineMargin⟩

/-! ## The per-rank ledger: the two-sided statements

`alpha_k` is an infimum over designs of a maximum over subsets.  Neither end is
written with `sInf`: an UPPER bound on it is one exhibited design every subset of
which fails above a level, and a LOWER bound on it is a level every design
reaches.  Both are first-order, and both are what the theorems below deliver. -/

section LedgerDefinitions

variable {m k : ℕ}

/-- **Domination at a LEVEL.**  `S_subset - level . I` positive semidefinite says
every eigenvalue of the atom block `S_subset = Σ_{c ∈ subset} g_c g_c*` is at
least `level`; `ComplexDominates` is the case `level = 1`.  Reading the least
eigenvalue through this predicate keeps every statement inside the
positive-semidefinite API, so no spectral theorem is needed anywhere. -/
def ComplexDominatesAtLevel (design : ComplexWeightedDesign m k)
    (subset : Finset (Fin m)) (level : ℝ) : Prop :=
  ((∑ atomLabel ∈ subset, complexAtom (design.atom atomLabel)) - ((level : ℝ) : ℂ)
    • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef

theorem complexDominatesAtLevel_one (design : ComplexWeightedDesign m k)
    (subset : Finset (Fin m)) :
    ComplexDominatesAtLevel design subset 1 ↔ ComplexDominates design subset := by
  rw [ComplexDominatesAtLevel, ComplexDominates, Complex.ofReal_one, one_smul]

/-- **The design's best-subset value is at most `bound`**, spelled without a
supremum: no `k`-subset survives any level strictly above `bound`.  This is the
exact statement a determinant or diagonal certificate delivers, and it is the
Loewner reading of `max_{|subset| = k} lambda_min ≤ bound`. -/
def ComplexDesignValueAtMost (design : ComplexWeightedDesign m k) (bound : ℝ) : Prop :=
  ∀ subset : Finset (Fin m), subset.card = k →
    ∀ level : ℝ, bound < level → ¬ ComplexDominatesAtLevel design subset level

theorem complexDesignValueAtMost_mono {design : ComplexWeightedDesign m k}
    {sharpBound looseBound : ℝ} (hle : sharpBound ≤ looseBound)
    (hsharp : ComplexDesignValueAtMost design sharpBound) :
    ComplexDesignValueAtMost design looseBound :=
  fun subset hcard level hlow => hsharp subset hcard level (lt_of_le_of_lt hle hlow)

/-- A best-subset value below one refutes complex weighted GTZ at that size: the
bridge from the quantitative ledger back to the Boolean statement. -/
theorem not_complexGtzWeighted_of_designValueAtMost
    {design : ComplexWeightedDesign m k} {bound : ℝ} (hbelowOne : bound < 1)
    (hvalue : ComplexDesignValueAtMost design bound) : ¬ ComplexGtzWeighted m k := by
  intro hgtz
  obtain ⟨subset, hcard, hdominates⟩ := hgtz design
  exact hvalue subset hcard 1 hbelowOne
    ((complexDominatesAtLevel_one design subset).mpr hdominates)

end LedgerDefinitions

/-- **`alpha_rank ≤ bound`, witnessed by an EXHIBITED design.**  An upper bound on
an infimum is one design; nothing here claims a lower bound. -/
def ComplexRankConstantAtMost (rank : ℕ) (bound : ℝ) : Prop :=
  ∃ (size : ℕ) (design : ComplexWeightedDesign size rank),
    ComplexDesignValueAtMost design bound

theorem complexRankConstantAtMost_mono {rank : ℕ} {sharpBound looseBound : ℝ}
    (hle : sharpBound ≤ looseBound)
    (hsharp : ComplexRankConstantAtMost rank sharpBound) :
    ComplexRankConstantAtMost rank looseBound := by
  obtain ⟨size, design, hvalue⟩ := hsharp
  exact ⟨size, design, complexDesignValueAtMost_mono hle hvalue⟩

/-- **`alpha_rank ≥ bound`**: every design of every size reaches the level.  This
is the universally quantified half, and it is exactly what
`exists_subset_atomSum_sub_rankInverse_posSemidef` supplies at `bound = 1/rank`. -/
def ComplexRankConstantAtLeast (rank : ℕ) (bound : ℝ) : Prop :=
  ∀ size : ℕ, ComplexGtzWeightedAtLevel size rank bound

/-- **The rank-inverse lower bound, in ledger form**: `alpha_k ≥ 1/k` at every
rank, over ℂ, with no hypothesis on the design. -/
theorem complexRankConstantAtLeast_rankInverse (rank : ℕ) :
    ComplexRankConstantAtLeast rank ((rank : ℝ)⁻¹) :=
  fun size => complexGtzWeightedAtLevel_rankInverse size rank

/-! ### Rank one: `alpha_1 = 1` exactly, both ends proved -/

/-- The one-atom design in `ℂ¹`: the single unit vector at weight one.  Its only
`1`-subset has atom block the identity, so its value is exactly `1`. -/
noncomputable def unitRankOneDesign : ComplexWeightedDesign 1 1 where
  atom := fun _ _ => 1
  weight := fun _ => 1
  weight_pos := fun _ => one_pos
  weight_sum_one := by simp
  isParseval := by
    ext rowIndex colIndex
    rw [Matrix.sum_apply, Fin.sum_univ_one]
    fin_cases rowIndex
    fin_cases colIndex
    simp [complexAtom_apply]

@[simp] theorem unitRankOneDesign_atom :
    unitRankOneDesign.atom = fun _ _ => (1 : ℂ) := rfl

/-- **`alpha_1 ≤ 1`**: the one-atom design's single subset has value exactly `1`,
so nothing above `1` survives. -/
theorem unitRankOneDesign_valueAtMost : ComplexDesignValueAtMost unitRankOneDesign 1 := by
  intro subset hcard level habove hpsd
  obtain ⟨atomLabel, hsingleton⟩ := Finset.card_eq_one.mp hcard
  rw [ComplexDominatesAtLevel, hsingleton, Finset.sum_singleton] at hpsd
  refine not_posSemidef_of_diag_re_neg 0 ?_ hpsd
  have hentry : (complexAtom (unitRankOneDesign.atom atomLabel)
      - ((level : ℝ) : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 0
      = (((1 - level : ℝ)) : ℂ) := by
    simp only [unitRankOneDesign_atom, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      complexAtom_apply, Matrix.one_apply, if_true, map_one]
    push_cast
    ring
  rw [hentry, Complex.ofReal_re]
  linarith

theorem complexRankConstantAtMost_one : ComplexRankConstantAtMost 1 1 :=
  ⟨1, unitRankOneDesign, unitRankOneDesign_valueAtMost⟩

/-- **`alpha_1 ≥ 1`**: Parseval in `ℂ¹` makes `|g_c|²` a weighted average of value
one, so a single atom already dominates. -/
theorem complexRankConstantAtLeast_one : ComplexRankConstantAtLeast 1 1 :=
  fun size => (complexGtzWeightedAtLevel_one_iff size 1).mpr (complexGtzWeighted_rankOne size)

/-! ### Rank two: the `ℂ²` SIC gives `alpha_2 ≤ 2 - 2/sqrt 3` -/

@[simp] theorem sicDesign_atom : sicDesign.atom = sicAtom := rfl

/-- The SIC pair's characteristic polynomial `z² - 4z + 8/3` factors as
`(z - alpha_2)(z - (4 - alpha_2))`: the two roots are `2 ± 2/sqrt 3`. -/
theorem sicPairCharpoly_factored (level : ℝ) :
    level ^ 2 - 4 * level + 8 / 3
      = (level - alphaRankTwo) * (level - (4 - alphaRankTwo)) := by
  linear_combination alphaRankTwo_isRoot

/-- On `(alpha_2, 2]` the SIC pair's characteristic polynomial is negative: the
first factor is positive, the second at most `alpha_2 - 2 < 0`. -/
theorem sicPairCharpoly_neg_of_le {level : ℝ} (habove : alphaRankTwo < level)
    (hle : level ≤ 2) : level ^ 2 - 4 * level + 8 / 3 < 0 := by
  have hwindow := alphaRankTwo_window
  rw [sicPairCharpoly_factored]
  exact mul_neg_of_pos_of_neg (by linarith) (by linarith [hwindow.2])

/-- **No pair of the `ℂ²` SIC survives any level above `alpha_2`.**  Two regions,
as at rank three: below `2` the determinant certificate fires; above `2` the
excess is first pushed down to the level `2` by monotonicity, where the
determinant is `-4/3`. -/
theorem sicPair_not_posSemidef_above_alphaRankTwo {firstIdx secondIdx : Fin 4}
    (hne : firstIdx ≠ secondIdx) (level : ℝ) (habove : alphaRankTwo < level) :
    ¬ (complexAtom (sicAtom firstIdx) + complexAtom (sicAtom secondIdx)
        - ((level : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
  intro hpsd
  rcases le_or_gt level 2 with hle | hgt
  · refine not_posSemidef_of_det_re_neg_gen ?_ hpsd
    rw [sicPair_shifted_det hne]
    have hcast : ((level : ℝ) : ℂ) ^ 2 - 4 * ((level : ℝ) : ℂ) + 8 / 3
        = (((level ^ 2 - 4 * level + 8 / 3 : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, Complex.ofReal_re]
    exact sicPairCharpoly_neg_of_le habove hle
  · have hlower := posSemidef_sub_smul_one_of_le hpsd (by linarith : (2 : ℝ) ≤ level)
    refine not_posSemidef_of_det_re_neg_gen ?_ hlower
    rw [sicPair_shifted_det hne]
    have hcast : (((2 : ℝ) : ℂ)) ^ 2 - 4 * (((2 : ℝ)) : ℂ) + 8 / 3
        = ((-(4 / 3 : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.ofReal_re]
    norm_num

/-- **`alpha_2 ≤ 2 - 2/sqrt 3`**, witnessed by the `ℂ²` SIC at `m = 4`: uniform
weight `1/4`, every leverage exactly `2`, cap `κ = 1`.  Sharpness at rank two is
CITED, not proved here (Nesterenko, arXiv:2604.24087). -/
theorem sicDesign_valueAtMost : ComplexDesignValueAtMost sicDesign alphaRankTwo := by
  intro subset hcard level habove hpsd
  obtain ⟨firstIdx, secondIdx, hne, hsubset⟩ := Finset.card_eq_two.mp hcard
  rw [ComplexDominatesAtLevel, hsubset, Finset.sum_insert (by simp [hne]),
    Finset.sum_singleton, sicDesign_atom] at hpsd
  exact sicPair_not_posSemidef_above_alphaRankTwo hne level habove hpsd

theorem complexRankConstantAtMost_two_sic : ComplexRankConstantAtMost 2 alphaRankTwo :=
  ⟨4, sicDesign, sicDesign_valueAtMost⟩

/-! ### Rank three: the Hesse SIC is the record, the trine is second -/

theorem trineDesign_valueAtMost :
    ComplexDesignValueAtMost trineDesign trineMarginRankThree :=
  fun subset hcard level habove => trine_no_triple_above_margin level habove subset hcard

theorem hesseDesign_valueAtMost :
    ComplexDesignValueAtMost hesseDesign hesseMarginRankThree :=
  fun subset hcard level habove => hesse_no_triple_above_margin level habove subset hcard

/-- **THE RANK-THREE UPPER BOUND**: `alpha_3 ≤ 3(1 - cos 2 pi / 9) ≈ 0.7018666706`,
witnessed by the Hesse SIC at `m = 9` — nine equiangular lines in `ℂ³`, uniform
weight `1/9`, every leverage exactly `3` (cap `κ = 1`, no spike and no limit
argument), all Gram data in `ℤ[ω]`. -/
theorem complexRankConstantAtMost_three_hesse :
    ComplexRankConstantAtMost 3 hesseMarginRankThree :=
  ⟨9, hesseDesign, hesseDesign_valueAtMost⟩

/-- The trine's `3 - sqrt 5` is now a COROLLARY of the Hesse bound, by
monotonicity: it is the sharpest witness at size `m = 6` and the one whose exact
value is pinned on both sides (`trineMargin_isGreatest`), but it is no longer the
record. -/
theorem complexRankConstantAtMost_three_trine :
    ComplexRankConstantAtMost 3 trineMarginRankThree :=
  complexRankConstantAtMost_mono (le_of_lt hesseMargin_lt_trineMargin)
    complexRankConstantAtMost_three_hesse

/-! ### The proved windows, per rank -/

/-- **Rank one is CLOSED**: `alpha_1 = 1`, both ends kernel-checked here. -/
theorem complexRankOne_closed :
    ComplexRankConstantAtLeast 1 1 ∧ ComplexRankConstantAtMost 1 1 :=
  ⟨complexRankConstantAtLeast_one, complexRankConstantAtMost_one⟩

/-- **The proved rank-two window**: `1/2 ≤ alpha_2 ≤ 2 - 2/sqrt 3`, a factor
`1.6906`.  The upper end is CITED to be exact (Nesterenko, arXiv:2604.24087);
that citation is not mechanized, so the proved statement is the window. -/
theorem complexRankTwo_provedWindow :
    ComplexRankConstantAtLeast 2 ((2 : ℝ)⁻¹)
      ∧ ComplexRankConstantAtMost 2 alphaRankTwo
      ∧ (2 : ℝ)⁻¹ < alphaRankTwo := by
  refine ⟨?_, complexRankConstantAtMost_two_sic, by linarith [alphaRankTwo_window.1]⟩
  have hcast : ((2 : ℕ) : ℝ)⁻¹ = ((2 : ℝ))⁻¹ := by norm_num
  rw [← hcast]
  exact complexRankConstantAtLeast_rankInverse 2

/-- **The proved rank-three window**: `1/3 ≤ alpha_3 ≤ 3(1 - cos 2 pi / 9)`, a
factor `2.1056`.  Both ends are kernel-checked here — the lower by maximal
volume, the upper by the Hesse SIC.  Nothing is known to close the gap. -/
theorem complexRankThree_provedWindow :
    ComplexRankConstantAtLeast 3 ((3 : ℝ)⁻¹)
      ∧ ComplexRankConstantAtMost 3 hesseMarginRankThree
      ∧ (3 : ℝ)⁻¹ < hesseMarginRankThree := by
  refine ⟨?_, complexRankConstantAtMost_three_hesse,
    by linarith [hesseMargin_window.1]⟩
  have hcast : ((3 : ℕ) : ℝ)⁻¹ = ((3 : ℝ))⁻¹ := by norm_num
  rw [← hcast]
  exact complexRankConstantAtLeast_rankInverse 3

/-- **THE LEDGER, ASSEMBLED.**  Everything this file proves about `alpha_k` over
ℂ, in one statement, with nothing measured or cited smuggled in:

* rank `k`, every `k`: `alpha_k ≥ 1/k` (maximal volume, weight-free and
  independent of the number of atoms);
* rank 1: `alpha_1 = 1`, both ends — the rank-inverse bound is SHARP here;
* rank 2: `1/2 ≤ alpha_2 ≤ 2 - 2/sqrt 3`, the upper end witnessed by the `ℂ²`
  SIC at `m = 4`;
* rank 3: `1/3 ≤ alpha_3 ≤ 3(1 - cos 2 pi / 9)`, the upper end witnessed by the
  Hesse SIC at `m = 9`, and the trine's `3 - sqrt 5` strictly above it;
* the trine's own value is pinned exactly, in Loewner form, at `3 - sqrt 5`.

Ranks `≥ 4` have only the `1/k` lower bound here: no rank-4 or rank-5 design is
mechanized anywhere in this repository. -/
theorem complexPerRankLedger :
    (∀ rank : ℕ, ComplexRankConstantAtLeast rank ((rank : ℝ)⁻¹))
      ∧ (ComplexRankConstantAtLeast 1 1 ∧ ComplexRankConstantAtMost 1 1)
      ∧ ComplexRankConstantAtMost 2 alphaRankTwo
      ∧ ComplexRankConstantAtMost 3 hesseMarginRankThree
      ∧ hesseMarginRankThree < trineMarginRankThree
      ∧ IsGreatest trineDominatedShifts trineMarginRankThree :=
  ⟨complexRankConstantAtLeast_rankInverse, complexRankOne_closed,
    complexRankConstantAtMost_two_sic, complexRankConstantAtMost_three_hesse,
    hesseMargin_lt_trineMargin, trineMargin_isGreatest⟩

/-! ## SCOPE NOTE: what is in the kernel here, and what is not

**PROVED here, kernel-checked.**  `alpha_k ≥ 1/k` at every rank over ℂ, by
maximal volume — Cramer's rule plus Parseval, field-blind, weight-free and
independent of `m`.  `alpha_1 = 1` exactly.  `alpha_2 ≤ 2 - 2/sqrt 3` via the
`ℂ²` SIC.  `alpha_3 ≤ 3(1 - cos 2 pi / 9)` via the Hesse SIC, with the Hesse
design built from scratch over `ℤ[ω]` (Parseval, leverage `3`, equiangularity
`9/4`, the phase cap `Re T ≤ 27/16`).  The shared-axis trine's value pinned
exactly at `3 - sqrt 5` in Loewner form, with the binding triple's least
eigenvalue proved in the ordinary sense via an explicit eigenvector.  The strict
comparison `Hesse < trine`.  The refutations at level one at `(4,2)`, `(6,3)` and
`(9,3)`.

**NOT proved here, and NOT claimed.**

* That `1/k` is anywhere near `alpha_k` for `k ≥ 2`.  It is not: at `k = 2` the
  CITED sharp constant is `2 - 2/sqrt 3 ≈ 0.845`, so `1/2` is `40.8%` low.  `1/k`
  is sharp only at `k = 1`.  Adversarial search does measure the MAXIMAL-VOLUME
  SUBSET's least eigenvalue descending to `1.0017/k` at `k = 2` — so the analysis
  has no slack left at that SELECTION — but that is MEASURED, at leverage `7e4`
  and Parseval residual `3e-14`, and a better constant needs a better selection,
  not a better estimate.  The corresponding `k = 3` and `k = 4` figures were not
  reproduced under a `1e-12` Parseval gate and are not recorded.
* A sharper `m`-aware lower bound.  The classical maximal-volume bound in the
  UNIFORM-weight normalisation reads `m / (k(m-k)+1)`, which exceeds `1/k` for
  every `k ≥ 2` and every `m` (it is `4/5` at `(4,2)` and `3/5` at `(6,3)`); it
  is not mechanized here, and the real-side assembly it would reuse
  (`Gtz/Reduction/MaximalVolume.lean`) is itself unfinished.
* That `3(1 - cos 2 pi / 9)` IS `alpha_3` rather than an upper bound.  MEASURED
  only, and the supporting search does not even find the Hesse basin from random
  starts — it sticks at the trine.
* That the Hesse design ATTAINS its margin.  Only `≤` is proved: no triple
  survives above it.  Attainment is EXACT ELSEWHERE (all `72` non-degenerate
  triples share `lambda_min = 3(1 - cos 2 pi / 9)`, the other `12` are
  rank-deficient), not mechanized.
* `sigma_min(G_C) ^ 2 = lambda_min(S_C)`.  Unused and unmechanized; the whole
  file is stated in Loewner form, which is what `ComplexDominates` needs.
* Anything at rank `≥ 4`.  `Gtz/Complex/SharpConstantLedger.lean` records
  measured rank-4 and rank-5 constants; none of them is used here, and its
  `measuredRankFourUncapped = 0.701866670643` coincides with the rank-3 Hesse
  constant to all twelve recorded digits under a leverage cap that cannot produce
  it, so it should be re-derived or withdrawn before anyone builds on it.
* Restricted invertibility.  `ComplexUniformLevel` names a rank-uniform level
  statement so the implication can be recorded; it is neither Bourgain–Tzafriri
  nor Spielman–Srivastava, which select a subset strictly smaller than the rank
  and whose bounds vanish identically at `k = rank`.  Nothing here assumes it,
  and `not_complexUniformLevel_one` shows the level `1` version is false. -/

end Gtz

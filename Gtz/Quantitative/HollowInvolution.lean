/-
# The hollow involution of the equal-share stratum (step S1 of the U6 layer)

**The object.** Six unit vectors `u_1..u_6` in `R^3`, pairwise, with
`sum_c u_c u_c^T = 2 I_3`.  In this repository's vocabulary that is a
`WeightedDesign 6 3` with every weight `1/6` and every leverage `3` — the
predicate `Gtz.IsEqualShare` below, stated rank-generically as
`weight = 1/m` and `leverage = k` so that the same hypothesis pair the shipped
`Gtz.sum_normalizedPairing_sq_uniform_six` already uses is exactly its two
projections.

**The involution.**  Write `Gamma` for the direction Gram
(`Gtz.directionGramMatrix`) and `M = Gamma - 1` (`Gtz.correlationInvolution`).
The shipped idempotency identity `Gamma diag(s) Gamma = Gamma` at a constant
share `s = k/m` reads `Gamma^2 = (m/k) Gamma`; when `m = 2k` that is
`Gamma^2 = 2 Gamma`, hence `M^2 = 1`.  Together with the vanishing diagonal
`gamma_cc = 1` and the symmetry of `Gamma` this makes `M` a **hollow symmetric
involution**, the abstract object `Gtz.IsHollowInvolution`.

Everything the pen's step S1 asks for is a reading of `M^2 = 1`:

* **row law** — `sum_{d /= c} gamma_cd^2 = 1`, the diagonal entry of `M^2`;
* **vanishing supply** — `sum_{d /= a,b} gamma_ad gamma_db = 0`, the off-diagonal
  entry of `M^2` after the two hollow terms are dropped;
* **trace zero** — hollowness, whence the split spectrum: `(1 + M)/2` and
  `(1 - M)/2` are complementary orthogonal projections of trace `size/2`, so at
  size six the spectrum is `{+1,+1,+1,-1,-1,-1}`;
* **the NORM CAP** — `1 - M` and `1 + M` are both positive semidefinite, because
  `(1 - M)^2 = 2 (1 - M)` makes `1 - M` a half-square, and
  `Matrix.PosSemidef.submatrix` restricts both facts to every principal
  submatrix with no injectivity hypothesis at all.  This is the single most
  load-bearing fact of the U6 layer and it is drawn here WITHOUT any spectral
  theory, honouring the repository's standing "no spectra anywhere" rule:
  the operator-norm bound `||M[C]|| <= 1` is delivered as the pair of Loewner
  facts `1 - M[C] ⪰ 0` and `1 + M[C] ⪰ 0`, which is exactly what its consumers
  (the criterion, the cap `sigma + 2|P| <= 1`, and cases 3 and 4 of the squeeze)
  actually use.  Mathlib has no spectral norm on `Matrix` and no compression
  lemma for one; none is needed.

**A REFUTATION.**  The pen brief lists "entries in `(-1,1)`" among the OUTPUTS of
S1, i.e. among the consequences of `M^2 = 1`, `diag M = 0` and symmetry.  It is
not one, and it is not a property of the stratum the brief itself declares
equivalent to its object.  Two kernel-checked counterexamples:

* abstractly, `!![0,1;1,0]` is a hollow symmetric involution with an entry of
  modulus exactly one (`Gtz.exists_isHollowInvolution_abs_apply_eq_one`), so the
  open bound does not follow from the S1 data;
* concretely, the octahedron `{±e_1, ±e_2, ±e_3}` at weight `1/6` IS a
  `WeightedDesign 6 3` with every weight `1/6` and every leverage `3` — exactly
  the brief's own "i.e." reading of the stratum — and it has `gamma = -1` on
  three antipodal pairs
  (`Gtz.not_forall_abs_directionGram_lt_one_of_isEqualShare`).

The open bound IS recoverable, but only from the brief's separate "pairwise
non-parallel" hypothesis, which the stated equivalence to the weight/leverage
form silently drops.  What holds unconditionally is the CLOSED bound
`|gamma| <= 1` plus the sharp boundary description
`Gtz.IsHollowInvolution.sq_apply_eq_one_iff`: an entry has modulus one exactly
when the whole rest of its row vanishes — transported to the design as
`Gtz.directionGram_eq_zero_of_sq_directionGram_eq_one`, a parallel pair forces
its atom orthogonal to every other atom.  And the excluded points are not
obstacles: the octahedron dominates through its orthogonal triple
(`Gtz.dominates_octahedronDesign`), so adding the hypothesis to U6 would delete a
point of the stratum at which the conclusion holds anyway.  (That EVERY
parallel-pair point dominates is not proved here.)

**The dictionary.**  For a triple `C` of distinct atoms of the stratum, the
three statements

    Dominates D C     <->     M[C] + (2/3) 1 ⪰ 0     <->     lambda_min(Gamma[C]) >= 1/3

are proved equivalent, routed through the shipped
`Gtz.dominates_triple_iff_posSemidef_tripleGapMatrix` exactly as the workflow-1
correction demands — the congruence is never asserted about `subsetSum`, which
is the FRAME sum and for which it is refuted at `tetraDesign`.  The bridge is
the entrywise identity `tripleGapMatrix = 3 (M[C] + (2/3) 1)`, which needs no
injectivity because `Gtz.hollowMatrixThree` carries its zeros explicitly.  A
frame-side dictionary `Dominates D C <-> sum_{c in C} u_c u_c^T ⪰ (1/k) 1` is
proved for an ARBITRARY subset at an arbitrary uniform-leverage stratum, so the
`AB`-versus-`BA` transfer the mirror law wants is available as a corollary of
two equivalences rather than as a separate spectral argument.

**The coordinate trap, made a theorem.**  This repository's per-triple
coordinate is `Gtz.normalizedPairing` (`rho`), not the pen's direction cosine
(`gamma`).  At the equal-share `(6,3)` stratum they differ by a factor:
`rho = (3/2) gamma` (`Gtz.normalizedPairing_eq_three_halves_mul_directionGram`),
and consequently
`correlationMatrixThree(rho) = (3/2) (hollowMatrixThree(gamma) + (2/3) 1)`.
Reading a shipped `rho`-threshold as a `gamma`-threshold silently changes every
constant; the identity above is the only sanctioned interface between the two
layers.

**Abstract and concrete, both directions.**  `Gtz.tightFrameDesign` builds a
design of the stratum out of a unit-row tight frame, so the abstract data is
inhabited by design data and not merely implied by it; `Gtz.icosaDesign` and the
octahedron are exhibited as points of the stratum.  What is deliberately NOT
claimed is that every abstract hollow involution arises this way: that needs a
rank-`k` Gram factorization of a positive semidefinite matrix, which this file
does not build.

**Hypothesis honesty.**  The stratum predicate carries BOTH `weight = 1/m` and
`leverage = k`.  The share condition alone is strictly weaker — it constrains
only the product — and `Gtz.Dominates` is not invariant under the atom rescaling
that fixes the shares (see the docstring of `Gtz.directionDesign`), so the
dictionary genuinely needs the leverage normalisation and not merely the share.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Design.FrameConservation
import Gtz.Design.RhoNormalForm
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Quantitative.GoodTripleGraph
import Gtz.Quantitative.RealnessEngine
import Gtz.Reduction.ExchangeInvariant
import Gtz.Reduction.Reductions

namespace Gtz

open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {size selSize m k : ℕ}

/-! ## S1(a) The abstract object: a hollow symmetric involution

The squeeze consumes this form; the design layer below produces it. -/

/-- **A hollow symmetric involution**: `M^T = M`, `M M = 1`, `M_ii = 0`.  The
abstract shadow of the equal-share stratum's correlation matrix, and the object
every step of the pen's S1 is really about. -/
structure IsHollowInvolution (invol : Matrix (Fin size) (Fin size) ℝ) : Prop where
  /-- The matrix is symmetric. -/
  symmetric : involᵀ = invol
  /-- The matrix squares to the identity. -/
  square_eq_one : invol * invol = 1
  /-- The diagonal vanishes. -/
  diagonal_eq_zero : ∀ index, invol index index = 0

namespace IsHollowInvolution

variable {invol : Matrix (Fin size) (Fin size) ℝ}

/-- Entries commute across the diagonal. -/
theorem apply_comm (hinvol : IsHollowInvolution invol) (rowIndex colIndex : Fin size) :
    invol colIndex rowIndex = invol rowIndex colIndex :=
  congrFun (congrFun hinvol.symmetric rowIndex) colIndex

/-- A real symmetric matrix is Hermitian. -/
theorem isHermitian (hinvol : IsHollowInvolution invol) : invol.IsHermitian := by
  show involᴴ = invol
  ext rowIndex colIndex
  rw [Matrix.conjTranspose_apply, star_trivial]
  exact hinvol.apply_comm rowIndex colIndex

/-- **Trace zero**, immediately from hollowness.  With `M M = 1` this is what
splits the spectrum evenly between `+1` and `-1`. -/
theorem trace_eq_zero (hinvol : IsHollowInvolution invol) : Matrix.trace invol = 0 := by
  simp only [Matrix.trace, Matrix.diag_apply, hinvol.diagonal_eq_zero, Finset.sum_const_zero]

/-- The negative of a hollow involution is a hollow involution. -/
theorem neg (hinvol : IsHollowInvolution invol) : IsHollowInvolution (-invol) where
  symmetric := by rw [Matrix.transpose_neg, hinvol.symmetric]
  square_eq_one := by rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, hinvol.square_eq_one]
  diagonal_eq_zero := fun index => by
    rw [Matrix.neg_apply, hinvol.diagonal_eq_zero, neg_zero]

/-! ### The row law -/

/-- **THE ROW LAW.**  Each row of a symmetric involution is a unit vector:
`sum_d M_cd^2 = 1`.  This is the diagonal entry of `M M = 1`. -/
theorem sum_sq_row (hinvol : IsHollowInvolution invol) (rowIndex : Fin size) :
    ∑ colIndex, invol rowIndex colIndex ^ 2 = 1 := by
  have hentry := congrFun (congrFun hinvol.square_eq_one rowIndex) rowIndex
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hentry
  rw [← hentry]
  refine Finset.sum_congr rfl fun colIndex _ => ?_
  rw [pow_two, hinvol.apply_comm rowIndex colIndex]

/-- **THE ROW LAW, off the diagonal.**  Since the diagonal vanishes, the whole
unit budget sits off it: `sum_{d /= c} M_cd^2 = 1`.  At the equal-share `(6,3)`
stratum this is the pen's `sum_{d /= c} gamma_cd^2 = 1` on the nose. -/
theorem sum_sq_row_erase (hinvol : IsHollowInvolution invol) (rowIndex : Fin size) :
    ∑ colIndex ∈ Finset.univ.erase rowIndex, invol rowIndex colIndex ^ 2 = 1 := by
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun colIndex => invol rowIndex colIndex ^ 2) (Finset.mem_univ rowIndex)
  rw [hinvol.diagonal_eq_zero rowIndex] at hsplit
  rw [hinvol.sum_sq_row rowIndex] at hsplit
  linarith [hsplit]

/-- Every entry has square at most one — the CLOSED bound, which is the true
statement.  The pen's open bound is refuted below. -/
theorem sq_apply_le_one (hinvol : IsHollowInvolution invol) (rowIndex colIndex : Fin size) :
    invol rowIndex colIndex ^ 2 ≤ 1 := by
  rw [← hinvol.sum_sq_row rowIndex]
  exact Finset.single_le_sum (f := fun otherIndex => invol rowIndex otherIndex ^ 2)
    (fun otherIndex _ => sq_nonneg _) (Finset.mem_univ colIndex)

/-- Every entry has modulus at most one. -/
theorem abs_apply_le_one (hinvol : IsHollowInvolution invol) (rowIndex colIndex : Fin size) :
    |invol rowIndex colIndex| ≤ 1 := by
  have hsq := hinvol.sq_apply_le_one rowIndex colIndex
  nlinarith [sq_abs (invol rowIndex colIndex), abs_nonneg (invol rowIndex colIndex)]

/-- **The boundary of the entry bound, described exactly.**  An off-diagonal
entry has modulus one precisely when the rest of its row vanishes — geometrically,
when the two directions are parallel and carry the whole row budget between them.
This is the sharp replacement for the pen's (false) claim that entries are
strictly inside `(-1,1)`. -/
theorem sq_apply_eq_one_iff (hinvol : IsHollowInvolution invol) {rowIndex colIndex : Fin size}
    (hdistinct : rowIndex ≠ colIndex) :
    invol rowIndex colIndex ^ 2 = 1
      ↔ ∀ otherIndex, otherIndex ≠ rowIndex → otherIndex ≠ colIndex →
          invol rowIndex otherIndex = 0 := by
  have hrest : ∑ otherIndex ∈ (Finset.univ.erase rowIndex).erase colIndex,
      invol rowIndex otherIndex ^ 2
      = 1 - invol rowIndex colIndex ^ 2 := by
    have hmember : colIndex ∈ Finset.univ.erase rowIndex :=
      Finset.mem_erase.mpr ⟨(Ne.symm hdistinct), Finset.mem_univ colIndex⟩
    have hsplit := Finset.sum_erase_add (Finset.univ.erase rowIndex)
      (fun otherIndex => invol rowIndex otherIndex ^ 2) hmember
    rw [hinvol.sum_sq_row_erase rowIndex] at hsplit
    linarith [hsplit]
  constructor
  · intro hboundary otherIndex hneRow hneCol
    have hvanishes : ∑ target ∈ (Finset.univ.erase rowIndex).erase colIndex,
        invol rowIndex target ^ 2 = 0 := by rw [hrest, hboundary]; ring
    have hmember : otherIndex ∈ (Finset.univ.erase rowIndex).erase colIndex :=
      Finset.mem_erase.mpr ⟨hneCol, Finset.mem_erase.mpr ⟨hneRow, Finset.mem_univ otherIndex⟩⟩
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun target _ => sq_nonneg (invol rowIndex target))).mp hvanishes otherIndex hmember
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hterm
  · intro hquiet
    have hvanishes : ∑ target ∈ (Finset.univ.erase rowIndex).erase colIndex,
        invol rowIndex target ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun target hmember => ?_
      rw [hquiet target (Finset.mem_erase.mp (Finset.mem_erase.mp hmember).2).1
        (Finset.mem_erase.mp hmember).1]
      ring
    rw [hvanishes] at hrest
    linarith [hrest]

/-! ### The vanishing supply chain -/

/-- **THE VANISHING SUPPLY CHAIN.**  For distinct `a, b` the two-step
correlations through every third index cancel exactly:
`sum_{d /= a,b} M_ad M_db = 0`.  This is the off-diagonal entry of `M M = 1`
with the two hollow terms `d = a` and `d = b` removed — both vanish because the
diagonal does, so nothing is lost by removing them. -/
theorem sum_sdiff_pair_mul (hinvol : IsHollowInvolution invol) {firstIndex secondIndex : Fin size}
    (hdistinct : firstIndex ≠ secondIndex) :
    ∑ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin size)),
        invol firstIndex otherIndex * invol otherIndex secondIndex = 0 := by
  have hentry := congrFun (congrFun hinvol.square_eq_one firstIndex) secondIndex
  rw [Matrix.mul_apply, Matrix.one_apply_ne hdistinct] at hentry
  have hpair : ∑ otherIndex ∈ ({firstIndex, secondIndex} : Finset (Fin size)),
      invol firstIndex otherIndex * invol otherIndex secondIndex = 0 := by
    rw [Finset.sum_pair hdistinct, hinvol.diagonal_eq_zero firstIndex,
      hinvol.diagonal_eq_zero secondIndex, zero_mul, mul_zero, add_zero]
  have hsplit := Finset.sum_sdiff
    (f := fun otherIndex => invol firstIndex otherIndex * invol otherIndex secondIndex)
    (Finset.subset_univ ({firstIndex, secondIndex} : Finset (Fin size)))
  rw [hpair, hentry] at hsplit
  linarith [hsplit]

/-! ### The norm cap

The pen calls this "every principal submatrix has operator norm at most one".
Mathlib has no spectral norm on `Matrix`, and this development has none either;
the honest and strictly more usable form is the pair of Loewner facts below. -/

/-- **The Loewner sandwich, upper half**: `1 - M ⪰ 0`.  Because
`(1 - M)^2 = 2 (1 - M)`, the matrix `1 - M` is half of its own square, hence
positive semidefinite — no eigenvalue, no norm, no Courant-Fischer. -/
theorem posSemidef_one_sub (hinvol : IsHollowInvolution invol) :
    ((1 : Matrix (Fin size) (Fin size) ℝ) - invol).PosSemidef := by
  have hconj : ((1 : Matrix (Fin size) (Fin size) ℝ) - invol)ᴴ = 1 - invol := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hinvol.isHermitian]
  have hhalf : (1 : Matrix (Fin size) (Fin size) ℝ) - invol
      = ((2 : ℝ)⁻¹) • (((1 : Matrix (Fin size) (Fin size) ℝ) - invol)ᴴ
          * ((1 : Matrix (Fin size) (Fin size) ℝ) - invol)) := by
    rw [hconj, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hinvol.square_eq_one]
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    split_ifs <;> ring
  rw [hhalf]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).smul (by norm_num)

/-- **The Loewner sandwich, lower half**: `1 + M ⪰ 0`, the upper half applied to
`-M`. -/
theorem posSemidef_one_add (hinvol : IsHollowInvolution invol) :
    ((1 : Matrix (Fin size) (Fin size) ℝ) + invol).PosSemidef := by
  have hshape : (1 : Matrix (Fin size) (Fin size) ℝ) + invol = 1 - -invol := by
    rw [sub_neg_eq_add]
  rw [hshape]
  exact hinvol.neg.posSemidef_one_sub

/-- **THE NORM CAP, upper half.**  Every principal submatrix `N = M[C]` satisfies
`1 - N ⪰ 0`.  `Matrix.PosSemidef.submatrix` needs no injectivity, but identifying
the compressed identity as the identity does, which is why `pick` must be
injective. -/
theorem posSemidef_one_sub_submatrix (hinvol : IsHollowInvolution invol)
    (pick : Fin selSize → Fin size) (hpick : Function.Injective pick) :
    ((1 : Matrix (Fin selSize) (Fin selSize) ℝ) - invol.submatrix pick pick).PosSemidef := by
  have hsub := hinvol.posSemidef_one_sub.submatrix pick
  have hone : ((1 : Matrix (Fin size) (Fin size) ℝ) - invol).submatrix pick pick
      = 1 - invol.submatrix pick pick := by
    rw [show ((1 : Matrix (Fin size) (Fin size) ℝ) - invol).submatrix pick pick
        = (1 : Matrix (Fin size) (Fin size) ℝ).submatrix pick pick
          - invol.submatrix pick pick from rfl, Matrix.submatrix_one pick hpick]
  rwa [hone] at hsub

/-- **THE NORM CAP, lower half.**  Every principal submatrix satisfies
`1 + N ⪰ 0`.  Together with the upper half this is `-1 ⪯ M[C] ⪯ 1`. -/
theorem posSemidef_one_add_submatrix (hinvol : IsHollowInvolution invol)
    (pick : Fin selSize → Fin size) (hpick : Function.Injective pick) :
    ((1 : Matrix (Fin selSize) (Fin selSize) ℝ) + invol.submatrix pick pick).PosSemidef := by
  have hneg := hinvol.neg.posSemidef_one_sub_submatrix pick hpick
  have hshape : (-invol).submatrix pick pick = -invol.submatrix pick pick := rfl
  rwa [hshape, sub_neg_eq_add] at hneg

/-- A compression of a hollow symmetric matrix along an injective selector is
hollow and symmetric.  It is NOT an involution: the norm cap is what survives. -/
theorem submatrix_transpose (hinvol : IsHollowInvolution invol)
    (pick : Fin selSize → Fin size) :
    (invol.submatrix pick pick)ᵀ = invol.submatrix pick pick := by
  ext rowIndex colIndex
  exact hinvol.apply_comm (pick rowIndex) (pick colIndex)

theorem submatrix_diagonal_eq_zero (hinvol : IsHollowInvolution invol)
    (pick : Fin selSize → Fin size) (index : Fin selSize) :
    invol.submatrix pick pick index index = 0 :=
  hinvol.diagonal_eq_zero (pick index)

/-! ### The split spectrum

Two readings.  De-spectralized: the halves `(1 ± M)/2` are complementary
orthogonal projections whose traces are `size/2` each.  Spectral:
`IsHollowInvolution.card_eigenvalues_eq_one` proves outright that exactly half the
eigenvalues are `+1`, so at size six `spec M = {+1,+1,+1,-1,-1,-1}` — that is the
rigorous form of the pen's S1 conclusion, and it does NOT go through
"rank of an idempotent is its trace", which this file never uses. -/

/-- The positive spectral projection `(1 + M)/2`. -/
noncomputable def positivePart (invol : Matrix (Fin size) (Fin size) ℝ) :
    Matrix (Fin size) (Fin size) ℝ :=
  ((2 : ℝ)⁻¹) • ((1 : Matrix (Fin size) (Fin size) ℝ) + invol)

/-- The negative spectral projection `(1 - M)/2`. -/
noncomputable def negativePart (invol : Matrix (Fin size) (Fin size) ℝ) :
    Matrix (Fin size) (Fin size) ℝ :=
  ((2 : ℝ)⁻¹) • ((1 : Matrix (Fin size) (Fin size) ℝ) - invol)

/-- `(1 + M)/2` is idempotent. -/
theorem isIdempotentElem_positivePart (hinvol : IsHollowInvolution invol) :
    IsIdempotentElem (positivePart invol) := by
  show positivePart invol * positivePart invol = positivePart invol
  rw [positivePart, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hinvol.square_eq_one,
    smul_smul]
  ext rowIndex colIndex
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> ring

/-- `(1 - M)/2` is idempotent. -/
theorem isIdempotentElem_negativePart (hinvol : IsHollowInvolution invol) :
    IsIdempotentElem (negativePart invol) := by
  have hshape : negativePart invol = positivePart (-invol) := by
    rw [negativePart, positivePart, sub_eq_add_neg]
  rw [hshape]
  exact hinvol.neg.isIdempotentElem_positivePart

/-- The two projections are complementary. -/
theorem positivePart_add_negativePart (invol : Matrix (Fin size) (Fin size) ℝ) :
    positivePart invol + negativePart invol = 1 := by
  rw [positivePart, negativePart, ← smul_add]
  ext rowIndex colIndex
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- The two projections annihilate one another — the spectral splitting. -/
theorem positivePart_mul_negativePart (hinvol : IsHollowInvolution invol) :
    positivePart invol * negativePart invol = 0 := by
  rw [positivePart, negativePart, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    hinvol.square_eq_one, smul_smul]
  ext rowIndex colIndex
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply,
    smul_eq_mul]
  ring

/-- **The split is even**: `trace((1 + M)/2) = size/2`.  The de-spectralized form
of "half the eigenvalues are `+1`"; the counted form is
`IsHollowInvolution.card_eigenvalues_eq_one`. -/
theorem trace_positivePart (hinvol : IsHollowInvolution invol) :
    Matrix.trace (positivePart invol) = (size : ℝ) / 2 := by
  rw [positivePart, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one,
    hinvol.trace_eq_zero, add_zero, smul_eq_mul, Fintype.card_fin]
  ring

theorem trace_negativePart (hinvol : IsHollowInvolution invol) :
    Matrix.trace (negativePart invol) = (size : ℝ) / 2 := by
  rw [negativePart, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one,
    hinvol.trace_eq_zero, sub_zero, smul_eq_mul, Fintype.card_fin]
  ring

/-- **Every eigenvalue is `±1`.**  The spectral reading of `M M = 1`, obtained by
applying the matrix twice to an eigenvector. -/
theorem sq_eigenvalues_eq_one (hinvol : IsHollowInvolution invol) (index : Fin size) :
    hinvol.isHermitian.eigenvalues index ^ 2 = 1 := by
  classical
  set eigenvector : Fin size → ℝ := ⇑(hinvol.isHermitian.eigenvectorBasis index)
    with heigenvector
  have hnonzero : eigenvector ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 <| hinvol.isHermitian.eigenvectorBasis.orthonormal.ne_zero index
  have hstep : invol *ᵥ eigenvector = hinvol.isHermitian.eigenvalues index • eigenvector :=
    hinvol.isHermitian.mulVec_eigenvectorBasis index
  have htwice : eigenvector = (hinvol.isHermitian.eigenvalues index ^ 2) • eigenvector := by
    calc eigenvector = (1 : Matrix (Fin size) (Fin size) ℝ) *ᵥ eigenvector := by
          rw [Matrix.one_mulVec]
      _ = (invol * invol) *ᵥ eigenvector := by rw [hinvol.square_eq_one]
      _ = invol *ᵥ (invol *ᵥ eigenvector) := by rw [Matrix.mulVec_mulVec]
      _ = (hinvol.isHermitian.eigenvalues index ^ 2) • eigenvector := by
          rw [hstep, Matrix.mulVec_smul, hstep, smul_smul, ← pow_two]
  by_contra hcontra
  apply hnonzero
  have hzero : (1 - hinvol.isHermitian.eigenvalues index ^ 2) • eigenvector = 0 := by
    rw [sub_smul, one_smul, ← htwice, sub_self]
  rcases smul_eq_zero.mp hzero with hscalar | hvector
  · exact absurd (by linarith [sub_eq_zero.mp hscalar] :
      hinvol.isHermitian.eigenvalues index ^ 2 = 1) hcontra
  · exact hvector

/-- Each eigenvalue is literally `1` or `-1`. -/
theorem eigenvalues_eq_one_or_neg_one (hinvol : IsHollowInvolution invol) (index : Fin size) :
    hinvol.isHermitian.eigenvalues index = 1 ∨ hinvol.isHermitian.eigenvalues index = -1 := by
  have hsq := hinvol.sq_eigenvalues_eq_one index
  rcases mul_eq_zero.mp (by linear_combination hsq :
      (hinvol.isHermitian.eigenvalues index - 1) * (hinvol.isHermitian.eigenvalues index + 1)
        = 0) with hleft | hright
  · exact Or.inl (by linarith [sub_eq_zero.mp hleft])
  · exact Or.inr (by linarith [eq_neg_of_add_eq_zero_left hright])

open scoped Classical in
/-- **THE SPLIT SPECTRUM, counted.**  Exactly half the eigenvalues are `+1`.  At
size six that is `spec M = {+1,+1,+1,-1,-1,-1}`, the pen's S1 conclusion. -/
theorem card_eigenvalues_eq_one (hinvol : IsHollowInvolution invol) :
    (Finset.univ.filter fun index => hinvol.isHermitian.eigenvalues index = 1).card * 2 = size := by
  set positiveSet : Finset (Fin size) :=
    Finset.univ.filter fun index => hinvol.isHermitian.eigenvalues index = 1 with hpositiveSet
  have hsum : ∑ index, hinvol.isHermitian.eigenvalues index = 0 := by
    have htrace := hinvol.isHermitian.trace_eq_sum_eigenvalues
    rw [hinvol.trace_eq_zero] at htrace
    exact htrace.symm
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun index => hinvol.isHermitian.eigenvalues index = 1)
    (fun index => hinvol.isHermitian.eigenvalues index)
  have hpositive : ∑ index ∈ positiveSet, hinvol.isHermitian.eigenvalues index
      = (positiveSet.card : ℝ) := by
    rw [Finset.sum_congr rfl fun index hmember =>
      (Finset.mem_filter.mp hmember).2, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hnegative : ∑ index ∈ Finset.univ.filter
        (fun index => ¬ hinvol.isHermitian.eigenvalues index = 1),
        hinvol.isHermitian.eigenvalues index
      = -((Finset.univ.filter
          (fun index => ¬ hinvol.isHermitian.eigenvalues index = 1)).card : ℝ) := by
    rw [Finset.sum_congr rfl fun index hmember =>
      (hinvol.eigenvalues_eq_one_or_neg_one index).resolve_left
        (Finset.mem_filter.mp hmember).2, Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one]
  have hcards := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin size)))
    (p := fun index => hinvol.isHermitian.eigenvalues index = 1)
  rw [Finset.card_univ, Fintype.card_fin] at hcards
  rw [hpositive, hnegative, hsum] at hsplit
  have hreal : (positiveSet.card : ℝ) * 2 = (size : ℝ) := by
    have hcomplement : ((Finset.univ.filter
        (fun index => ¬ hinvol.isHermitian.eigenvalues index = 1)).card : ℝ)
        = (size : ℝ) - (positiveSet.card : ℝ) := by
      have := congrArg (fun count : ℕ => (count : ℝ)) hcards
      push_cast at this
      rw [hpositiveSet]
      linarith [this]
    rw [hcomplement] at hsplit
    linarith [hsplit]
  exact_mod_cast hreal

end IsHollowInvolution

/-! ## A hollow involution whose entries are NOT strictly inside `(-1,1)`

The pen brief's S1 asserts "entries in `(-1,1)`".  The CLOSED bound is
`IsHollowInvolution.abs_apply_le_one`; the open one is false, already at size
two. -/

/-- The two-point swap, a hollow symmetric involution with unit entries. -/
def swapInvolutionTwo : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

theorem isHollowInvolution_swapInvolutionTwo : IsHollowInvolution swapInvolutionTwo where
  symmetric := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> rfl
  square_eq_one := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [swapInvolutionTwo, Matrix.mul_apply, Fin.sum_univ_two]
  diagonal_eq_zero := fun index => by fin_cases index <;> rfl

/-- **REFUTATION of the pen's open entry bound, abstract half.**  A hollow
symmetric involution may have an off-diagonal entry of modulus exactly one. -/
theorem exists_isHollowInvolution_abs_apply_eq_one :
    ∃ invol : Matrix (Fin 2) (Fin 2) ℝ, IsHollowInvolution invol
      ∧ ∃ rowIndex colIndex : Fin 2, rowIndex ≠ colIndex ∧ |invol rowIndex colIndex| = 1 :=
  ⟨swapInvolutionTwo, isHollowInvolution_swapInvolutionTwo, 0, 1, by decide, by
    show |swapInvolutionTwo 0 1| = 1
    norm_num [swapInvolutionTwo]⟩

/-! ## S3 support: the hollow `3 x 3` block and the cap `sigma + 2|P| <= 1`

The compression of a hollow involution at a triple is a hollow symmetric `3 x 3`
matrix, and the two Loewner facts of the norm cap turn into two determinant
inequalities.  Their conjunction is the pen's `(C2)`. -/

/-- **The hollow symmetric `3 x 3` block** with off-diagonal entries
`(e1, e2, e3)` in the slots `(0,1)`, `(0,2)`, `(1,2)` — the same slot convention
as `Gtz.correlationMatrixThree`. -/
def hollowMatrixThree (edgeFirst edgeSecond edgeThird : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, edgeFirst, edgeSecond;
     edgeFirst, 0, edgeThird;
     edgeSecond, edgeThird, 0]

theorem hollowMatrixThree_transpose (edgeFirst edgeSecond edgeThird : ℝ) :
    (hollowMatrixThree edgeFirst edgeSecond edgeThird)ᵀ
      = hollowMatrixThree edgeFirst edgeSecond edgeThird := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> rfl

/-- Shifting the hollow block by the identity gives the unit-diagonal correlation
matrix — the bridge into the shipped elliptope layer. -/
theorem one_add_hollowMatrixThree (edgeFirst edgeSecond edgeThird : ℝ) :
    (1 : Matrix (Fin 3) (Fin 3) ℝ) + hollowMatrixThree edgeFirst edgeSecond edgeThird
      = correlationMatrixThree edgeFirst edgeSecond edgeThird := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [hollowMatrixThree, correlationMatrixThree]

theorem one_sub_hollowMatrixThree (edgeFirst edgeSecond edgeThird : ℝ) :
    (1 : Matrix (Fin 3) (Fin 3) ℝ) - hollowMatrixThree edgeFirst edgeSecond edgeThird
      = correlationMatrixThree (-edgeFirst) (-edgeSecond) (-edgeThird) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [hollowMatrixThree, correlationMatrixThree]

/-- **`(C2)`, the pen's norm consequence.**  When both Loewner halves of the norm
cap hold at a hollow `3 x 3` block, `sigma + 2|P| <= 1` where `sigma` is the sum
of the three squared edges and `P` their product.  Realness enters the whole U6
argument here and nowhere else: this is what excludes the tight weight
configuration of the pen's S4 (two disjoint triangles at `4/9`, whose
intra-triangle side has `sigma + 2 sqrt p = 52/27 > 1`). -/
theorem sq_sum_add_two_mul_abs_prod_le_one_of_posSemidef {edgeFirst edgeSecond edgeThird : ℝ}
    (hupper : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowMatrixThree edgeFirst edgeSecond edgeThird).PosSemidef)
    (hlower : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowMatrixThree edgeFirst edgeSecond edgeThird).PosSemidef) :
    edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2
      + 2 * |edgeFirst * edgeSecond * edgeThird| ≤ 1 := by
  have hupperDet : (0 : ℝ) ≤ 1 - edgeFirst ^ 2 - edgeSecond ^ 2 - edgeThird ^ 2
      - 2 * (edgeFirst * edgeSecond * edgeThird) := by
    have hdet := hupper.det_nonneg
    rw [one_sub_hollowMatrixThree, det_correlationMatrixThree, elliptopeBracket] at hdet
    nlinarith [hdet]
  have hlowerDet : (0 : ℝ) ≤ 1 - edgeFirst ^ 2 - edgeSecond ^ 2 - edgeThird ^ 2
      + 2 * (edgeFirst * edgeSecond * edgeThird) := by
    have hdet := hlower.det_nonneg
    rw [one_add_hollowMatrixThree, det_correlationMatrixThree, elliptopeBracket] at hdet
    nlinarith [hdet]
  rcases abs_cases (edgeFirst * edgeSecond * edgeThird) with ⟨habs, _⟩ | ⟨habs, _⟩ <;>
    rw [habs] <;> linarith

/-- The compression of a hollow involution at three indices IS the hollow `3 x 3`
block of its three entries.  Distinctness is NOT needed: the diagonal of the
compression is hollow whatever the selector does, and the symmetry supplies the
lower triangle. -/
theorem IsHollowInvolution.submatrix_three_eq_hollowMatrixThree
    {invol : Matrix (Fin size) (Fin size) ℝ} (hinvol : IsHollowInvolution invol)
    (firstIndex secondIndex thirdIndex : Fin size) :
    invol.submatrix ![firstIndex, secondIndex, thirdIndex]
        ![firstIndex, secondIndex, thirdIndex]
      = hollowMatrixThree (invol firstIndex secondIndex) (invol firstIndex thirdIndex)
          (invol secondIndex thirdIndex) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Matrix.submatrix_apply, hollowMatrixThree] <;>
    first
      | exact hinvol.diagonal_eq_zero _
      | rfl
      | exact hinvol.apply_comm _ _

/-- **THE NORM CAP AT A TRIPLE**, in scalar form: for any three distinct indices
of a hollow involution, `sigma + 2|P| <= 1`.  This is `(C2)` on the abstract
object; the design-level corollary is `Gtz.directionGram_normCap_triple`. -/
theorem IsHollowInvolution.normCap_triple {invol : Matrix (Fin size) (Fin size) ℝ}
    (hinvol : IsHollowInvolution invol) {firstIndex secondIndex thirdIndex : Fin size}
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex) :
    invol firstIndex secondIndex ^ 2 + invol firstIndex thirdIndex ^ 2
        + invol secondIndex thirdIndex ^ 2
      + 2 * |invol firstIndex secondIndex * invol firstIndex thirdIndex
          * invol secondIndex thirdIndex| ≤ 1 := by
  have hpick : Function.Injective ![firstIndex, secondIndex, thirdIndex] := by
    intro leftSlot rightSlot hvalue
    fin_cases leftSlot <;> fin_cases rightSlot <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hblock := hinvol.submatrix_three_eq_hollowMatrixThree firstIndex secondIndex thirdIndex
  have hupper := hinvol.posSemidef_one_sub_submatrix ![firstIndex, secondIndex, thirdIndex] hpick
  have hlower := hinvol.posSemidef_one_add_submatrix ![firstIndex, secondIndex, thirdIndex] hpick
  rw [hblock] at hupper hlower
  exact sq_sum_add_two_mul_abs_prod_le_one_of_posSemidef hupper hlower

/-! ## S1(b) The concrete object: the equal-share stratum -/

/-- **The raw pairing is the direction cosine scaled by the leverage.**  On a
design all of whose atoms have the same positive leverage `level`,
`<g_c, g_d> = level gamma_cd`.  At the `(6,3)` stratum, `<g_c,g_d> = 3 gamma_cd`.
Only uniform LEVERAGE is used, so this holds on the uniform-leverage stratum at
every size, `(7,3)` included. -/
theorem dotProduct_atom_eq_of_uniformLeverage (D : WeightedDesign m k) {level : ℝ}
    (hlevel : 0 < level) (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = level)
    (firstIndex secondIndex : Fin m) :
    D.atom firstIndex ⬝ᵥ D.atom secondIndex
      = level * directionGram D firstIndex secondIndex := by
  have hsqrt : Real.sqrt level * Real.sqrt level = level := Real.mul_self_sqrt hlevel.le
  have hinvSquare : (Real.sqrt level)⁻¹ * (Real.sqrt level)⁻¹ = level⁻¹ := by
    rw [← mul_inv, hsqrt]
  rw [directionGram_eq_scaled_atomPairing D firstIndex secondIndex, hleverage firstIndex,
    hleverage secondIndex, hinvSquare, ← mul_assoc, mul_inv_cancel₀ hlevel.ne', one_mul]

/-- **THE EQUAL-SHARE STRATUM.**  A weighted design with uniform weight `1/m` AND
uniform leverage `k`.  At `(m,k) = (6,3)` these are exactly the two hypotheses
the shipped uniform lemmas carry (`weight = 1/6`, `leverage = 3`), so the
predicate is their packaging and its projections drop straight into them.

BOTH conditions are load-bearing.  Uniform SHARE `t_c l_c = k/m` alone constrains
only the product and does not force either factor: with six atoms and shares
`1/2` the leverage vector `(2,2,4,4,4,4)` is admissible.  And `Gtz.Dominates` is
NOT invariant under the atom rescaling that fixes the shares — see the docstring
of `Gtz.directionDesign` — so the domination dictionary below genuinely needs
`leverage = k`, not merely `share = k/m`. -/
structure IsEqualShare (D : WeightedDesign m k) : Prop where
  /-- Every weight is `1/m`. -/
  weight_eq : ∀ atomIndex, D.weight atomIndex = (m : ℝ)⁻¹
  /-- Every leverage is the rank. -/
  leverage_eq : ∀ atomIndex, leverageOf (D.atom atomIndex) = (k : ℝ)

private theorem sizePositive (D : WeightedDesign m k) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with hzero | hpositive
  · subst hzero
    have hsum := D.weight_sum_one
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact absurd hsum (by norm_num)
  · exact hpositive

namespace IsEqualShare

variable {D : WeightedDesign m k}

/-- The stratum is nonempty of atoms. -/
theorem size_pos (_hequal : IsEqualShare D) : 0 < m := sizePositive D

/-- At positive rank every atom is nondegenerate. -/
theorem leverage_pos (hequal : IsEqualShare D) (hrank : 0 < k) (atomIndex : Fin m) :
    0 < leverageOf (D.atom atomIndex) := by
  rw [hequal.leverage_eq atomIndex]
  exact_mod_cast hrank

/-- The share is the rank-to-size ratio at every atom. -/
theorem atomShare_eq (hequal : IsEqualShare D) (atomIndex : Fin m) :
    atomShare D atomIndex = (k : ℝ) / (m : ℝ) := by
  rw [atomShare, hequal.weight_eq atomIndex, hequal.leverage_eq atomIndex, inv_mul_eq_div]

/-- Every direction has unit self-correlation. -/
theorem directionGram_self (hequal : IsEqualShare D) (hrank : 0 < k) (atomIndex : Fin m) :
    directionGram D atomIndex atomIndex = 1 :=
  Gtz.directionGram_self D (hequal.leverage_pos hrank atomIndex)

/-- At rank at least two the stratum is all-heavy, so every shipped `AllHeavy`
lemma applies without further argument. -/
theorem allHeavy (hequal : IsEqualShare D) (hrank : 2 ≤ k) : AllHeavy D := by
  intro atomIndex
  rw [hequal.leverage_eq atomIndex]
  exact_mod_cast hrank

/-- **The raw pairing is the direction cosine scaled by the rank**:
`<g_c, g_d> = k gamma_cd`.  At the `(6,3)` stratum, `<g_c,g_d> = 3 gamma_cd`. -/
theorem dotProduct_atom_eq (hequal : IsEqualShare D) (hrank : 0 < k)
    (firstIndex secondIndex : Fin m) :
    D.atom firstIndex ⬝ᵥ D.atom secondIndex = (k : ℝ) * directionGram D firstIndex secondIndex :=
  dotProduct_atom_eq_of_uniformLeverage D (by exact_mod_cast hrank) hequal.leverage_eq
    firstIndex secondIndex

end IsEqualShare

/-! ### The stratum's involution -/

/-- **The correlation involution** `M = Gamma - 1` of a design: the hollow shadow
of its direction Gram. -/
noncomputable def correlationInvolution (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  directionGramMatrix D - 1

theorem correlationInvolution_apply_of_ne (D : WeightedDesign m k) {firstIndex secondIndex : Fin m}
    (hdistinct : firstIndex ≠ secondIndex) :
    correlationInvolution D firstIndex secondIndex = directionGram D firstIndex secondIndex := by
  rw [correlationInvolution, Matrix.sub_apply, Matrix.one_apply_ne hdistinct, sub_zero]
  rfl

theorem correlationInvolution_apply_self (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) :
    correlationInvolution D atomIndex atomIndex = 0 := by
  rw [correlationInvolution, Matrix.sub_apply, Matrix.one_apply_eq,
    show directionGramMatrix D atomIndex atomIndex = directionGram D atomIndex atomIndex from rfl,
    Gtz.directionGram_self D hpositive, sub_self]

/-- **The correlation involution compressed at a triple IS the hollow block of the
three direction cosines.**  Needs only nondegenerate atoms and three distinct
indices — no involution, hence no `m = 2k`.  This is the entrywise reading that
lets the `(6,3)` dictionary be stated at every size. -/
theorem correlationInvolution_submatrix_three_eq_hollowMatrixThree (D : WeightedDesign m k)
    (hpositive : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex))
    {firstIndex secondIndex thirdIndex : Fin m} (hfirstSecond : firstIndex ≠ secondIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) (hsecondThird : secondIndex ≠ thirdIndex) :
    (correlationInvolution D).submatrix ![firstIndex, secondIndex, thirdIndex]
        ![firstIndex, secondIndex, thirdIndex]
      = hollowMatrixThree (directionGram D firstIndex secondIndex)
          (directionGram D firstIndex thirdIndex) (directionGram D secondIndex thirdIndex) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Matrix.submatrix_apply, hollowMatrixThree] <;>
    first
      | exact correlationInvolution_apply_self D (hpositive _)
      | exact correlationInvolution_apply_of_ne D hfirstSecond
      | exact correlationInvolution_apply_of_ne D hfirstThird
      | exact correlationInvolution_apply_of_ne D hsecondThird
      | exact (correlationInvolution_apply_of_ne D (Ne.symm hfirstSecond)).trans
          (directionGram_comm D secondIndex firstIndex)
      | exact (correlationInvolution_apply_of_ne D (Ne.symm hfirstThird)).trans
          (directionGram_comm D thirdIndex firstIndex)
      | exact (correlationInvolution_apply_of_ne D (Ne.symm hsecondThird)).trans
          (directionGram_comm D thirdIndex secondIndex)

/-- **`Gamma^2 = (m/k) Gamma` on the stratum.**  The shipped idempotency identity
`Gamma diag(s) Gamma = Gamma` with the share diagonal collapsed to the scalar
`k/m`. -/
theorem directionGramMatrix_sq_of_isEqualShare (D : WeightedDesign m k)
    (hequal : IsEqualShare D) (hrank : 0 < k) :
    directionGramMatrix D * directionGramMatrix D
      = ((m : ℝ) / (k : ℝ)) • directionGramMatrix D := by
  have hsizeReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hequal.size_pos
  have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
  have hsharePos : (0 : ℝ) < (k : ℝ) / (m : ℝ) := div_pos hrankReal hsizeReal
  have hmaster := directionGramMatrix_mul_diagonal_atomShare_mul_self D
  have hdiagonal : Matrix.diagonal (atomShare D)
      = ((k : ℝ) / (m : ℝ)) • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    ext rowIndex colIndex
    simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs with hequalIndex
    · rw [hequal.atomShare_eq rowIndex, mul_one]
    · rw [mul_zero]
  rw [hdiagonal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at hmaster
  have hscaled := congrArg (fun target => ((k : ℝ) / (m : ℝ))⁻¹ • target) hmaster
  simp only [smul_smul, inv_mul_cancel₀ hsharePos.ne', one_smul] at hscaled
  rw [hscaled, inv_div]

/-- **THE INVOLUTION LAW.**  On the equal-share stratum with `m = 2k` the
correlation matrix `M = Gamma - 1` is a hollow symmetric involution.  The
hypothesis `m = 2k` is genuinely needed: at a general size the identity is
`M^2 = (m/k - 2) Gamma + 1`, and only the doubling makes the correction vanish.
This is exactly why the argument is a `(6,3)` tool and not a `(7,3)` tool. -/
theorem isHollowInvolution_correlationInvolution (D : WeightedDesign m k)
    (hequal : IsEqualShare D) (hrank : 0 < k) (hdouble : (m : ℝ) = 2 * (k : ℝ)) :
    IsHollowInvolution (correlationInvolution D) where
  symmetric := by
    ext rowIndex colIndex
    show directionGramMatrix D colIndex rowIndex - (1 : Matrix (Fin m) (Fin m) ℝ) colIndex rowIndex
      = directionGramMatrix D rowIndex colIndex - (1 : Matrix (Fin m) (Fin m) ℝ) rowIndex colIndex
    rw [show directionGramMatrix D colIndex rowIndex
        = directionGram D colIndex rowIndex from rfl,
      show directionGramMatrix D rowIndex colIndex
        = directionGram D rowIndex colIndex from rfl,
      directionGram_comm D colIndex rowIndex, Matrix.one_apply, Matrix.one_apply]
    split_ifs with hforward hbackward hbackward
    · rfl
    · exact absurd hforward.symm hbackward
    · exact absurd hbackward.symm hforward
    · rfl
  square_eq_one := by
    have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
    have hratio : (m : ℝ) / (k : ℝ) = 2 := by
      rw [hdouble]
      field_simp
    have hsquare := directionGramMatrix_sq_of_isEqualShare D hequal hrank
    rw [hratio] at hsquare
    rw [correlationInvolution, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, hsquare]
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    split_ifs <;> ring
  diagonal_eq_zero := fun atomIndex =>
    correlationInvolution_apply_self D (hequal.leverage_pos hrank atomIndex)

/-! ### The stratum's S1 laws, read off the involution -/

/-- **THE ROW LAW ON THE STRATUM**: `sum_{d /= c} gamma_cd^2 = 1` at every atom of
an equal-share design of size `2k`.  Read off the diagonal of `M^2 = 1`. -/
theorem sum_sq_directionGram_erase_of_isEqualShare (D : WeightedDesign m k)
    (hequal : IsEqualShare D) (hrank : 0 < k) (hdouble : (m : ℝ) = 2 * (k : ℝ))
    (atomIndex : Fin m) :
    ∑ otherIndex ∈ Finset.univ.erase atomIndex, directionGram D atomIndex otherIndex ^ 2 = 1 := by
  have hinvol := isHollowInvolution_correlationInvolution D hequal hrank hdouble
  rw [← hinvol.sum_sq_row_erase atomIndex]
  refine Finset.sum_congr rfl fun otherIndex hmember => ?_
  rw [correlationInvolution_apply_of_ne D (Ne.symm (Finset.mem_erase.mp hmember).1)]

/-- **THE VANISHING SUPPLY CHAIN ON THE STRATUM**:
`sum_{d /= a,b} gamma_ad gamma_db = 0`.  The shipped supply-chain law says the
sum equals `(1 - s_a - s_b) gamma_ab`, and on this stratum both shares are `1/2`,
so the coefficient is exactly zero.  Read here instead off the off-diagonal of
`M^2 = 1`, which needs no share bookkeeping at all. -/
theorem sum_sdiff_directionGram_mul_of_isEqualShare (D : WeightedDesign m k)
    (hequal : IsEqualShare D) (hrank : 0 < k) (hdouble : (m : ℝ) = 2 * (k : ℝ))
    {firstIndex secondIndex : Fin m} (hdistinct : firstIndex ≠ secondIndex) :
    ∑ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin m)),
        directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex = 0 := by
  have hinvol := isHollowInvolution_correlationInvolution D hequal hrank hdouble
  rw [← hinvol.sum_sdiff_pair_mul hdistinct]
  refine Finset.sum_congr rfl fun otherIndex hmember => ?_
  have hnotPair := (Finset.mem_sdiff.mp hmember).2
  have hneFirst : firstIndex ≠ otherIndex := by
    intro hcontra
    exact hnotPair (by rw [← hcontra]; exact Finset.mem_insert_self _ _)
  have hneSecond : otherIndex ≠ secondIndex := by
    intro hcontra
    exact hnotPair (by rw [hcontra]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [correlationInvolution_apply_of_ne D hneFirst, correlationInvolution_apply_of_ne D hneSecond]

/-- **THE NORM CAP ON THE STRATUM**, in the pen's scalar form `(C2)`:
`sigma_C + 2 |P_C| <= 1` at every triple of distinct atoms, where
`sigma_C = sum of the three squared direction cosines` and `P_C` is their
product.  Everything the U6 squeeze spends realness on passes through here. -/
theorem directionGram_normCap_triple (D : WeightedDesign m k) (hequal : IsEqualShare D)
    (hrank : 0 < k) (hdouble : (m : ℝ) = 2 * (k : ℝ)) {firstIndex secondIndex thirdIndex : Fin m}
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex) :
    directionGram D firstIndex secondIndex ^ 2 + directionGram D firstIndex thirdIndex ^ 2
        + directionGram D secondIndex thirdIndex ^ 2
      + 2 * |directionGram D firstIndex secondIndex * directionGram D firstIndex thirdIndex
          * directionGram D secondIndex thirdIndex| ≤ 1 := by
  have hinvol := isHollowInvolution_correlationInvolution D hequal hrank hdouble
  have hcap := hinvol.normCap_triple hfirstSecond hfirstThird hsecondThird
  rw [correlationInvolution_apply_of_ne D hfirstSecond,
    correlationInvolution_apply_of_ne D hfirstThird,
    correlationInvolution_apply_of_ne D hsecondThird] at hcap
  exact hcap

/-! ## S1(c) The dictionary

Three equivalent readings of `Gtz.Dominates` on the stratum.  The frame reading
holds at an arbitrary subset and arbitrary uniform leverage; the Gram readings
are stated at a triple, where they are what the covering sentence consumes. -/

/-- The unit-direction frame sum `sum_{c in C} u_c u_c^T` of a subset. -/
noncomputable def unitFrameSum (D : WeightedDesign m k) (C : Finset (Fin m)) :
    Matrix (Fin k) (Fin k) ℝ :=
  ∑ atomIndex ∈ C, atomMatrix (unitAtom D atomIndex)

/-- On a uniform-leverage design the raw atom sum is the direction sum scaled by
the common leverage. -/
theorem subsetSum_eq_smul_unitFrameSum (D : WeightedDesign m k) {level : ℝ} (hlevel : 0 < level)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = level) (C : Finset (Fin m)) :
    subsetSum D C = level • unitFrameSum D C := by
  rw [subsetSum, unitFrameSum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [atomMatrix_unitAtom D atomIndex, hleverage atomIndex, smul_smul,
    mul_inv_cancel₀ hlevel.ne', one_smul]

/-- **THE DICTIONARY, frame side.**  On a uniform-leverage design a subset
dominates exactly when its unit directions resolve at the reciprocal level:
`sum_{c in C} u_c u_c^T ⪰ (1/level) 1`.  No distinctness, no cardinality, no
condition on the weights — only uniform leverage, so this is available at `(7,3)`
as well as at `(6,3)`.  Composed with the Gram-side dictionary below it yields the
`AB`-versus-`BA` transfer, landed as
`Gtz.posSemidef_unitFrameSum_iff_posSemidef_directionGramMatrix_submatrix`. -/
theorem dominates_iff_posSemidef_unitFrameSum (D : WeightedDesign m k) {level : ℝ}
    (hlevel : 0 < level) (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = level)
    (C : Finset (Fin m)) :
    Dominates D C ↔ (unitFrameSum D C - level⁻¹ • 1).PosSemidef := by
  have hshape : subsetSum D C - 1
      = level • (unitFrameSum D C - level⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
    rw [subsetSum_eq_smul_unitFrameSum D hlevel hleverage C, smul_sub, smul_smul,
      mul_inv_cancel₀ hlevel.ne', one_smul]
  rw [Dominates, hshape]
  exact posSemidef_smul_iff hlevel

/-- **The gap matrix of a triple is the shifted hollow block, scaled by three.**
The entrywise bridge from the shipped `Gtz.tripleGapMatrix` — whose diagonal is
`leverage - 1 = 2` and whose off-diagonal is `<g_c,g_d> = 3 gamma_cd` — into the
pen's `M[C] + (2/3) 1`.  No injectivity is needed because `hollowMatrixThree`
carries its zeros explicitly. -/
theorem tripleGapMatrix_eq_smul_hollowShift (D : WeightedDesign m 3)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    (firstIndex secondIndex thirdIndex : Fin m) :
    tripleGapMatrix D firstIndex secondIndex thirdIndex
      = (3 : ℝ) • (hollowMatrixThree (directionGram D firstIndex secondIndex)
          (directionGram D firstIndex thirdIndex) (directionGram D secondIndex thirdIndex)
        + (2 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
  have hpair : ∀ leftIndex rightIndex : Fin m,
      atomPairing D leftIndex rightIndex = 3 * directionGram D leftIndex rightIndex := by
    intro leftIndex rightIndex
    have hdot := dotProduct_atom_eq_of_uniformLeverage D (by norm_num) hleverage leftIndex
      rightIndex
    rw [atomPairing, hdot]
  have hexcess : ∀ atomIndex : Fin m, heavyExcess D atomIndex = 2 := by
    intro atomIndex
    rw [heavyExcess, hleverage atomIndex]
    norm_num
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, tripleGapMatrix, hollowMatrixThree,
      Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.of_apply, Fin.reduceEq, if_true, if_false] <;>
    first
      | (rw [hexcess]; norm_num)
      | (rw [hpair]; norm_num)

/-- **THE DICTIONARY, Gram side.**  A triple of distinct atoms of a design of rank
three all of whose leverages are `3` dominates exactly when the hollow block of
its three direction cosines, shifted by `2/3`, is positive semidefinite.  On the
equal-share `(6,3)` stratum that block IS the compression `M[C]` of the
correlation involution (next theorem), so the condition reads
`lambda_min(M[C]) >= -2/3`; at other sizes the block is still the right object,
there just is no involution behind it.

Routed through `Gtz.dominates_triple_iff_posSemidef_tripleGapMatrix`, which is a
statement about the GRAM gap and needs only distinctness.  The congruence is
never asserted about `Gtz.subsetSum` (the FRAME gap), where it is refuted at
`tetraDesign`. -/
theorem dominates_triple_iff_posSemidef_hollowShift (D : WeightedDesign m 3)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {firstIndex secondIndex thirdIndex : Fin m}
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex) :
    Dominates D {firstIndex, secondIndex, thirdIndex}
      ↔ (hollowMatrixThree (directionGram D firstIndex secondIndex)
          (directionGram D firstIndex thirdIndex) (directionGram D secondIndex thirdIndex)
        + (2 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  rw [dominates_triple_iff_posSemidef_tripleGapMatrix D hfirstSecond hfirstThird hsecondThird,
    tripleGapMatrix_eq_smul_hollowShift D hleverage firstIndex secondIndex thirdIndex]
  exact posSemidef_smul_iff (by norm_num)

/-- **THE DICTIONARY, `M[C]` form.**  The same statement with the block written as
the literal compression of the correlation involution — the form the squeeze
consumes.  No `m = 2k`: the compression identity is entrywise. -/
theorem dominates_triple_iff_posSemidef_correlationInvolution_submatrix (D : WeightedDesign m 3)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {firstIndex secondIndex thirdIndex : Fin m}
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex) :
    Dominates D {firstIndex, secondIndex, thirdIndex}
      ↔ ((correlationInvolution D).submatrix ![firstIndex, secondIndex, thirdIndex]
            ![firstIndex, secondIndex, thirdIndex]
          + (2 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  have hpositive : ∀ atomIndex : Fin m, 0 < leverageOf (D.atom atomIndex) := fun atomIndex => by
    rw [hleverage atomIndex]; norm_num
  rw [correlationInvolution_submatrix_three_eq_hollowMatrixThree D hpositive hfirstSecond
    hfirstThird hsecondThird]
  exact dominates_triple_iff_posSemidef_hollowShift D hleverage hfirstSecond hfirstThird
    hsecondThird

/-- **THE DICTIONARY, `Gamma[C]` form.**  `Dominates` is `Gamma[C] ⪰ (1/3) 1`. -/
theorem dominates_triple_iff_posSemidef_directionGramMatrix_submatrix (D : WeightedDesign m 3)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {firstIndex secondIndex thirdIndex : Fin m}
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex) :
    Dominates D {firstIndex, secondIndex, thirdIndex}
      ↔ ((directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
            ![firstIndex, secondIndex, thirdIndex]
          - (3 : ℝ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  have hpick : Function.Injective ![firstIndex, secondIndex, thirdIndex] := by
    intro leftSlot rightSlot hvalue
    fin_cases leftSlot <;> fin_cases rightSlot <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hshape : (directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
        ![firstIndex, secondIndex, thirdIndex] - (3 : ℝ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = (correlationInvolution D).submatrix ![firstIndex, secondIndex, thirdIndex]
          ![firstIndex, secondIndex, thirdIndex]
        + (2 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    have hsub : (correlationInvolution D).submatrix ![firstIndex, secondIndex, thirdIndex]
        ![firstIndex, secondIndex, thirdIndex]
        = (directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
            ![firstIndex, secondIndex, thirdIndex] - 1 := by
      rw [correlationInvolution, show (directionGramMatrix D - 1).submatrix
          ![firstIndex, secondIndex, thirdIndex] ![firstIndex, secondIndex, thirdIndex]
          = (directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
              ![firstIndex, secondIndex, thirdIndex]
            - (1 : Matrix (Fin m) (Fin m) ℝ).submatrix ![firstIndex, secondIndex, thirdIndex]
              ![firstIndex, secondIndex, thirdIndex] from rfl,
        Matrix.submatrix_one _ hpick]
    rw [hsub]
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    split_ifs <;> ring
  rw [hshape]
  exact dominates_triple_iff_posSemidef_correlationInvolution_submatrix D hleverage hfirstSecond
    hfirstThird hsecondThird

/-- **The level test against `lambdaMinMat`, as a Loewner statement.**  For a
symmetric matrix, `level <= lambda_min` is exactly `target - level 1 ⪰ 0`.  The
repository carried the Rayleigh half (`Gtz.le_lambdaMinMat_iff_forall_dotProduct`)
and the eigenvalue half separately; this is the Loewner bridge between them. -/
theorem le_lambdaMinMat_iff_posSemidef_sub_smul_one {dim : ℕ} [Nonempty (Fin dim)]
    (target : Matrix (Fin dim) (Fin dim) ℝ) (hsymmetric : targetᵀ = target) (level : ℝ) :
    level ≤ lambdaMinMat target
      ↔ (target - level • (1 : Matrix (Fin dim) (Fin dim) ℝ)).PosSemidef := by
  have hgapSymmetric : (target - level • (1 : Matrix (Fin dim) (Fin dim) ℝ))ᵀ
      = target - level • 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hsymmetric]
  have hform : ∀ direction : Fin dim → ℝ,
      direction ⬝ᵥ ((target - level • (1 : Matrix (Fin dim) (Fin dim) ℝ)) *ᵥ direction)
        = direction ⬝ᵥ (target *ᵥ direction) - level * (direction ⬝ᵥ direction) := by
    intro direction
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
  rw [le_lambdaMinMat_iff_forall_dotProduct target level,
    posSemidef_iff_quadForm_nonneg _ hgapSymmetric]
  constructor
  · intro hlevel direction
    rw [hform direction]
    linarith [hlevel direction]
  · intro hpsd direction
    have hgoal := hpsd direction
    rw [hform direction] at hgoal
    linarith [hgoal]

/-- **THE DICTIONARY, least-eigenvalue form.**  A triple of the `(6,3)`
equal-share stratum dominates exactly when `lambda_min(Gamma[C]) >= 1/3`.  This
is the pen's calibration coordinate: the Mercedes/tetrahedral tripod sits at
exactly `1/3` (the tie), `K_4`'s stars at `1/2`, and the icosahedron's coherent
triples at `1 - 1/sqrt 5`. -/
theorem dominates_triple_iff_inv_three_le_lambdaMinMat (D : WeightedDesign m 3)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {firstIndex secondIndex thirdIndex : Fin m}
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex) :
    Dominates D {firstIndex, secondIndex, thirdIndex}
      ↔ (3 : ℝ)⁻¹ ≤ lambdaMinMat ((directionGramMatrix D).submatrix
          ![firstIndex, secondIndex, thirdIndex] ![firstIndex, secondIndex, thirdIndex]) := by
  have hsymmetric : ((directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
      ![firstIndex, secondIndex, thirdIndex])ᵀ
      = (directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
          ![firstIndex, secondIndex, thirdIndex] := by
    ext rowIndex colIndex
    exact directionGram_comm D _ _
  rw [le_lambdaMinMat_iff_posSemidef_sub_smul_one _ hsymmetric]
  exact dominates_triple_iff_posSemidef_directionGramMatrix_submatrix D hleverage hfirstSecond
    hfirstThird hsecondThird

/-- **The `AB`-versus-`BA` transfer at the stratum's own level**, obtained by
composing the two dictionaries rather than by a separate spectral argument: for a
triple of distinct atoms of a uniform-leverage-three design, the FRAME gap
`sum_{c in C} u_c u_c^T - (1/3) 1` (coordinate space, `3 x 3` because the rank is
three) and the GRAM gap `Gamma[C] - (1/3) 1` (slot space) have the same Loewner
status.  This is the hinge the mirror law of the pen's S2 wants, and it needs no
characteristic polynomial: both sides are equivalent to the same `Gtz.Dominates`. -/
theorem posSemidef_unitFrameSum_iff_posSemidef_directionGramMatrix_submatrix
    (D : WeightedDesign m 3) (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {firstIndex secondIndex thirdIndex : Fin m} (hfirstSecond : firstIndex ≠ secondIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) (hsecondThird : secondIndex ≠ thirdIndex) :
    (unitFrameSum D {firstIndex, secondIndex, thirdIndex} - (3 : ℝ)⁻¹ • 1).PosSemidef
      ↔ ((directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
            ![firstIndex, secondIndex, thirdIndex] - (3 : ℝ)⁻¹ • 1).PosSemidef :=
  (dominates_iff_posSemidef_unitFrameSum D (by norm_num) hleverage
      {firstIndex, secondIndex, thirdIndex}).symm.trans
    (dominates_triple_iff_posSemidef_directionGramMatrix_submatrix D hleverage hfirstSecond
      hfirstThird hsecondThird)

/-! ## The `rho`-versus-`gamma` coordinate bridge

This repository's per-triple coordinate is `Gtz.normalizedPairing`; the pen's is
the direction cosine.  On the `(6,3)` equal-share stratum they differ by exactly
`3/2`, and every shipped threshold has to be rescaled accordingly. -/

/-- **`rho = (3/2) gamma` on the equal-share `(6,3)` stratum.**  The normalized
pairing divides the raw pairing `3 gamma` by `sqrt(x_c x_d) = 2`.  Consequently
the shipped box cell `rho^2 <= 1/4` is `gamma^2 <= 1/9`, the half-box
`rho^2 <= 1/2` is `gamma^2 <= 2/9`, and compatibility `rho^2 <= 1` is
`|gamma| <= 2/3`. -/
theorem normalizedPairing_eq_three_halves_mul_directionGram (D : WeightedDesign m 3)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    (firstIndex secondIndex : Fin m) :
    normalizedPairing D firstIndex secondIndex
      = (3 / 2 : ℝ) * directionGram D firstIndex secondIndex := by
  have hexcess : ∀ atomIndex : Fin m, heavyExcess D atomIndex = 2 := by
    intro atomIndex
    rw [heavyExcess, hleverage atomIndex]
    norm_num
  have hdot := dotProduct_atom_eq_of_uniformLeverage D (by norm_num) hleverage firstIndex
    secondIndex
  rw [normalizedPairing, hexcess, hexcess, atomPairing, hdot,
    show (2 : ℝ) * 2 = 4 from by norm_num,
    show Real.sqrt 4 = 2 from by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]]
  norm_num
  ring

/-- **The two coordinate systems, as one matrix identity.**  The shipped
`correlationMatrixThree` in `rho` coordinates IS the pen's shifted hollow block
in `gamma` coordinates, scaled by `3/2`.  Reading a `rho`-statement as a
`gamma`-statement without this factor silently changes every threshold. -/
theorem correlationMatrixThree_normalizedPairing_eq_smul_hollowShift (D : WeightedDesign m 3)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    (firstIndex secondIndex thirdIndex : Fin m) :
    correlationMatrixThree (normalizedPairing D firstIndex secondIndex)
        (normalizedPairing D firstIndex thirdIndex)
        (normalizedPairing D secondIndex thirdIndex)
      = (3 / 2 : ℝ) • (hollowMatrixThree (directionGram D firstIndex secondIndex)
          (directionGram D firstIndex thirdIndex) (directionGram D secondIndex thirdIndex)
        + (2 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
  rw [normalizedPairing_eq_three_halves_mul_directionGram D hleverage firstIndex secondIndex,
    normalizedPairing_eq_three_halves_mul_directionGram D hleverage firstIndex thirdIndex,
    normalizedPairing_eq_three_halves_mul_directionGram D hleverage secondIndex thirdIndex]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [correlationMatrixThree, hollowMatrixThree, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply, smul_eq_mul] <;>
    norm_num

/-! ## Abstract to concrete: designs built out of unit-row tight frames

The squeeze consumes the abstract form; GTZ consumes the concrete one.  The map
from concrete to abstract is `Gtz.isHollowInvolution_correlationInvolution`.  In
the other direction, a unit-row tight frame — which is exactly the geometric
content of the abstract object — produces a design of the stratum whose
correlation matrix is the frame's own Gram. -/

/-- **A design out of a unit-row tight frame.**  Rows `u_c` of unit length with
`sum_c u_c u_c^T = (m/k) 1` give an equal-share design with atoms
`g_c = sqrt(k) u_c` and weights `1/m`. -/
noncomputable def tightFrameDesign (frame : Matrix (Fin m) (Fin k) ℝ) (hsize : 0 < m)
    (hrank : 0 < k) (htight : frameᵀ * frame = ((m : ℝ) / (k : ℝ)) • 1) : WeightedDesign m k where
  atom := fun atomIndex => Real.sqrt (k : ℝ) • frame atomIndex
  weight := fun _ => (m : ℝ)⁻¹
  weight_pos := fun _ => inv_pos.mpr (by exact_mod_cast hsize)
  weight_sum_one := by
    have hsizeReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hsize
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ hsizeReal.ne']
  isParseval := by
    have hsizeReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hsize
    have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
    have hsqrt : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hrankReal.le
    have hrows : ∑ atomIndex, atomMatrix (frame atomIndex) = frameᵀ * frame :=
      (transpose_mul_self_eq_sum_rows frame).symm
    calc ∑ atomIndex, (m : ℝ)⁻¹ • atomMatrix (Real.sqrt (k : ℝ) • frame atomIndex)
        = ((m : ℝ)⁻¹ * (k : ℝ)) • ∑ atomIndex, atomMatrix (frame atomIndex) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun atomIndex _ => ?_
          rw [atomMatrix_smul, hsqrt, smul_smul]
      _ = ((m : ℝ)⁻¹ * (k : ℝ)) • (((m : ℝ) / (k : ℝ)) • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
          rw [hrows, htight]
      _ = 1 := by
          rw [smul_smul, show ((m : ℝ)⁻¹ * (k : ℝ)) * ((m : ℝ) / (k : ℝ)) = 1 from by field_simp,
            one_smul]

theorem tightFrameDesign_atom (frame : Matrix (Fin m) (Fin k) ℝ) (hsize : 0 < m) (hrank : 0 < k)
    (htight : frameᵀ * frame = ((m : ℝ) / (k : ℝ)) • 1) (atomIndex : Fin m) :
    (tightFrameDesign frame hsize hrank htight).atom atomIndex
      = Real.sqrt (k : ℝ) • frame atomIndex := rfl

/-- Unit rows are exactly what makes the tight-frame design equal-share. -/
theorem isEqualShare_tightFrameDesign (frame : Matrix (Fin m) (Fin k) ℝ) (hsize : 0 < m)
    (hrank : 0 < k) (htight : frameᵀ * frame = ((m : ℝ) / (k : ℝ)) • 1)
    (hunit : ∀ atomIndex, leverageOf (frame atomIndex) = 1) :
    IsEqualShare (tightFrameDesign frame hsize hrank htight) where
  weight_eq := fun _ => rfl
  leverage_eq := fun atomIndex => by
    have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
    rw [tightFrameDesign_atom, leverageOf_smul, Real.sq_sqrt hrankReal.le, hunit atomIndex,
      mul_one]

/-- The frame rows ARE the design's unit directions. -/
theorem unitAtom_tightFrameDesign (frame : Matrix (Fin m) (Fin k) ℝ) (hsize : 0 < m)
    (hrank : 0 < k) (htight : frameᵀ * frame = ((m : ℝ) / (k : ℝ)) • 1)
    (hunit : ∀ atomIndex, leverageOf (frame atomIndex) = 1) (atomIndex : Fin m) :
    unitAtom (tightFrameDesign frame hsize hrank htight) atomIndex = frame atomIndex := by
  have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
  have hsqrtPos : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hrankReal
  have hleverage := (isEqualShare_tightFrameDesign frame hsize hrank htight hunit).leverage_eq
    atomIndex
  rw [unitAtom, hleverage, tightFrameDesign_atom, smul_smul, inv_mul_cancel₀ hsqrtPos.ne',
    one_smul]

/-- The design's direction Gram is the frame's own Gram. -/
theorem directionGram_tightFrameDesign (frame : Matrix (Fin m) (Fin k) ℝ) (hsize : 0 < m)
    (hrank : 0 < k) (htight : frameᵀ * frame = ((m : ℝ) / (k : ℝ)) • 1)
    (hunit : ∀ atomIndex, leverageOf (frame atomIndex) = 1) (firstIndex secondIndex : Fin m) :
    directionGram (tightFrameDesign frame hsize hrank htight) firstIndex secondIndex
      = frame firstIndex ⬝ᵥ frame secondIndex := by
  rw [directionGram, unitAtom_tightFrameDesign frame hsize hrank htight hunit,
    unitAtom_tightFrameDesign frame hsize hrank htight hunit]

/-! ## The stratum is inhabited, and its boundary is real

Two points of the equal-share `(6,3)` stratum: the icosahedron (the maximal real
equiangular set, all fifteen `gamma^2 = 1/5`) and the octahedron (three antipodal
pairs, `gamma = -1` on each).  The second refutes the pen's open entry bound and
shows the "pairwise non-parallel" hypothesis is unnecessary for U6. -/

/-- **The icosahedron design is a point of the equal-share `(6,3)` stratum.**  The
non-vacuity witness: `Gtz.icosaDesign` has uniform weight `1/6` and uniform
leverage `3` by construction. -/
theorem isEqualShare_icosaDesign : IsEqualShare icosaDesign where
  weight_eq := fun _ => by
    show (1 : ℝ) / 6 = ((6 : ℕ) : ℝ)⁻¹
    norm_num
  leverage_eq := fun atomIndex => by
    rw [leverageOf_eq_dotProduct, icosaDesign_atom, icosaAtom_leverage]
    norm_num

/-- Hence the icosahedron carries a hollow symmetric involution. -/
theorem isHollowInvolution_icosaDesign : IsHollowInvolution (correlationInvolution icosaDesign) :=
  isHollowInvolution_correlationInvolution icosaDesign isEqualShare_icosaDesign (by norm_num)
    (by norm_num)

/-- The six coordinate directions `±e_1, ±e_2, ±e_3` as a unit-row frame. -/
def octahedronFrame : Matrix (Fin 6) (Fin 3) ℝ :=
  Matrix.of ![![1, 0, 0], ![-1, 0, 0], ![0, 1, 0], ![0, -1, 0], ![0, 0, 1], ![0, 0, -1]]

theorem octahedronFrame_tight :
    octahedronFrameᵀ * octahedronFrame = ((6 : ℕ) / ((3 : ℕ) : ℝ) : ℝ) • 1 := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [octahedronFrame, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

theorem octahedronFrame_unit (atomIndex : Fin 6) : leverageOf (octahedronFrame atomIndex) = 1 := by
  fin_cases atomIndex <;>
    simp [octahedronFrame, leverageOf, Fin.sum_univ_three]

/-- **The octahedron as an equal-share `(6,3)` design**: six unit directions with
three antipodal pairs, weight `1/6`, leverage `3`. -/
noncomputable def octahedronDesign : WeightedDesign 6 3 :=
  tightFrameDesign octahedronFrame (by norm_num) (by norm_num) octahedronFrame_tight

theorem isEqualShare_octahedronDesign : IsEqualShare octahedronDesign :=
  isEqualShare_tightFrameDesign octahedronFrame (by norm_num) (by norm_num) octahedronFrame_tight
    octahedronFrame_unit

/-- **REFUTATION of the pen's open entry bound, concrete half.**  The antipodal
pair `{e_1, -e_1}` of the octahedron has direction cosine exactly `-1`. -/
theorem directionGram_octahedronDesign_zero_one : directionGram octahedronDesign 0 1 = -1 := by
  rw [octahedronDesign, directionGram_tightFrameDesign octahedronFrame (by norm_num) (by norm_num)
    octahedronFrame_tight octahedronFrame_unit]
  simp [octahedronFrame, dotProduct, Fin.sum_univ_three]

/-- **The pen's "entries in `(-1,1)`" is FALSE on the equal-share `(6,3)`
stratum.**  The closed bound `|gamma| <= 1` is the true statement
(`Gtz.abs_directionGram_le_one`, shipped); the strict one needs the pairwise
non-parallel hypothesis, which the octahedron violates. -/
theorem not_forall_abs_directionGram_lt_one_of_isEqualShare :
    ¬ ∀ (D : WeightedDesign 6 3), IsEqualShare D →
        ∀ firstIndex secondIndex : Fin 6, firstIndex ≠ secondIndex →
          |directionGram D firstIndex secondIndex| < 1 := by
  intro hclaim
  have hstrict := hclaim octahedronDesign isEqualShare_octahedronDesign 0 1 (by decide)
  rw [directionGram_octahedronDesign_zero_one] at hstrict
  norm_num at hstrict

/-- **And the excluded point satisfies U6 anyway.**  The octahedron dominates
through its orthogonal triple `{e_1, e_2, e_3}`, at margin `2`.  So a "pairwise
non-parallel" hypothesis would delete a genuine point of the stratum at which the
U6 conclusion holds, buying nothing; U6 should be stated without it.  (That every
point carrying a parallel pair dominates is not proved here — only that this one
does, together with the structural fact
`Gtz.directionGram_eq_zero_of_sq_directionGram_eq_one` that a parallel pair forces
its atom orthogonal to the whole rest of the design.) -/
theorem dominates_octahedronDesign : Dominates octahedronDesign {0, 2, 4} := by
  have hshape : subsetSum octahedronDesign {0, 2, 4} - 1
      = (2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    have hsqrt : Real.sqrt ((3 : ℕ) : ℝ) ^ 2 = ((3 : ℕ) : ℝ) := Real.sq_sqrt (by norm_num)
    rw [subsetSum, show ({0, 2, 4} : Finset (Fin 6)) = insert 0 (insert 2 {4}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, atomMatrix, Matrix.vecMulVec_apply, octahedronDesign, tightFrameDesign_atom,
      Pi.smul_apply, smul_eq_mul, octahedronFrame, Matrix.of_apply]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.cons_val_four, Matrix.cons_val_fin_one, Matrix.cons_val', Matrix.empty_val'] <;>
      norm_num
  rw [Dominates, hshape]
  exact (Matrix.PosDef.one).posSemidef.smul (by norm_num)

/-- **A parallel pair exhausts its atom's row.**  If two atoms of the stratum have
`gamma^2 = 1` — that is, if their directions are parallel — then the first is
orthogonal to every OTHER atom of the design.  This is the row law's boundary case
transported from `Gtz.IsHollowInvolution.sq_apply_eq_one_iff`, and it is the exact
structural content of the pen's discarded "pairwise non-parallel" hypothesis. -/
theorem directionGram_eq_zero_of_sq_directionGram_eq_one (D : WeightedDesign m k)
    (hequal : IsEqualShare D) (hrank : 0 < k) (hdouble : (m : ℝ) = 2 * (k : ℝ))
    {firstIndex secondIndex : Fin m} (hdistinct : firstIndex ≠ secondIndex)
    (hparallel : directionGram D firstIndex secondIndex ^ 2 = 1) {otherIndex : Fin m}
    (hneFirst : otherIndex ≠ firstIndex) (hneSecond : otherIndex ≠ secondIndex) :
    directionGram D firstIndex otherIndex = 0 := by
  have hinvol := isHollowInvolution_correlationInvolution D hequal hrank hdouble
  have hboundary : correlationInvolution D firstIndex secondIndex ^ 2 = 1 := by
    rw [correlationInvolution_apply_of_ne D hdistinct]; exact hparallel
  have hquiet := (hinvol.sq_apply_eq_one_iff hdistinct).mp hboundary otherIndex hneFirst hneSecond
  rwa [correlationInvolution_apply_of_ne D (Ne.symm hneFirst)] at hquiet

/-! ## The `(6,3)` instances, with every numeric side condition discharged

Everything above is stated at a general size, and the general statements carry
`(k : R)` and `(m : R)` as `Nat.cast` numerals while a consumer writes the real
literals `3` and `1/6`.  This last section closes that gap: it is the interface
the U6 squeeze and the assembly agent should call, and it takes nothing but
`IsEqualShare D` and the distinctness of a triple. -/

/-- Build the stratum predicate from the literal `(6,3)` hypothesis pair the
shipped uniform lemmas already carry (`weight = 1/6`, `leverage = 3`). -/
theorem isEqualShare_six_of_weight_of_leverage (D : WeightedDesign 6 3)
    (hweight : ∀ atomIndex, D.weight atomIndex = 1 / 6)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3) : IsEqualShare D where
  weight_eq := fun atomIndex => by rw [hweight atomIndex]; norm_num
  leverage_eq := fun atomIndex => by rw [hleverage atomIndex]; norm_num

/-- The weight projection in literal form, so that
`Gtz.sum_normalizedPairing_sq_uniform_six` and its siblings take it verbatim. -/
theorem IsEqualShare.weight_eq_six {D : WeightedDesign 6 3} (hequal : IsEqualShare D)
    (atomIndex : Fin 6) : D.weight atomIndex = 1 / 6 := by
  rw [hequal.weight_eq atomIndex]; norm_num

/-- The leverage projection in literal form. -/
theorem IsEqualShare.leverage_eq_three {D : WeightedDesign m 3} (hequal : IsEqualShare D)
    (atomIndex : Fin m) : leverageOf (D.atom atomIndex) = 3 := by
  rw [hequal.leverage_eq atomIndex]; norm_num

/-- The stratum is all-heavy, in the form `Gtz.AllHeavy` wants. -/
theorem IsEqualShare.allHeavy_three {D : WeightedDesign m 3} (hequal : IsEqualShare D) :
    AllHeavy D := hequal.allHeavy (by norm_num)

/-- **THE INVOLUTION LAW at `(6,3)`.** -/
theorem isHollowInvolution_correlationInvolution_six (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) : IsHollowInvolution (correlationInvolution D) :=
  isHollowInvolution_correlationInvolution D hequal (by norm_num) (by norm_num)

/-- **THE ROW LAW at `(6,3)`**: `sum_{d /= c} gamma_cd^2 = 1`. -/
theorem sum_sq_directionGram_erase_six (D : WeightedDesign 6 3) (hequal : IsEqualShare D)
    (atomIndex : Fin 6) :
    ∑ otherIndex ∈ Finset.univ.erase atomIndex, directionGram D atomIndex otherIndex ^ 2 = 1 :=
  sum_sq_directionGram_erase_of_isEqualShare D hequal (by norm_num) (by norm_num) atomIndex

/-- **THE VANISHING SUPPLY CHAIN at `(6,3)`**: `sum_{d /= a,b} gamma_ad gamma_db = 0`. -/
theorem sum_sdiff_directionGram_mul_six (D : WeightedDesign 6 3) (hequal : IsEqualShare D)
    {firstIndex secondIndex : Fin 6} (hdistinct : firstIndex ≠ secondIndex) :
    ∑ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 6)),
        directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex = 0 :=
  sum_sdiff_directionGram_mul_of_isEqualShare D hequal (by norm_num) (by norm_num) hdistinct

/-- **THE NORM CAP at `(6,3)`**, the pen's `(C2)`: `sigma_C + 2 |P_C| <= 1`. -/
theorem directionGram_normCap_triple_six (D : WeightedDesign 6 3) (hequal : IsEqualShare D)
    {firstIndex secondIndex thirdIndex : Fin 6} (hfirstSecond : firstIndex ≠ secondIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) (hsecondThird : secondIndex ≠ thirdIndex) :
    directionGram D firstIndex secondIndex ^ 2 + directionGram D firstIndex thirdIndex ^ 2
        + directionGram D secondIndex thirdIndex ^ 2
      + 2 * |directionGram D firstIndex secondIndex * directionGram D firstIndex thirdIndex
          * directionGram D secondIndex thirdIndex| ≤ 1 :=
  directionGram_normCap_triple D hequal (by norm_num) (by norm_num) hfirstSecond hfirstThird
    hsecondThird

/-- **THE DICTIONARY at `(6,3)`**, hollow-block form. -/
theorem dominates_triple_iff_posSemidef_hollowShift_six (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) {firstIndex secondIndex thirdIndex : Fin 6}
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex) :
    Dominates D {firstIndex, secondIndex, thirdIndex}
      ↔ (hollowMatrixThree (directionGram D firstIndex secondIndex)
          (directionGram D firstIndex thirdIndex) (directionGram D secondIndex thirdIndex)
        + (2 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef :=
  dominates_triple_iff_posSemidef_hollowShift D hequal.leverage_eq_three hfirstSecond hfirstThird
    hsecondThird

/-- **THE DICTIONARY at `(6,3)`**, least-eigenvalue form: `lambda_min(Gamma[C]) >= 1/3`. -/
theorem dominates_triple_iff_inv_three_le_lambdaMinMat_six (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) {firstIndex secondIndex thirdIndex : Fin 6}
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex) :
    Dominates D {firstIndex, secondIndex, thirdIndex}
      ↔ (3 : ℝ)⁻¹ ≤ lambdaMinMat ((directionGramMatrix D).submatrix
          ![firstIndex, secondIndex, thirdIndex] ![firstIndex, secondIndex, thirdIndex]) :=
  dominates_triple_iff_inv_three_le_lambdaMinMat D hequal.leverage_eq_three hfirstSecond
    hfirstThird hsecondThird

/-- **THE DICTIONARY at `(6,3)`**, frame form: `sum_{c in C} u_c u_c^T ⪰ (1/3) 1`, at an
arbitrary subset. -/
theorem dominates_iff_posSemidef_unitFrameSum_six (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) (C : Finset (Fin 6)) :
    Dominates D C ↔ (unitFrameSum D C - (3 : ℝ)⁻¹ • 1).PosSemidef :=
  dominates_iff_posSemidef_unitFrameSum D (by norm_num) hequal.leverage_eq_three C

/-- **The coordinate bridge at `(6,3)`**: `rho = (3/2) gamma`. -/
theorem normalizedPairing_eq_three_halves_mul_directionGram_six (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) (firstIndex secondIndex : Fin 6) :
    normalizedPairing D firstIndex secondIndex
      = (3 / 2 : ℝ) * directionGram D firstIndex secondIndex :=
  normalizedPairing_eq_three_halves_mul_directionGram D hequal.leverage_eq_three firstIndex
    secondIndex

/-! ### Consistency checks against shipped facts

The dictionary is pinned to an object whose domination was proved independently,
so a drift in either definition breaks the build. -/

/-- The shipped `Gtz.icosaDesign_dominates`, read through the least-eigenvalue
dictionary: the icosahedron's coherent triple has `lambda_min(Gamma[C]) >= 1/3`.
Independently, that margin is exactly `1 - 1/sqrt 5`. -/
theorem inv_three_le_lambdaMinMat_icosaDesign :
    (3 : ℝ)⁻¹ ≤ lambdaMinMat ((directionGramMatrix icosaDesign).submatrix
      ![0, 2, 4] ![0, 2, 4]) :=
  (dominates_triple_iff_inv_three_le_lambdaMinMat_six icosaDesign isEqualShare_icosaDesign
    (by decide) (by decide) (by decide)).mp icosaDesign_dominates

/-- The same, read through the hollow-block dictionary. -/
theorem posSemidef_hollowShift_icosaDesign :
    (hollowMatrixThree (directionGram icosaDesign 0 2) (directionGram icosaDesign 0 4)
        (directionGram icosaDesign 2 4)
      + (2 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef :=
  (dominates_triple_iff_posSemidef_hollowShift_six icosaDesign isEqualShare_icosaDesign
    (by decide) (by decide) (by decide)).mp icosaDesign_dominates

/-- The row law, instantiated at the octahedron's antipodal atom: the single
squared correlation `(-1)^2` exhausts the whole unit budget of that row. -/
theorem sum_sq_directionGram_erase_octahedronDesign :
    ∑ otherIndex ∈ Finset.univ.erase (0 : Fin 6),
        directionGram octahedronDesign 0 otherIndex ^ 2 = 1 :=
  sum_sq_directionGram_erase_six octahedronDesign isEqualShare_octahedronDesign 0

end Gtz

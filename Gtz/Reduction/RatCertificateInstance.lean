/-
# An exact rational (6,3) certificate, end to end

The rational consumption layer (`Gtz.Reduction.RatCertificate`) is exercised here on a
concrete `RatDesign 6 3`: every number in the design, in the base set, in the LDL
congruence and in the outsider pivots is a rational literal, and the conclusion is real
Loewner domination.

The design is the split tetrahedron over ℚ — the four regular-tetrahedron directions
with the last two duplicated, weights `(1/4, 1/4, 1/6, 1/12, 1/8, 1/8)`. Its real
avatar is proven an EXACT TIE in `Gtz.Ties.SplitTetrahedronTie`
(`splitTetraDesign_isTie`): it dominates weakly and no 3-subset dominates strictly.

That makes the instance the interesting one rather than a generic one. A certificate
built from strict inequalities could not reach a tie; this certificate does, because
its outsider hypothesis is NON-STRICT and it is met here with EXACT EQUALITY:

  base set `Q = {0, 1, 2, 4}` carries the four distinct tetrahedron directions, so
  `S_Q = 4·I` and the Gram shift is `3·I` — certified by `L = 1`, `d = (3, 3, 3)`;
  each of the two outsiders has pivot EXACTLY `1`, so the weighted outsider excess is
  EXACTLY `0`.

So the tie locus is inside the certificate's reach, not outside it. What the tie
locus does obstruct is any covering argument: `∑ t_e (q_e − 1) ≤ 0` holding with
equality means the hypothesis has zero slack, hence survives no perturbation, so this
certificate covers a ball of radius exactly `0` in the outsider direction — see
`Gtz.LinAlg.CongruenceRobustness`, where the gate half is shown to be robust with an
explicit positive radius and the outsider half is the half that is not.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Reduction.RatCertificate

namespace Gtz

open Matrix

/-! ### Designs are determined by their atoms and weights -/

/-- Two weighted designs with the same atoms and weights are equal — the remaining
fields are propositions. -/
theorem WeightedDesign.ext {m k : ℕ} {first second : WeightedDesign m k}
    (hatom : first.atom = second.atom) (hweight : first.weight = second.weight) :
    first = second := by
  cases first
  cases second
  simp_all

/-! ### The rational split-tetrahedron design -/

/-- The six atoms: the four regular-tetrahedron directions with the last two
duplicated. Every entry is `±1`, so every leverage is `3`. -/
def splitTetraRatAtom : Fin 6 → Fin 3 → ℚ :=
  ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, 1, -1], ![-1, -1, 1], ![-1, -1, 1]]

/-- The weights: each tetrahedron direction receives `1/4` in total, with the two
duplicated directions splitting theirs as `1/6 + 1/12` and `1/8 + 1/8`. -/
def splitTetraRatWeight : Fin 6 → ℚ := ![1/4, 1/4, 1/6, 1/12, 1/8, 1/8]

/-- The exact rational split-tetrahedron `(6,3)` design. Parseval is entrywise
rational arithmetic: each direction's total weight is `1/4` and the four directions
resolve `4·I`. -/
def splitTetraRatDesign : RatDesign 6 3 where
  atom := splitTetraRatAtom
  weight := splitTetraRatWeight
  weight_pos := by intro c; fin_cases c <;> norm_num [splitTetraRatWeight]
  weight_sum_one := by
    simp only [Fin.sum_univ_six, splitTetraRatWeight, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    intro i j
    simp only [Fin.sum_univ_six, splitTetraRatWeight, splitTetraRatAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    fin_cases i <;> fin_cases j <;> norm_num

/-- The base set: the four atoms carrying the four DISTINCT tetrahedron directions. -/
def splitTetraRatBase : Finset (Fin 6) := {0, 1, 2, 4}

theorem splitTetraRatBase_card : splitTetraRatBase.card = 3 + 1 := by decide

/-! ### The certificate data, computed exactly -/

/-- **The base Gram shift is `3·I`.** The four distinct tetrahedron directions resolve
`∑_d v_d v_dᵀ = 4·I`, so `S_Q − 1 = 3·I`. -/
theorem splitTetraRat_gram :
    ratGram splitTetraRatDesign splitTetraRatBase
      = (3 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
  ext i j
  rw [ratGram, Matrix.of_apply, splitTetraRatBase,
    show ({0, 1, 2, 4} : Finset (Fin 6)) = insert 0 (insert 1 (insert 2 {4})) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [splitTetraRatDesign, splitTetraRatAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_four,
    Matrix.tail_cons, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num

/-- The inverse of the base Gram shift, exactly: `(3·I)⁻¹ = (1/3)·I`. -/
theorem splitTetraRat_gramInv :
    (ratGram splitTetraRatDesign splitTetraRatBase)⁻¹
      = (1/3 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
  apply Matrix.inv_eq_right_inv
  rw [splitTetraRat_gram, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  norm_num

/-- **The LDL congruence certificate**: `L = 1` and `d = (3, 3, 3)` witness the gate. -/
theorem splitTetraRat_congruence :
    (1 : Matrix (Fin 3) (Fin 3) ℚ)ᵀ * ratGram splitTetraRatDesign splitTetraRatBase * 1
      = Matrix.diagonal ![3, 3, 3] := by
  rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, splitTetraRat_gram]
  ext i j
  simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num

/-- The complement of the base set is exactly the two duplicate atoms. -/
theorem splitTetraRatBase_compl : splitTetraRatBaseᶜ = {3, 5} := by decide

/-- **Every outsider pivot is EXACTLY `1`.** The outsiders are the duplicated
tetrahedron directions, each of leverage `3`, and the resolvent is `(1/3)·I`. The
certificate's outsider hypothesis is therefore met with equality, not with slack. -/
theorem splitTetraRat_pivot_eq_one (e : Fin 6) (he : e ∈ splitTetraRatBaseᶜ) :
    splitTetraRatDesign.atom e ⬝ᵥ
        ((ratGram splitTetraRatDesign splitTetraRatBase)⁻¹ *ᵥ splitTetraRatDesign.atom e)
      = 1 := by
  have hduplicate : e = 3 ∨ e = 5 := by
    rw [splitTetraRatBase_compl] at he
    fin_cases e <;> revert he <;> decide
  rw [splitTetraRat_gramInv]
  rcases hduplicate with rfl | rfl <;>
    simp [splitTetraRatDesign, splitTetraRatAtom, dotProduct, Matrix.mulVec,
      Fin.sum_univ_three, Matrix.one_apply] <;> norm_num

/-- **The weighted outsider excess is EXACTLY zero** — the pigeonhole hypothesis at
its own boundary. -/
theorem splitTetraRat_excess_eq_zero :
    ∑ e ∈ splitTetraRatBaseᶜ, splitTetraRatDesign.weight e *
      (splitTetraRatDesign.atom e ⬝ᵥ
        ((ratGram splitTetraRatDesign splitTetraRatBase)⁻¹ *ᵥ splitTetraRatDesign.atom e)
        - 1) = 0 := by
  refine Finset.sum_eq_zero fun e he => ?_
  rw [splitTetraRat_pivot_eq_one e he]
  ring

/-! ### The certificate consumed -/

/-- **The end-to-end exact instance.** A rational `(6,3)` design, an exact rational LDL
congruence certificate, exact rational outsider pivots — and real Loewner domination
out the other end, entirely through the shipped consumer
`ratCertificate_dominates_of_excess`.

The design's real avatar is an exact tie (`Gtz.splitTetraDesign_isTie`), so this is a
certificate FIRING ON THE TIE LOCUS: a rational certificate is not obstructed by the
tie variety. What the tie locus removes is the certificate's SLACK, and with it any
neighbourhood of validity. -/
theorem splitTetraRatDesign_certified_dominates :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates splitTetraRatDesign.toReal C :=
  ratCertificate_dominates_of_excess splitTetraRatDesign (by norm_num)
    splitTetraRatBase splitTetraRatBase_card 1 ![3, 3, 3]
    (by simp) (by intro i; fin_cases i <;> norm_num)
    splitTetraRat_congruence
    (le_of_eq splitTetraRat_excess_eq_zero)

/-- The same instance through the POINTWISE consumer, since every pivot here is exactly
`1`: both readings of branch (a) fire at this tie. -/
theorem splitTetraRatDesign_certified_dominates_pointwise :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates splitTetraRatDesign.toReal C :=
  ratCertificate_dominates splitTetraRatDesign (by norm_num)
    splitTetraRatBase splitTetraRatBase_card 1 ![3, 3, 3]
    (by simp) (by intro i; fin_cases i <;> norm_num)
    splitTetraRat_congruence
    (fun e he => le_of_eq (splitTetraRat_pivot_eq_one e he))

end Gtz

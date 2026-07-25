import Gtz.Reduction.RatCertificate
import Gtz.Reduction.BranchTwoRational

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# AUDITOR B counter-brick

The builder's file offers, as the rational branch-(b) consumer, a certificate whose
diagonal must be negative at EXACTLY ONE index, and then discovers that the rank-3
specialization of it is INCOMPLETE (`exists_dominatingTriple_withoutStrictGate`),
and names deciding that incompleteness "the single most valuable next brick".

This probe shows the incompleteness is an artifact of the certificate class, not of
GTZ: relaxing "one negative pivot" to "NONNEGATIVE diagonal" gives a consumer that
(i) is shorter, (ii) works at every rank, (iii) needs no cap criterion, no
determinant sign, no signature witness, no `Cramer` expansion, and (iv) fires at
exactly the witness where the builder's rank-3 producer is silent.

`Gtz.posSemidef_congr_right` (PsdKit.lean:129) already existed in the repo.
-/

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- **The complete real consumer.** A congruence of the subset's Gram shift to a
NONNEGATIVE diagonal certifies domination — at every rank, with no side condition
and no determinant sign. Compare `dominates_of_capCongruence`, which asks for
exactly one negative pivot plus a determinant sign on an enlarged set. -/
theorem dominates_of_psdCongruence (D : WeightedDesign m k) (subset : Finset (Fin m))
    (basis : Matrix (Fin k) (Fin k) ℝ) (diagVec : Fin k → ℝ)
    (hbasisDet : IsUnit basis.det)
    (hCongr : basisᵀ * (subsetSum D subset - 1) * basis = Matrix.diagonal diagVec)
    (hNonnegPivots : ∀ i, 0 ≤ diagVec i) :
    Dominates D subset := by
  have hsym : (subsetSum D subset - 1)ᵀ = subsetSum D subset - 1 := by
    rw [Matrix.transpose_sub, subsetSum_transpose, Matrix.transpose_one]
  rw [Dominates, posSemidef_congr_right hsym hbasisDet, hCongr]
  exact Matrix.posSemidef_diagonal_iff.mpr hNonnegPivots

/-- **The complete rational consumer.** Every hypothesis is a finite ℚ-identity or
ℚ-comparison; the conclusion is real Loewner domination. Unlike
`ratDominates_of_capCongruence` this needs no fresh atom, no enlarged
determinant, and no sign discipline on the diagonal beyond nonnegativity. -/
theorem ratDominates_of_psdCongruence (R : RatDesign m k) (subset : Finset (Fin m))
    (basisRat : Matrix (Fin k) (Fin k) ℚ) (diagRat : Fin k → ℚ)
    (hbasisDet : basisRat.det ≠ 0)
    (hCongr : basisRatᵀ * ratGram R subset * basisRat = Matrix.diagonal diagRat)
    (hNonnegPivots : ∀ i, 0 ≤ diagRat i) :
    Dominates R.toReal subset := by
  refine dominates_of_psdCongruence R.toReal subset
    (basisRat.map (fun q : ℚ => (q : ℝ))) (fun i => (diagRat i : ℝ)) ?_ ?_ ?_
  · rw [det_cast]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hbasisDet)
  · rw [R.gram_cast subset, ← Matrix.transpose_map, ← map_mul_cast, ← map_mul_cast,
      hCongr]
    ext i j
    rcases eq_or_ne i j with rfl | hoffDiagonal
    · simp [Matrix.map_apply]
    · simp [Matrix.map_apply, hoffDiagonal]
  · intro i
    exact_mod_cast hNonnegPivots i

/-- The frontier shape: a `k`-subset with a nonnegative-diagonal congruence is a
witness for `GtzWeighted m k`. -/
theorem ratPsdCertificate_exists_dominating (R : RatDesign m k)
    (subset : Finset (Fin m)) (hcard : subset.card = k)
    (basisRat : Matrix (Fin k) (Fin k) ℚ) (diagRat : Fin k → ℚ)
    (hbasisDet : basisRat.det ≠ 0)
    (hCongr : basisRatᵀ * ratGram R subset * basisRat = Matrix.diagonal diagRat)
    (hNonnegPivots : ∀ i, 0 ≤ diagRat i) :
    ∃ C : Finset (Fin m), C.card = k ∧ Dominates R.toReal C :=
  ⟨subset, hcard,
    ratDominates_of_psdCongruence R subset basisRat diagRat hbasisDet hCongr
      hNonnegPivots⟩

/-! ### The builder's own counterexample, certified -/

/-- The congruence basis that diagonalizes the all-ones Gram shift. -/
def degenerateWitnessBasis : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 1, 1; 0, -1, 0; 0, 0, -1]

/-- The Gram shift of `exists_dominatingTriple_withoutStrictGate`'s triple is
the all-ones matrix. -/
theorem degenerateWitness_gramShift :
    (atomMatrix ![1, 1, 0] + atomMatrix ![1, 0, 1] + atomMatrix ![0, 1, 1]
      - 1 : Matrix (Fin 3) (Fin 3) ℝ) = atomMatrix ![1, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [atomMatrix, Matrix.vecMulVec_apply]

/-- **The congruence, exactly**: nonnegative diagonal `(1, 0, 0)`, unit determinant. -/
theorem degenerateWitness_congruence :
    degenerateWitnessBasisᵀ
        * (atomMatrix ![1, 1, 0] + atomMatrix ![1, 0, 1] + atomMatrix ![0, 1, 1]
            - 1 : Matrix (Fin 3) (Fin 3) ℝ)
        * degenerateWitnessBasis
      = Matrix.diagonal ![1, 0, 0] := by
  rw [degenerateWitness_gramShift]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [degenerateWitnessBasis, atomMatrix, Matrix.vecMulVec_apply,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]

theorem degenerateWitnessBasis_det : degenerateWitnessBasis.det = 1 := by
  simp [degenerateWitnessBasis, Matrix.det_fin_three]

/-- **The named gap is not a gap for this consumer.** At the exact triple where
`exists_dominatingTriple_withoutStrictGate` shows every pair gate degenerates —
so `dominates_of_pairGate` and `cap_fires_iff_det_nonneg` are both silent —
the nonnegative-diagonal congruence certifies domination outright, by one rational
matrix identity. -/
theorem degenerateWitness_isPosSemidef_byCongruence :
    (atomMatrix ![1, 1, 0] + atomMatrix ![1, 0, 1] + atomMatrix ![0, 1, 1]
      - 1 : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hsym : (atomMatrix ![1, 1, 0] + atomMatrix ![1, 0, 1] + atomMatrix ![0, 1, 1]
      - 1 : Matrix (Fin 3) (Fin 3) ℝ)ᵀ
      = atomMatrix ![1, 1, 0] + atomMatrix ![1, 0, 1] + atomMatrix ![0, 1, 1] - 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [atomMatrix, Matrix.vecMulVec_apply, Matrix.transpose_apply]
  rw [posSemidef_congr_right hsym
    (isUnit_iff_ne_zero.mpr (by rw [degenerateWitnessBasis_det]; norm_num)),
    degenerateWitness_congruence]
  exact Matrix.posSemidef_diagonal_iff.mpr (by
    intro i; fin_cases i <;> norm_num)

/-! ### The same tie the builder certified, with the weaker certificate -/

/-- The split-tetrahedron dominating triple `{0,1,2}` certified by a NONNEGATIVE
diagonal congruence — no gate, no fresh atom, no negative pivot, no cap
determinant. Diagonal `(2, 3/2, 0)`. -/
theorem splitTetraTriple_psdCongruence :
    (!![1, 1/2, -1; 0, 1, -1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℚ)ᵀ
        * ratGram splitTetraRatDesign (insert 2 ({0, 1} : Finset (Fin 6)))
        * !![1, 1/2, -1; 0, 1, -1; 0, 0, 1]
      = Matrix.diagonal ![2, 3/2, 0] := by
  have hgram : ratGram splitTetraRatDesign (insert 2 ({0, 1} : Finset (Fin 6)))
      = !![2, -1, 1; -1, 2, 1; 1, 1, 2] := by
    ext i j
    rw [ratGram, Matrix.of_apply,
      show insert 2 ({0, 1} : Finset (Fin 6)) = insert 2 (insert 0 {1}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    simp only [splitTetraRatDesign, splitTetraRatAtom, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    fin_cases i <;> fin_cases j <;> norm_num
  have htranspose : (!![1, 1/2, -1; 0, 1, -1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℚ)ᵀ
      = !![1, 0, 0; 1/2, 1, 0; -1, -1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  rw [hgram, htranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal,
      Matrix.cons_val_two, Matrix.tail_cons]

theorem splitTetraTriple_dominates_byPsdCongruence :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates splitTetraRatDesign.toReal C :=
  ratPsdCertificate_exists_dominating splitTetraRatDesign
    (insert 2 ({0, 1} : Finset (Fin 6))) (by decide)
    !![1, 1/2, -1; 0, 1, -1; 0, 0, 1] ![2, 3/2, 0]
    (by norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.tail_cons])
    splitTetraTriple_psdCongruence
    (by
      intro i
      fin_cases i
      · norm_num
      · norm_num
      · norm_num [Matrix.cons_val_two, Matrix.tail_cons])

/-! ### Non-vacuity of `branchTests_agree`'s double side condition -/

/-- Both of `branchTests_agree`'s side conditions hold simultaneously on the
split tetrahedron at `core = {0,1,2}`, `insider = 4`, `extra = 0`: the upper base
`{0,1,2,4}` has Gram shift `3·I ≻ 0`, and the lower gate `{1,2}` has determinant
`-3 < 0`. So that theorem is not vacuous — but note it speaks ONLY inside the
intersection of the two branches' domains. -/
theorem branchTests_agree_isNonvacuous :
    (subsetSum splitTetraRatDesign.toReal ({0, 1, 2, 4} : Finset (Fin 6)) - 1).PosDef
      ∧ (subsetSum splitTetraRatDesign.toReal ({1, 2} : Finset (Fin 6)) - 1).det < 0 := by
  constructor
  · have hshift : subsetSum splitTetraRatDesign.toReal ({0, 1, 2, 4} : Finset (Fin 6)) - 1
        = Matrix.diagonal ![(3 : ℝ), 3, 3] := by
      rw [splitTetraRatDesign.gram_cast,
        show ({0, 1, 2, 4} : Finset (Fin 6)) = splitTetraRatBase from rfl,
        splitTetraRat_gram]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
          Matrix.diagonal, Matrix.cons_val_two, Matrix.tail_cons]
    rw [hshift]
    exact Matrix.PosDef.diagonal (by
      intro i
      fin_cases i
      · norm_num
      · norm_num
      · norm_num [Matrix.cons_val_two, Matrix.tail_cons])
  · have hshift : subsetSum splitTetraRatDesign.toReal ({1, 2} : Finset (Fin 6)) - 1
        = pairGramShift (splitTetraRatDesign.toReal.atom 1)
            (splitTetraRatDesign.toReal.atom 2) := by
      rw [subsetSum, Finset.sum_pair (by decide), pairGramShift]
    rw [hshift, pairGramShift_det]
    norm_num [splitTetraRatDesign, splitTetraRatAtom, RatDesign.toReal, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

end Gtz

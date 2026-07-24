/-
# The local balance at the split-tetrahedron ties

At every split-tetrahedron tie the twelve distinct-direction 3-subsets are the active
family: each dominates weakly (`balanceSubset_dominates`) and its gap vanishes at the
direction it misses (`balanceSubset_tight`), so each has smallest subset eigenvalue
exactly `1`. The first-order object the whole family carries is the LOCAL balance over
this active family: nonnegative multipliers `balanceCoefficient` with, for every
atom `c`,

  `∑_{i with c ∈ C_i} θ_i · ⟨g_c, w_i⟩² = t_c`,

`w_i` the missed direction of `C_i` (`splitTetraDesign_localBalance`). Only subsets
CONTAINING the atom contribute. The matrix pairing `⟨Λ, g_c g_cᵀ⟩ = t_c`, which sums
the same data over the WHOLE family, agrees with the local balance only under full
symmetry and fails at asymmetric splits (`splitTetraDesign_noStressCertificate`); the
local form is the invariant that survives on the whole flat. The explicit solution:
`θ = (chosen copy weight)/3` on the subsets missing a duplicated direction, and
`θ = (4/3)·(product of the two chosen copy weights)` on those missing an unsplit one.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Ties.SplitTetrahedronTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ### The active family: the twelve distinct-direction triples -/

/-- The twelve 3-subsets carrying three distinct tetrahedron directions, ordered by the
direction they miss (`3, 3, 2, 2, 1, 1, 1, 1, 0, 0, 0, 0`). -/
def balanceSubset : Fin 12 → Finset (Fin 6) :=
  ![{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 1, 5},
    {0, 2, 4}, {0, 2, 5}, {0, 3, 4}, {0, 3, 5},
    {1, 2, 4}, {1, 2, 5}, {1, 3, 4}, {1, 3, 5}]

/-- The tetrahedron direction each active subset misses — its tight direction. -/
def balanceMissingDir : Fin 12 → Fin 4 := ![3, 3, 2, 2, 1, 1, 1, 1, 0, 0, 0, 0]

variable (splitA splitB : ℝ)

/-- The local-balance multipliers: `(chosen copy weight)/3` where one duplicated
direction is present, `(4/3)·(product of both chosen copy weights)` where both are. -/
noncomputable def balanceCoefficient : Fin 12 → ℝ :=
  ![splitA / 3, (1/4 - splitA) / 3, splitB / 3, (1/4 - splitB) / 3,
    4/3 * (splitA * splitB), 4/3 * (splitA * (1/4 - splitB)),
    4/3 * ((1/4 - splitA) * splitB), 4/3 * ((1/4 - splitA) * (1/4 - splitB)),
    4/3 * (splitA * splitB), 4/3 * (splitA * (1/4 - splitB)),
    4/3 * ((1/4 - splitA) * splitB), 4/3 * ((1/4 - splitA) * (1/4 - splitB))]

variable (hAPos : 0 < splitA) (hALt : splitA < 1/4) (hBPos : 0 < splitB)
  (hBLt : splitB < 1/4)

include hAPos hALt hBPos hBLt in
/-- The multipliers are nonnegative on the whole family. -/
theorem balanceCoefficient_nonneg (i : Fin 12) :
    0 ≤ balanceCoefficient splitA splitB i := by
  fin_cases i
  · exact (by linarith : (0 : ℝ) ≤ splitA / 3)
  · exact (by linarith : (0 : ℝ) ≤ (1/4 - splitA) / 3)
  · exact (by linarith : (0 : ℝ) ≤ splitB / 3)
  · exact (by linarith : (0 : ℝ) ≤ (1/4 - splitB) / 3)
  · exact (by nlinarith : (0 : ℝ) ≤ 4/3 * (splitA * splitB))
  · exact (by nlinarith : (0 : ℝ) ≤ 4/3 * (splitA * (1/4 - splitB)))
  · exact (by nlinarith : (0 : ℝ) ≤ 4/3 * ((1/4 - splitA) * splitB))
  · exact (by nlinarith : (0 : ℝ) ≤ 4/3 * ((1/4 - splitA) * (1/4 - splitB)))
  · exact (by nlinarith : (0 : ℝ) ≤ 4/3 * (splitA * splitB))
  · exact (by nlinarith : (0 : ℝ) ≤ 4/3 * (splitA * (1/4 - splitB)))
  · exact (by nlinarith : (0 : ℝ) ≤ 4/3 * ((1/4 - splitA) * splitB))
  · exact (by nlinarith : (0 : ℝ) ≤ 4/3 * ((1/4 - splitA) * (1/4 - splitB)))

/-! ### Each active subset dominates: one sum of squares per missed direction -/

private theorem gapForm_nonneg_dirs_012 (x : Fin 3 → ℝ) :
    0 ≤ (tetraAtom 0 ⬝ᵥ x) ^ 2 + ((tetraAtom 1 ⬝ᵥ x) ^ 2 + (tetraAtom 2 ⬝ᵥ x) ^ 2)
      - x ⬝ᵥ x := by
  simp only [tetraAtom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, dotProduct, Fin.sum_univ_three]
  nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 + x 2), sq_nonneg (x 1 + x 2)]

private theorem gapForm_nonneg_dirs_013 (x : Fin 3 → ℝ) :
    0 ≤ (tetraAtom 0 ⬝ᵥ x) ^ 2 + ((tetraAtom 1 ⬝ᵥ x) ^ 2 + (tetraAtom 3 ⬝ᵥ x) ^ 2)
      - x ⬝ᵥ x := by
  simp only [tetraAtom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, dotProduct,
    Fin.sum_univ_three]
  nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1 + x 2)]

private theorem gapForm_nonneg_dirs_023 (x : Fin 3 → ℝ) :
    0 ≤ (tetraAtom 0 ⬝ᵥ x) ^ 2 + ((tetraAtom 2 ⬝ᵥ x) ^ 2 + (tetraAtom 3 ⬝ᵥ x) ^ 2)
      - x ⬝ᵥ x := by
  simp only [tetraAtom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, dotProduct,
    Fin.sum_univ_three]
  nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 + x 2), sq_nonneg (x 1 - x 2)]

private theorem gapForm_nonneg_dirs_123 (x : Fin 3 → ℝ) :
    0 ≤ (tetraAtom 1 ⬝ᵥ x) ^ 2 + ((tetraAtom 2 ⬝ᵥ x) ^ 2 + (tetraAtom 3 ⬝ᵥ x) ^ 2)
      - x ⬝ᵥ x := by
  simp only [tetraAtom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, dotProduct,
    Fin.sum_univ_three]
  nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2)]

private theorem dominates_insert_triple (aOne aTwo aThree : Fin 6)
    (hOne : aOne ∉ ({aTwo, aThree} : Finset (Fin 6)))
    (hTwo : aTwo ∉ ({aThree} : Finset (Fin 6)))
    (hform : ∀ x : Fin 3 → ℝ,
      0 ≤ (splitTetraAtom aOne ⬝ᵥ x) ^ 2 + ((splitTetraAtom aTwo ⬝ᵥ x) ^ 2 +
        (splitTetraAtom aThree ⬝ᵥ x) ^ 2) - x ⬝ᵥ x) :
    Dominates (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt)
      {aOne, aTwo, aThree} := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
  · exact ((Matrix.posSemidef_sum ({aOne, aTwo, aThree} : Finset (Fin 6)) fun c _ =>
      posSemidef_atomMatrix
        ((splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).atom c)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, dominationGap_form, Finset.sum_insert hOne,
      Finset.sum_insert hTwo, Finset.sum_singleton]
    simpa only [splitTetraDesign_atom] using hform x

/-- **Each active subset dominates weakly** — its gap is the sum of three squares
determined by the pair pattern of the three directions it carries. -/
theorem balanceSubset_dominates (i : Fin 12) :
    Dominates (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt)
      (balanceSubset i) := by
  fin_cases i
  · exact dominates_insert_triple splitA splitB hAPos hALt hBPos hBLt 0 1 2
      (by decide) (by decide) gapForm_nonneg_dirs_012
  · exact dominates_insert_triple splitA splitB hAPos hALt hBPos hBLt 0 1 3
      (by decide) (by decide) gapForm_nonneg_dirs_012
  · exact dominates_insert_triple splitA splitB hAPos hALt hBPos hBLt 0 1 4
      (by decide) (by decide) gapForm_nonneg_dirs_013
  · exact dominates_insert_triple splitA splitB hAPos hALt hBPos hBLt 0 1 5
      (by decide) (by decide) gapForm_nonneg_dirs_013
  · exact dominates_insert_triple splitA splitB hAPos hALt hBPos hBLt 0 2 4
      (by decide) (by decide) gapForm_nonneg_dirs_023
  · exact dominates_insert_triple splitA splitB hAPos hALt hBPos hBLt 0 2 5
      (by decide) (by decide) gapForm_nonneg_dirs_023
  · exact dominates_insert_triple splitA splitB hAPos hALt hBPos hBLt 0 3 4
      (by decide) (by decide) gapForm_nonneg_dirs_023
  · exact dominates_insert_triple splitA splitB hAPos hALt hBPos hBLt 0 3 5
      (by decide) (by decide) gapForm_nonneg_dirs_023
  · exact dominates_insert_triple splitA splitB hAPos hALt hBPos hBLt 1 2 4
      (by decide) (by decide) gapForm_nonneg_dirs_123
  · exact dominates_insert_triple splitA splitB hAPos hALt hBPos hBLt 1 2 5
      (by decide) (by decide) gapForm_nonneg_dirs_123
  · exact dominates_insert_triple splitA splitB hAPos hALt hBPos hBLt 1 3 4
      (by decide) (by decide) gapForm_nonneg_dirs_123
  · exact dominates_insert_triple splitA splitB hAPos hALt hBPos hBLt 1 3 5
      (by decide) (by decide) gapForm_nonneg_dirs_123

/-- **Each active subset is tight at its missed direction**: the gap form vanishes
there, so with `balanceSubset_dominates` its smallest subset eigenvalue is exactly
`1` — the subset is active at the tie. -/
theorem balanceSubset_tight (i : Fin 12) :
    tetraAtom (balanceMissingDir i) ⬝ᵥ
      ((subsetSum (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt)
          (balanceSubset i) - 1) *ᵥ tetraAtom (balanceMissingDir i)) = 0 := by
  fin_cases i <;>
    exact splitTetra_gapForm_zero_of_unusedDir splitA splitB hAPos hALt hBPos hBLt
      (by decide) (by decide)

set_option maxHeartbeats 1600000 in
/-- **The local balance**: the nonnegative multipliers on the active subsets' tight
directions reproduce every atom's weight ATOM-LOCALLY — only subsets containing the
atom contribute:

  `∑_{i with c ∈ C_i} θ_i · ⟨g_c, w_i⟩² = t_c`. -/
theorem splitTetraDesign_localBalance (c : Fin 6) :
    ∑ i : Fin 12,
      (if c ∈ balanceSubset i then
        balanceCoefficient splitA splitB i *
          ((splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).atom c ⬝ᵥ
            tetraAtom (balanceMissingDir i)) ^ 2
      else 0)
      = (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).weight c := by
  fin_cases c <;>
  · simp [Fin.sum_univ_succ, balanceSubset, balanceMissingDir, balanceCoefficient,
      splitTetraAtom, splitTetraDirIndex, tetraAtom, dotProduct, Finset.mem_insert,
      Finset.mem_singleton, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    ring

end Gtz
